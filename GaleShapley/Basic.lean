import Mathlib.Algebra.Order.BigOperators.Group.Finset
import GaleShapley.Matching
import GaleShapley.Iterate

/-!

# Gale-Shapley algorithm

This file defines the Gale-Shapley algorithm and proves that it always produces a
stable matching.

-/
namespace GaleShapley

open Classical BigOperators GaleShapley.Iterate
noncomputable section

variable {M W: Type} [Fintype M] [Fintype W]

abbrev Pref (M W: Type) [Fintype M] [Fintype W] := M → Fin (Fintype.card W) ≃ W

-- tracks the algorithm state and invariants
structure GaleShapleyState (M W: Type) [Fintype M] [Fintype W] where
  mPref: Pref M W
  wPref: Pref W M
  matching: Matching M W
  proposeIndex: M → Nat  -- the index of the next proposal. |W| means no more proposals.
  bound: ∀ m, proposeIndex m ≤ Fintype.card W
  matchedLastProposed:
    ∀ m, ∀ w, matching m = some w → (mPref m).symm w + 1 = proposeIndex m
  noWorseThanProposedTo:
    ∀ m, ∀ w, (mPref m).symm w < proposeIndex m →     -- m proposed to w
      ∃ m', (inverseMatching matching w) = some m' ∧  -- m' is paired with w
        (wPref w).symm m' <= (wPref w).symm m         -- w prefers m' to m

-- at least one proposer is unmatched and has at least one proposal left to make
def notDone (state: GaleShapleyState M W) := ∃ m, state.matching m = none ∧ state.proposeIndex m < Fintype.card W

-- these simp lemmas state an obvious bound on the proposeIndex
@[simp]
lemma proposeMaxIndex (state: GaleShapleyState M W):
    ¬ (state.proposeIndex m < Fintype.card W) ↔ state.proposeIndex m = Fintype.card W := by
  have := state.bound m
  constructor <;> omega

@[simp]
lemma proposeMaxIndex' (state: GaleShapleyState M W):
    Fintype.card W ≤ state.proposeIndex m ↔ state.proposeIndex m = Fintype.card W := by
  have := state.bound m
  constructor <;> omega

/- the cast of characters for each step of the algorithm -/

-- who is being proposed to at this sate
def proposee {state: GaleShapleyState M W} (h: notDone state): W :=
    state.mPref (choose h) ⟨state.proposeIndex (choose h), (choose_spec h).2⟩

-- says that m proposed to w at this state
def proposedAtState {state: GaleShapleyState M W} (h: notDone state) (m: M) (w: W): Prop :=
    m = choose h ∧ proposee h = w

-- the current match of the proposee at this state, if any
def curMatch {state: GaleShapleyState M W} (h: notDone state): Option M :=
    inverseMatching state.matching (proposee h)

-- the match of the proposee after the proposal is either accepted or rejected
def newMatch {state: GaleShapleyState M W} (h: notDone state): M :=
    match curMatch h with
    | none => choose h
    | some m => if (state.wPref (proposee h)).symm (choose h) ≤
        (state.wPref (proposee h)).symm m then choose h else m

-- who is rejected by the proposee at this state, if any
def rejectee {state: GaleShapleyState M W} (h: notDone state): Option M :=
    if curMatch h = none then none
    else if curMatch h = some (newMatch h) then some (choose h) else curMatch h

-- says that m was rejected by w at this state
def rejectedAtState {state: GaleShapleyState M W} (h: notDone state) (m: M) (w: W) :=
    proposee h = w ∧ rejectee h = some m

/- This is a key definition. It implements one iteration of the algorithm and proves that
   the invariants are preserved.
 -/
def galeShapleyNextStep (state: GaleShapleyState M W): Option (GaleShapleyState M W) :=
  if h0: notDone state then
    let hm0' := Classical.choose_spec h0
    let m0 := choose h0
    have m0_proposer: m0 = choose h0 := by rfl
    have hm0: state.matching m0 = none ∧ state.proposeIndex m0 < Fintype.card W := by
      rw [m0_proposer]
      exact hm0'
    let w0 := proposee h0
    have w0_proposee: w0 = proposee h0 := by rfl
    let w0_curMatch := curMatch h0
    let w0_newMatch := newMatch h0
    let newMatching': M → Option W := fun m =>
      if m ≠ m0 ∧ w0_curMatch ≠ some m then state.matching m
      else if m = w0_newMatch then some w0
      else none
    let invNewMatching' : W → Option M := fun w =>
      if w ≠ w0 then inverseMatching state.matching w else some w0_newMatch
    let newMatching := createMatching newMatching' invNewMatching' (by
      intros m w
      simp [newMatching', invNewMatching']
      split_ifs <;> ((try simp); (try tauto))
      · case _ h1 h2 =>
        rw [h2]
        intro m_matches_w0
        have: w0_curMatch = m := by
          have := (inverseProperty state.matching m w0).mp m_matches_w0
          simp [w0_curMatch, curMatch, this]
        exact False.elim (h1.2 this)
      · exact (inverseProperty state.matching m w).mp
    )
    let newProposeIndex := fun m =>
      if m ≠ m0 then state.proposeIndex m else state.proposeIndex m + 1
    have newBound: ∀ m, newProposeIndex m ≤ Fintype.card W := by
      intro m
      simp [newProposeIndex]
      split_ifs with m_eq_m0
      · rw [m_eq_m0]
        omega
      · exact state.bound m
    have newMatchedLastProposed:
        ∀ m, ∀ w, newMatching m = some w → (state.mPref m).symm w + 1 = newProposeIndex m := by
      intros m w
      by_cases h1: m ≠ m0 ∧ w0_curMatch ≠ some m
      · simp [newMatching, newProposeIndex, h1, createMatching, newMatching']
        exact state.matchedLastProposed m w
      · by_cases h1': m = m0
        · simp [newMatching, newProposeIndex, h1', createMatching, newMatching']
          intros _ c2
          rw [← c2]
          simp [w0, proposee]
        · have h1'': w0_curMatch = m := by tauto
          simp [newMatching, newProposeIndex, h1', ← h1'', createMatching, newMatching']
          simp [w0_curMatch, curMatch, ← w0_proposee] at h1''
          intros _ w_eq_w0
          rw [← w_eq_w0]
          rw [← inverseProperty state.matching m w0] at h1''
          exact state.matchedLastProposed m w0 h1''
    have newMatch_options: w0_newMatch = m0 ∨ w0_newMatch = w0_curMatch := by
      simp only [w0_newMatch, newMatch]
      split <;> tauto
      split_ifs <;> tauto
    have newNoWorseThanProposedTo:
        ∀ m, ∀ w, (state.mPref m).symm w < newProposeIndex m →     -- m proposed to w
          ∃ m', (inverseMatching newMatching w) = some m' ∧  -- m' is paired with w
            (state.wPref w).symm m' <= (state.wPref w).symm m := by
      intros m w
      by_cases h1: m = m0 ∧ w = w0
      · simp [newProposeIndex, newMatching, h1, createMatching, newMatching']
        intro
        use w0_newMatch
        rw [← inverseProperty _ w0_newMatch w0]
        simp
        rcases newMatch_options with cond | cond <;> simp [cond]
        simp [w0_newMatch, newMatch, m0, w0]
        split <;> rw [← m0_proposer]; split <;> omega
      · intro lt_newProposeIndex
        have prev: (state.mPref m).symm w < state.proposeIndex m := by
          by_cases h2: m ≠ m0
          · simp [h2, newProposeIndex] at lt_newProposeIndex
            exact lt_newProposeIndex
          · push_neg at h2
            simp [h2, newProposeIndex] at lt_newProposeIndex ⊢
            by_contra bad
            have eq: (state.mPref m0).symm w = ⟨state.proposeIndex m0, hm0.2⟩ := by
              apply_fun (fun x => x.val)
              simp
              omega
              exact Fin.val_injective
            have w0_eq: w0 = (state.mPref m0) ⟨state.proposeIndex m0, hm0.2⟩ := by rfl
            rw [← eq] at w0_eq
            simp at w0_eq
            tauto
        have := state.noWorseThanProposedTo m w prev
        by_cases h2: w ≠ w0
        · obtain ⟨m', w_matches_m', w_prefers_m'⟩ := this
          use m'
          constructor
          · rw [← inverseProperty state.matching m' w] at w_matches_m'
            rw [← inverseProperty newMatching m' w]
            have c1: m' ≠ m0 := by
              by_contra bad
              rw [bad, hm0.1] at w_matches_m'
              contradiction
            have c2: w0_curMatch ≠ some m' := by
              by_contra bad
              simp [w0_curMatch, curMatch] at bad
              rcases h3: ((inverseMatching state.matching) w0) with _ | m''
              · simp [w0_curMatch, curMatch, h3] at bad
              · simp [w0_curMatch, curMatch, h3] at bad
                have := (inverseProperty state.matching m'' w0).mpr h3
                rw [bad, w_matches_m'] at this
                simp at this
                contradiction
            simp [c1, c2, newMatching, createMatching, newMatching']
            exact w_matches_m'
          · exact w_prefers_m'
        · push_neg at h2
          rw [h2] at lt_newProposeIndex prev this ⊢
          simp [h2] at h1
          use w0_newMatch
          constructor
          · rw [← inverseProperty newMatching w0_newMatch w0]
            push_neg at h1
            simp [h1, newMatching, createMatching, newMatching']
            rcases newMatch_options <;> tauto
          · obtain ⟨m'', w0_matches_m'', w0_prefers_m''⟩ := this
            have: m'' = w0_curMatch := by
              simp [w0_curMatch, curMatch, w0_matches_m'']
            simp [w0_curMatch] at this
            suffices (state.wPref w0).symm w0_newMatch ≤ (state.wPref w0).symm m'' by omega
            simp [w0_newMatch, newMatch, ← m0_proposer, ← w0_proposee, ← this]
            split_ifs <;> omega
    let newState := {
      mPref := state.mPref
      wPref := state.wPref
      matching := newMatching
      proposeIndex := newProposeIndex
      bound := newBound
      matchedLastProposed := newMatchedLastProposed
      noWorseThanProposedTo := newNoWorseThanProposedTo
    }
    some newState
  else none

-- prove the termination of the algorithm
def galeShapleyTermination (state: GaleShapleyState M W) :=
    Fintype.card M * Fintype.card W - ∑ m : M, state.proposeIndex m

lemma galeShapleyDecreasing {state : GaleShapleyState M W}
    {newState : GaleShapleyState M W}
    (nextStep : galeShapleyNextStep state = some newState):
    galeShapleyTermination newState < galeShapleyTermination state := by
  unfold galeShapleyTermination
  have totalBound: ∑ m, newState.proposeIndex m ≤ Fintype.card M * Fintype.card W := by
    apply Finset.sum_le_card_nsmul
    intro x
    simp only [Finset.mem_univ, forall_true_left]
    exact newState.bound x
  have increasing: ∑ m, newState.proposeIndex m > ∑ m, state.proposeIndex m := by
    simp only [galeShapleyNextStep, ne_eq, ite_not] at nextStep
    by_cases h': notDone state

    · simp [h'] at nextStep
      simp_rw [← nextStep]
      clear nextStep

      apply Finset.sum_lt_sum
      intro i
      split <;> omega

      use (choose h')
      simp

    · simp [h'] at nextStep

  omega

def galeShapleyTerminator: Terminator (GaleShapleyState M W) := {
  nextStep := galeShapleyNextStep
  termination := galeShapleyTermination
  decreasing := fun state nd => by
    rw [Option.isSome_iff_exists] at nd
    obtain ⟨nextState, nextStep⟩ := nd
    simp_rw [nextStep]
    simp
    exact galeShapleyDecreasing nextStep
}

@[simp]
lemma galeShapleyTerminatorTermination_rfl (state: GaleShapleyState M W):
    galeShapleyTerminator.termination state =
      Fintype.card M * Fintype.card W - ∑ m : M, state.proposeIndex m := by rfl

@[simp]
lemma galeShapleyTerminatorNextStep (state: GaleShapleyState M W):
    galeShapleyTerminator.nextStep state = galeShapleyNextStep state := by rfl

/- This is a key definition. It runs iterations of `galeShapleyNextStep` repeatedly until it
   terminates, and collects the result into a list. -/
def galeShapleyIterate (state: GaleShapleyState M W): List (GaleShapleyState M W) :=
    iterate galeShapleyTerminator state

@[simp]
lemma galeShapleyIterate_rfl (state: GaleShapleyState M W):
    iterate galeShapleyTerminator state = galeShapleyIterate state := by rfl

theorem galeShapleyIterateNonEmpty: ∀ (state: GaleShapleyState M W),
    galeShapleyIterate state ≠ [] := by
  intro state
  unfold galeShapleyIterate iterate
  split <;> simp

/- Define the initial state of the algorithm, and functions to run the algorithm starting from
   the initial state.
-/
variable
    (mPref: Pref M W)
    (wPref: Pref W M)

@[simps]
def initialState: GaleShapleyState M W := {
    mPref := mPref
    wPref := wPref
    matching := emptyMatching
    proposeIndex := fun _ => 0
    bound := by simp
    matchedLastProposed := by simp [emptyMatching]
    noWorseThanProposedTo := by simp
  }

def galeShapleyList: List (GaleShapleyState M W) := galeShapleyIterate (initialState mPref wPref)

@[simp]
lemma galeShapleyList_rfl: galeShapleyIterate (initialState mPref wPref) = galeShapleyList mPref wPref := by rfl

theorem galeShapleyListNonEmpty: galeShapleyList mPref wPref ≠ [] := by
  apply galeShapleyIterateNonEmpty

/- This is a key definition. Given a set of preferences, it runs the algorithm from the initial state
   and returns the final state of the algorithm. -/
def galeShapleyFinalState: GaleShapleyState M W :=
  (galeShapleyList mPref wPref).getLast (galeShapleyListNonEmpty mPref wPref)

@[simp]
lemma galeShapleyFinalState_rfl:
    (galeShapleyList mPref wPref).getLast (galeShapleyListNonEmpty mPref wPref) =
    galeShapleyFinalState mPref wPref
  := by rfl

/- Extract the final matching from the final state. -/
def galeShapley: Matching M W := (galeShapleyFinalState mPref wPref).matching

@[simp]
lemma galeShapley_def:
  (galeShapleyFinalState mPref wPref).matching = galeShapley mPref wPref := by rfl

/- At this point, we have defined the algorithm. The rest of this file is proving that it
   produces a stable matching.
-/

-- Various lemmas relating the next state to the current state

lemma notDoneIsSome {state: GaleShapleyState M W}: notDone state → Option.isSome (galeShapleyNextStep state) := by
  intro nd
  unfold galeShapleyNextStep
  simp [nd]

lemma someIsNotDone {state: GaleShapleyState M W}: Option.isSome (galeShapleyNextStep state) → notDone state := by
  intro is_some
  by_contra bad
  simp [galeShapleyNextStep, bad] at is_some

lemma nextStateSomeIsNotDone {state: GaleShapleyState M W} (nextStateSome: galeShapleyNextStep state = some nextState):
    notDone state := by
  unfold galeShapleyNextStep at nextStateSome
  split_ifs at nextStateSome
  tauto

lemma nextStateNoneisDone {state: GaleShapleyState M W} (nextStateSome: galeShapleyNextStep state = none) :
    ¬ notDone state := by
  unfold galeShapleyNextStep at nextStateSome
  split_ifs at nextStateSome with done
  exact done

lemma pref_invariant_nextState' {state: (GaleShapleyState M W)} (h: notDone state):
     ((galeShapleyNextStep state).get (notDoneIsSome h)).mPref = state.mPref ∧
     ((galeShapleyNextStep state).get (notDoneIsSome h)).wPref = state.wPref := by
  simp [galeShapleyNextStep, h]

lemma pref_invariant_nextState {state: (GaleShapleyState M W)}
    (nextStateSome: galeShapleyNextStep state = some nextState):
    nextState.mPref = state.mPref ∧ nextState.wPref = state.wPref := by
  have := pref_invariant_nextState' (nextStateSomeIsNotDone nextStateSome)
  simp_rw [nextStateSome] at this
  simp at this
  exact this

lemma mPref_invariant_nextState {state: (GaleShapleyState M W)}
    (nextStateSome: galeShapleyNextStep state = some nextState): nextState.mPref = state.mPref := by
  exact (pref_invariant_nextState nextStateSome).1

lemma wPref_invariant_nextState {state: (GaleShapleyState M W)}
    (nextStateSome: galeShapleyNextStep state = some nextState): nextState.wPref = state.wPref := by
  exact (pref_invariant_nextState nextStateSome).2

-- Lemmas used to carry out induction arguments on the algorithm.
-- Specializes the corresponding lemmas in `Iterate` for convenience.

lemma iterate_single_state {state: GaleShapleyState M W} (noneStep: galeShapleyNextStep state = none):
    galeShapleyIterate state = [state] := Iterate.iterate_single_state noneStep

lemma iterate_next_state {state: GaleShapleyState M W} (nextStep: galeShapleyNextStep state = some nextState):
    galeShapleyIterate state = state :: galeShapleyIterate nextState := Iterate.iterate_next_state nextStep

-- global invariance of mPref and wPref

lemma pref_invariant': ∀ state: (GaleShapleyState M W),
    ∀ s ∈ (galeShapleyIterate state), s.mPref = state.mPref ∧ s.wPref = state.wPref := by
  intro state
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
      have single_state := iterate_single_state noneStep
      rw [single_state]
      simp
  | case2 state nextState nextStep ih =>
      simp [iterate_next_state nextStep]
      suffices nextState.mPref = state.mPref ∧ nextState.wPref = state.wPref by (
        rw [← this.1, ← this.2]
        exact ih
      )
      exact pref_invariant_nextState nextStep

lemma pref_invariant: (galeShapleyFinalState mPref wPref).mPref = mPref ∧
   (galeShapleyFinalState mPref wPref).wPref = wPref := by
  apply pref_invariant' (initialState mPref wPref)
  simp only [galeShapleyFinalState, galeShapleyList]
  apply List.getLast_mem

@[simp]
lemma mPref_invariant: (galeShapleyFinalState mPref wPref).mPref = mPref :=
  (pref_invariant mPref wPref).1

@[simp]
lemma wPref_invariant: (galeShapleyFinalState mPref wPref).wPref = wPref :=
  (pref_invariant mPref wPref).2

-- Now we prepare for the proof that Gale-Shapley algorithm produces a stable matching.

lemma finalStateHasNoNextStep': ∀ state: (GaleShapleyState M W),
    galeShapleyNextStep ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty state)) = none := by
  intro state
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
      simp_rw [iterate_single_state noneStep]
      simpa
  | case2 state nextState nextStep ih =>
      simp_rw [iterate_next_state nextStep]
      rw [List.getLast_cons (galeShapleyIterateNonEmpty _)]
      exact ih

lemma finalStateHasNoNextStep: galeShapleyNextStep (galeShapleyFinalState mPref wPref) = none := by
  apply finalStateHasNoNextStep'

lemma unmatchedExhaustedProposals: ∀ m, galeShapley mPref wPref m = none →
    (galeShapleyFinalState mPref wPref).proposeIndex m = Fintype.card W := by
  have := finalStateHasNoNextStep mPref wPref
  apply nextStateNoneisDone at this
  unfold notDone at this
  push_neg at this
  simp at this
  exact this

def isUnstablePair (matching: Matching M W) (m: M) (w: W): Prop :=
  let invMatching := inverseMatching matching
  (matching m = none ∨ (mPref m).symm w < (mPref m).symm (Option.getD (matching m) w)) ∧
  (invMatching w = none ∨ (wPref w).symm m < (wPref w).symm (Option.getD (invMatching w) m))


def isStableMatching (matching: Matching M W): Prop :=
  ∀ m, ∀ w, ¬ (isUnstablePair mPref wPref matching m w)

/- This is the main theorem: The Gale-Shapley algorithm always produces a stable matching. -/
theorem galeShapleyGivesStableMatching: isStableMatching mPref wPref (galeShapley mPref wPref) := by
  intros m w
  by_contra unstable
  simp only [isUnstablePair] at unstable
  rcases unstable with ⟨mUnstable, wUnstable⟩
  let gsFinalState := galeShapleyFinalState mPref wPref
  by_cases m_proposed_w: (mPref m).symm w < gsFinalState.proposeIndex m
  · have := gsFinalState.noWorseThanProposedTo m w
    simp [gsFinalState] at this
    specialize this m_proposed_w
    obtain ⟨m', w_matches_m', w_prefers_m'⟩ := this
    simp [w_matches_m'] at wUnstable
    omega
  · rcases h: ((galeShapley mPref wPref) m) with _ | w'
    · have := unmatchedExhaustedProposals mPref wPref m
      specialize this h
      rw [this] at m_proposed_w
      push_neg at m_proposed_w
      have : (mPref m).symm w < Fintype.card W := by simp only [Fin.is_lt]
      omega
    · simp [h] at mUnstable
      have := (galeShapleyFinalState mPref wPref).matchedLastProposed m w' h
      simp at this
      simp only [gsFinalState] at m_proposed_w
      omega

theorem galeShapleyNoUnstablePair {m: M} {w: W} (h: isUnstablePair mPref wPref (galeShapley mPref wPref) m w): False := by
  have := galeShapleyGivesStableMatching mPref wPref
  unfold isStableMatching at this
  specialize this m w
  contradiction
