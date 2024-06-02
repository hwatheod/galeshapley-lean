import GaleShapley.Compute.Matching
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GaleShapley.Compute

open BigOperators

variable {M W: Type} [Fintype M] [Fintype W] [LinearOrder M] [DecidableEq M] [DecidableEq W]

abbrev Pref (M W: Type) [Fintype M] [Fintype W] := M → Fin (Fintype.card W) ≃ W

structure GaleShapleyState (M W: Type) [Fintype M] [Fintype W] [LinearOrder M] [DecidableEq M] [DecidableEq W] where
  mPref: Pref M W
  wPref: Pref W M
  matching: Matching M W
  proposeIndex: M → Nat
  bound: ∀ m, proposeIndex m ≤ Fintype.card W
  matchedLastProposed:
    ∀ m, ∀ w, matching m = some w → (mPref m).symm w + 1 = proposeIndex m
  noWorseThanProposedTo:
    ∀ m, ∀ w, (mPref m).symm w < proposeIndex m →     -- m proposed to w
      ∃ m', (inverseMatching matching w) = some m' ∧  -- m' is paired with w
        (wPref w).symm m' <= (wPref w).symm m

abbrev notDone (state: GaleShapleyState M W) := ∃ m, state.matching m = none ∧ state.proposeIndex m < Fintype.card W

def proposer {state: GaleShapleyState M W} (h: notDone state): M :=
    Finset.min' {m : M | state.matching m = none ∧ state.proposeIndex m < Fintype.card W}.toFinset
    (by
      unfold notDone at h
      exact (Set.toFinset_nonempty.mpr h)
    )

def proposee {state: GaleShapleyState M W} (h: notDone state) :=
    state.mPref (proposer h) ⟨state.proposeIndex (proposer h),
    (by
      unfold notDone at h
      unfold proposer
      have := Finset.min'_mem
        {m : M | state.matching m = none ∧ state.proposeIndex m < Fintype.card W}.toFinset
        (Set.toFinset_nonempty.mpr h)
      simp at this ⊢
      obtain ⟨_, this⟩ := this
      exact this
    )⟩

def curMatch {state: GaleShapleyState M W} (h: notDone state): Option M :=
    inverseMatching state.matching (proposee h)

def newMatch {state: GaleShapleyState M W} (h: notDone state) :=
    match curMatch h with
    | none => proposer h
    | some m => if (state.wPref (proposee h)).symm (proposer h) ≤
        (state.wPref (proposee h)).symm m then proposer h else m

def galeShapleyNextStep (state: GaleShapleyState M W): Option (GaleShapleyState M W) :=
  if h0: notDone state then
    let m0 := proposer h0
    have m0_proposer: m0 = proposer h0 := by rfl
    have hm0: state.matching m0 = none ∧ state.proposeIndex m0 < Fintype.card W := by
      rw [m0_proposer]
      unfold proposer
      have := Finset.min'_mem
        {m : M | state.matching m = none ∧ state.proposeIndex m < Fintype.card W}.toFinset
        (Set.toFinset_nonempty.mpr h0)
      simp at this ⊢
      exact this
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
          have := inverseProperty.mp m_matches_w0
          simp [w0_curMatch, curMatch, this]
        exact False.elim (h1.2 this)
      · exact inverseProperty.mp
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
          rw [← inverseProperty] at h1''
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
        rw [← inverseProperty]
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
          · rw [← inverseProperty] at w_matches_m'
            rw [← inverseProperty]
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
                have := inverseProperty.mpr h3
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
          · rw [← inverseProperty]
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

      use (proposer h')
      simp

    · simp [h'] at nextStep

  omega

set_option linter.unusedVariables false in
def galeShapleyFinalState (state: GaleShapleyState M W): GaleShapleyState M W :=
    match h: galeShapleyNextStep state with  -- h is needed in the decreasing_by proof
    | none => state
    | some newState => galeShapleyFinalState newState
termination_by
  galeShapleyTermination state
decreasing_by
  simp_wf
  exact galeShapleyDecreasing h

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

def galeShapley: Matching M W := (galeShapleyFinalState (initialState mPref wPref)).matching

abbrev isUnstablePair (matching: Matching M W) (m: M) (w: W): Prop :=
  let invMatching := inverseMatching matching
  (matching m = none ∨ (mPref m).symm w < (mPref m).symm (Option.getD (matching m) w)) ∧
  (invMatching w = none ∨ (wPref w).symm m < (wPref w).symm (Option.getD (invMatching w) m))


abbrev isStableMatching (matching: Matching M W): Prop :=
  ∀ m, ∀ w, ¬ (isUnstablePair mPref wPref matching m w)
