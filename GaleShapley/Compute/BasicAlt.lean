import GaleShapley.Compute.Matching
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GaleShapley.Compute

open BigOperators

variable {M W: Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

abbrev Pref (M W: Type) [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] := M → Fin (Fintype.card W) ≃ W

structure GaleShapleyState (M W: Type) [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] where
  mPref: Pref M W
  wPref: Pref W M
  matching: Matching M W
  proposeIndex: M → Nat
  bound: ∀ m, proposeIndex m ≤ Fintype.card W
  matchedLessThanProposeIndex:
    ∀ m, ∀ w, matching m = some w → (mPref m).symm w < proposeIndex m
  noWorseThanProposedTo:
    ∀ m, ∀ w, (mPref m).symm w < proposeIndex m →     -- m proposed to w
      ∃ m', (inverseMatching matching w) = some m' ∧  -- m' is paired with w
        (wPref w).symm m' <= (wPref w).symm m

def galeShapleyNextStep (state: GaleShapleyState M W): Option (GaleShapleyState M W) :=
  let wCard := Fintype.card W
  let newProposals: M → Option W := fun m =>
    let curPartner := state.matching m
    let curProposeIndex := state.proposeIndex m
    if curPartner = none then
      if h: (state.proposeIndex m >= wCard) then none else
        some (state.mPref m ⟨curProposeIndex, (by simpa only [Set.mem_setOf_eq, ge_iff_le, not_le,
          curProposeIndex, wCard] using h)⟩)
    else none
  if h0: ∀ m, newProposals m = none then none else
    let proposalsToConsider: W → Finset M := fun w =>
      let newReceivedProposals := { m | newProposals m = some w }.toFinset
      newReceivedProposals ∪ {m' | state.matching m' = some w}.toFinset
    let acceptedProposals': W → Option M := fun w =>
      if h : proposalsToConsider w = {} then none else
        let indices := (state.wPref w).invFun '' (proposalsToConsider w)
        let min_index := Finset.min' indices.toFinset (by
          simp only [Set.coe_setOf, Equiv.invFun_as_coe, Set.coe_toFinset, Set.toFinset_image,
            Set.mem_setOf_eq, Finset.image_nonempty, Set.toFinset_nonempty, indices]
          rw [Set.nonempty_iff_ne_empty]
          simp
          exact h
        )
        some (state.wPref w min_index)
    have: ∀ m, ∀ w, acceptedProposals' w = some m → state.matching m = some w ∨ newProposals m = some w := by
      intros m w w_acceptsM
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Equiv.invFun_as_coe, Set.coe_toFinset,
        Set.toFinset_image, acceptedProposals'] at w_acceptsM
      by_cases h : proposalsToConsider w = ∅
      · simp only [h, ↓reduceDite] at w_acceptsM
      · simp only [h, ↓reduceDite, Set.coe_setOf, Set.mem_setOf_eq, Option.some.injEq] at w_acceptsM
        have: m ∈ proposalsToConsider w := by
          apply_fun (state.wPref w).symm at w_acceptsM
          simp at w_acceptsM
          have: (state.wPref w).symm m ∈ Finset.image (fun a => (state.wPref w).symm a) (proposalsToConsider w) := by
            rw [← w_acceptsM]
            exact Finset.min'_mem _ _
          simp at this
          exact this
        simp [proposalsToConsider, h] at this
        exact Or.symm this
    let acceptedProposals: Matching W M := {
      matching := acceptedProposals'
      matchingCondition := by
        simp [isMatching]
        intros w1 w2 m equal2

        rw [equal2]
        intro equal1
        have this1 := this m w1 equal1
        have this2 := this m w2 equal2
        by_cases mPaired: state.matching m = none
        simp [mPaired] at this1 this2
        rw [this1] at this2
        simp only [Option.some.injEq] at this2
        exact this2

        simp [newProposals, mPaired] at this1 this2
        rw [this1] at this2
        simp only [Option.some.injEq] at this2
        exact this2
    }
    let newMatching := inverseMatching acceptedProposals
    let newProposeIndex := fun m =>
      let curProposeIndex := state.proposeIndex m
      if newProposals m = none then curProposeIndex else curProposeIndex + 1
    have newBound: ∀ m, newProposeIndex m ≤ wCard := by
      intro m
      simp only [newProposeIndex]
      by_cases h2: newProposals m = none
      simp only [h2, ↓reduceIte]
      exact state.bound m
      simp only [h2, ↓reduceIte]
      simp only [ge_iff_le, Set.coe_setOf, Set.mem_setOf_eq, ite_eq_right_iff, dite_eq_left_iff,
        not_le, imp_false, not_lt, not_forall, exists_prop, newProposals] at h2
      omega
    have newMatchedLessThanProposeIndex:
        ∀ m, ∀ w, newMatching m = some w → (state.mPref m).symm w < newProposeIndex m := by
      intros m w m_newMatches_w
      by_cases h: state.matching m = newMatching m
      · rw [← h] at m_newMatches_w
        have := state.matchedLessThanProposeIndex m w m_newMatches_w
        simp [newProposeIndex]
        split <;> omega
      · rw [m_newMatches_w] at h
        have w_accepted_m := this m w
        simp [h] at w_accepted_m
        simp only [newMatching] at m_newMatches_w
        have := inverseProperty.mpr m_newMatches_w
        specialize w_accepted_m this
        simp [newProposeIndex, w_accepted_m]
        simp [newProposals] at w_accepted_m
        split_ifs at w_accepted_m
        simp at w_accepted_m
        apply_fun (state.mPref m).symm at w_accepted_m
        simp at w_accepted_m
        rw [← w_accepted_m]
        simp
    have w_proposedTo: ∀ w, ∀ m', m' ∈ proposalsToConsider w →
        (∃ m'', acceptedProposals w = some m'' ∧
          (state.wPref w).symm m'' ≤ (state.wPref w).symm m') := by
      intro w m' m'_proposed_w
      have proposalsNonempty: proposalsToConsider w ≠ ∅ := by
        by_contra bad
        rw [bad] at m'_proposed_w
        contradiction
      have: acceptedProposals w ≠ none := by
        simp [acceptedProposals, acceptedProposals']
        exact proposalsNonempty
      apply Option.ne_none_iff_exists.mp at this
      obtain ⟨m'', w_accepted_m''⟩ := this
      use m''
      constructor
      · exact w_accepted_m''.symm
      · simp [acceptedProposals', proposalsNonempty] at w_accepted_m''
        apply_fun (state.wPref w).symm at w_accepted_m''
        simp at w_accepted_m''
        rw [w_accepted_m'']
        apply Finset.min'_le
        simp
        exact m'_proposed_w
    have newNoWorseThanProposedTo:
      ∀ m, ∀ w, (state.mPref m).symm w < newProposeIndex m →     -- m proposed to w
        ∃ m', (inverseMatching newMatching w) = some m' ∧  -- m' is paired with w
          (state.wPref w).symm m' <= (state.wPref w).symm m := by
      intros m w lt_newProposeIndex
      simp [newMatching]
      by_cases lt_curProposed: ↑((state.mPref m).symm w) < state.proposeIndex m
      · have := state.noWorseThanProposedTo m w lt_curProposed
        obtain ⟨m', w_matches_m', w_prefers_m'_to_m⟩ := this
        have m'_matches_w := inverseProperty.mpr w_matches_m'
        have m'_proposed_w: m' ∈ proposalsToConsider w := by simp [proposalsToConsider, m'_matches_w]
        obtain ⟨m'', w_accepted_m'', w_prefers_m''_to_m'⟩ := w_proposedTo w m' m'_proposed_w
        use m''
        simp only [acceptedProposals] at w_accepted_m''
        constructor
        · exact w_accepted_m''
        · omega
      · simp [newProposeIndex] at lt_newProposeIndex
        have: newProposals m ≠ none := by
          by_contra bad
          simp [bad] at lt_newProposeIndex
          contradiction
        simp [this] at lt_newProposeIndex
        simp [newProposals] at this
        have m_proposed_w: (state.mPref m).symm w = state.proposeIndex m := by omega
        have: m ∈ proposalsToConsider w := by
          simp [proposalsToConsider]
          left
          simp [newProposals, this]
          have: ((state.mPref m).symm w) < wCard := ((state.mPref m).symm w).isLt
          rw [m_proposed_w] at this
          have: ¬ (wCard ≤ state.proposeIndex m) := by omega
          simp [this]
          apply_fun (state.mPref m).symm
          simp
          apply_fun (fun x => x.val)
          simp
          exact m_proposed_w.symm

          exact Fin.val_injective
        exact w_proposedTo w m this
    let newState := {
      mPref := state.mPref
      wPref := state.wPref
      matching := newMatching
      proposeIndex := newProposeIndex
      bound := newBound
      matchedLessThanProposeIndex := newMatchedLessThanProposeIndex
      noWorseThanProposedTo := newNoWorseThanProposedTo
    }
    some newState

set_option linter.unusedVariables false in
def galeShapleyIterate (state: GaleShapleyState M W): List (GaleShapleyState M W) :=
    match h: galeShapleyNextStep state with  -- h is needed in the decreasing_by proof
    | none => [state]
    | some newState => state :: galeShapleyIterate newState
termination_by
  let mCard := Fintype.card M
  let wCard := Fintype.card W
  mCard * wCard - ∑ m, state.proposeIndex m
decreasing_by
  let mCard := Fintype.card M
  let wCard := Fintype.card W
  -- This is copied from simp_wf, but as a simp only since otherwise it takes forever
  simp only [InvImage, WellFoundedRelation.rel, Prod.Lex, Nat.lt_wfRel, sizeOf_nat, Nat.lt_eq]
  have totalBound: ∑ m, newState.proposeIndex m ≤ mCard * wCard := by
    apply Finset.sum_le_card_nsmul
    intro x
    simp only [Finset.mem_univ, forall_true_left]
    exact newState.bound x
  have increasing: ∑ m, newState.proposeIndex m > ∑ m, state.proposeIndex m := by
    simp only [galeShapleyNextStep, ge_iff_le, ite_eq_right_iff, dite_eq_left_iff, not_le,
      imp_false, not_lt, Set.toFinset_setOf, Set.mem_setOf_eq, Equiv.invFun_as_coe,
      Finset.coe_union, Finset.coe_filter, Finset.mem_univ, true_and, Set.toFinset_image,
      Set.toFinset_union] at h
    split_ifs at h with cond

    simp only [Option.some.injEq] at h
    simp_rw [← h]
    clear h

    apply Finset.sum_lt_sum
    intro i
    split <;> omega

    push_neg at cond
    obtain ⟨i, hi⟩ := cond
    use i
    have hi' : ¬ Fintype.card W ≤ state.proposeIndex i := by omega
    simp only [Finset.mem_univ, hi, hi', forall_true_left, ↓reduceIte, lt_add_iff_pos_right,
      zero_lt_one, and_self]

  generalize mCard * wCard = a at totalBound increasing ⊢
  generalize ∑ m : M, state.proposeIndex m = b at totalBound increasing ⊢
  generalize ∑ m : M, newState.proposeIndex m = c at totalBound increasing ⊢
  omega

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
    matchedLessThanProposeIndex := by simp [emptyMatching]
    noWorseThanProposedTo := by simp
  }

def galeShapleyList: List (GaleShapleyState M W) := galeShapleyIterate (initialState mPref wPref)

theorem galeShapleyIterateNonEmpty: ∀ (state: GaleShapleyState M W),
    galeShapleyIterate state ≠ [] := by
  intro state
  unfold galeShapleyIterate
  split <;> simp

theorem galeShapleyListNonEmpty: galeShapleyList mPref wPref ≠ [] := by
  apply galeShapleyIterateNonEmpty

lemma iterate_single_state {state: GaleShapleyState M W} (noneStep: galeShapleyNextStep state = none):
    galeShapleyIterate state = [state] := by
  unfold galeShapleyIterate
  rw [noneStep]

lemma iterate_next_state {state: GaleShapleyState M W} (nextStep: galeShapleyNextStep state = some nextState):
    galeShapleyIterate state = state :: galeShapleyIterate nextState := by
  conv_lhs => unfold galeShapleyIterate
  rw [nextStep]

def galeShapleyFinalState: GaleShapleyState M W :=
  List.getLast (galeShapleyList mPref wPref) (galeShapleyListNonEmpty mPref wPref)

lemma pref_invariant' {state: GaleShapleyState M W}:
    ∀ {{s}}, s ∈ galeShapleyIterate state → s.mPref = state.mPref ∧ s.wPref = state.wPref := by
  induction state using galeShapleyIterate.induct with
  | case1 state noneStep =>
      rw [iterate_single_state noneStep]
      simp
  | case2 state nextState nextStep ih =>
      rw [iterate_next_state nextStep]
      suffices state.mPref = nextState.mPref ∧ state.wPref = nextState.wPref by (
        simp [this]
        exact ih
      )
      simp [galeShapleyNextStep] at nextStep
      split_ifs at nextStep with h
      simp [h] at nextStep
      apply_fun (fun x => (x.mPref, x.wPref)) at nextStep
      simp at nextStep
      exact nextStep

lemma pref_invariant: (galeShapleyFinalState mPref wPref).mPref = mPref ∧
   (galeShapleyFinalState mPref wPref).wPref = wPref := by
  apply pref_invariant' (state := initialState mPref wPref)
  simp only [galeShapleyFinalState, galeShapleyList]
  apply List.getLast_mem

@[simp]
lemma mPref_invariant: (galeShapleyFinalState mPref wPref).mPref = mPref :=
  (pref_invariant mPref wPref).1

@[simp]
lemma wPref_invariant: (galeShapleyFinalState mPref wPref).wPref = wPref :=
  (pref_invariant mPref wPref).2

def galeShapley: Matching M W := (galeShapleyFinalState mPref wPref).matching

set_option linter.unusedVariables false in
lemma finalStateHasNoNextStep': ∀ state: (GaleShapleyState M W),
    galeShapleyNextStep (List.getLast (galeShapleyIterate state) (galeShapleyIterateNonEmpty state)) = none := by
  intro state
  induction state using galeShapleyIterate.induct with
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
  unfold galeShapleyNextStep at this
  simp only [ge_iff_le, mPref_invariant, ite_eq_right_iff, dite_eq_left_iff,
    not_le, imp_false, not_lt, wPref_invariant, Set.toFinset_setOf, Set.mem_setOf_eq,
    Equiv.invFun_as_coe, Finset.coe_union, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.toFinset_image, Set.toFinset_union, not_forall, Classical.not_imp, not_exists, not_and] at this
  intros m m_unmatched
  specialize this m m_unmatched
  have := (galeShapleyFinalState mPref wPref).bound m
  omega

@[reducible]
def isUnstablePair (matching: Matching M W) (m: M) (w: W): Prop :=
  let invMatching := inverseMatching matching
  (matching m = none ∨ (mPref m).symm w < (mPref m).symm (Option.getD (matching m) w)) ∧
  (invMatching w = none ∨ (wPref w).symm m < (wPref w).symm (Option.getD (invMatching w) m))


@[reducible]
def isStableMatching (matching: Matching M W): Prop :=
  ∀ m, ∀ w, ¬ (isUnstablePair mPref wPref matching m w)

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
    have: (galeShapleyFinalState mPref wPref).matching = galeShapley mPref wPref := by rfl
    rw [this] at w_matches_m'
    simp [w_matches_m'] at wUnstable
    omega
  · have := unmatchedExhaustedProposals mPref wPref m
    rcases h: ((galeShapley mPref wPref) m) with _ | w'
    · specialize this h
      rw [this] at m_proposed_w
      push_neg at m_proposed_w
      have : (mPref m).symm w < Fintype.card W := by simp only [Fin.is_lt]
      omega
    · simp [h] at mUnstable
      have := (galeShapleyFinalState mPref wPref).matchedLessThanProposeIndex m w' h
      simp at this
      simp only [gsFinalState] at m_proposed_w
      omega

theorem galeShapleyNoUnstablePair {m: M} {w: W} (h: isUnstablePair mPref wPref (galeShapley mPref wPref) m w): False := by
  have := galeShapleyGivesStableMatching mPref wPref
  unfold isStableMatching at this
  specialize this m w
  contradiction
