import GaleShapley.Matching
import GaleShapley.Basic

/-!

  # Lemmas for the Gale-Shapley algorithm

  In this file, we prove many lemmas about an arbitrary execution of the Gale-Shapley
  algorithm.

-/
namespace GaleShapley

open Classical GaleShapley.Iterate
noncomputable section

variable {M W: Type} [Fintype M] [Fintype W]
  (mPref: Pref M W)
  (wPref: Pref W M)

def proposed (m: M) (w: W) :=
    ∃ s ∈ galeShapleyList mPref wPref, ∃ (h: notDone s), proposedAtState h m w

def neverRejectedFromState (state: GaleShapleyState M W) (m: M) (w: W) :=
    ∀ s ∈ galeShapleyIterate state, (h: notDone s) →
    ¬ rejectedAtState h m w

-- Lemmas about current state

lemma newMatch_choices {state: GaleShapleyState M W} (h: notDone state):
    newMatch h = choose h ∨ newMatch h = curMatch h := by
  simp only [newMatch]
  split <;> tauto
  split_ifs <;> tauto

lemma didNotPropose {state: GaleShapleyState M W} (h: notDone state)
    (m_matched: state.matching m ≠ none): m ≠ choose h := by
  by_contra bad
  have := choose_spec h
  rw [← bad] at this
  tauto

lemma curMatch_lemma {state: GaleShapleyState M W} {m: M} (h: notDone state):
    curMatch h = some m → state.matching m = some (proposee h) := by
  intros m_eq_curMatch
  unfold curMatch at m_eq_curMatch
  rwa [← inverseProperty] at m_eq_curMatch

-- Lemmas about next state

lemma proposeIndex_nextState' {state: (GaleShapleyState M W)} (h: notDone state) (m: M):
    ((galeShapleyNextStep state).get (notDoneIsSome h)).proposeIndex m =
      if m = choose h then state.proposeIndex m + 1 else state.proposeIndex m := by
  simp [galeShapleyNextStep, h]

lemma proposeIndex_nextState {state: (GaleShapleyState M W)}
    (nextStateSome: galeShapleyNextStep state = some nextState) (m: M):
    nextState.proposeIndex m =
      if m = choose (nextStateSomeIsNotDone nextStateSome) then state.proposeIndex m + 1 else state.proposeIndex m := by
  have := proposeIndex_nextState' (nextStateSomeIsNotDone nextStateSome) m
  simp [nextStateSome] at this
  exact this

lemma proposeIndexIsMonotonic_nextState' {state: GaleShapleyState M W} (h: notDone state)
    (m: M): state.proposeIndex m ≤ ((galeShapleyNextStep state).get (notDoneIsSome h)).proposeIndex m := by
  have := proposeIndex_nextState' h m
  split at this <;> omega

lemma proposeIndexIsMonotonic_nextState {state: GaleShapleyState M W}
    (nextStateSome: galeShapleyNextStep state = some nextState)
    (m: M): state.proposeIndex m ≤ nextState.proposeIndex m := by
  have := proposeIndexIsMonotonic_nextState' (nextStateSomeIsNotDone nextStateSome) m
  simp [nextStateSome] at this
  exact this

lemma matching_nextState' {state: (GaleShapleyState M W)} (h: notDone state) (m: M):
    ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m =
      let m0 := choose h
      let w0 := proposee h
      let w0_curMatch := curMatch h
      let w0_newMatch := newMatch h
      if m ≠ m0 ∧ w0_curMatch ≠ some m then state.matching m
      else if m = w0_newMatch then some w0
      else none
  := by simp [galeShapleyNextStep, h, createMatching]

lemma matching_nextState {state: (GaleShapleyState M W)}
    (nextStateSome: galeShapleyNextStep state = some nextState) (m: M):
    nextState.matching m =
      let m0 := choose (nextStateSomeIsNotDone nextStateSome)
      let w0 := proposee (nextStateSomeIsNotDone nextStateSome)
      let w0_curMatch := curMatch (nextStateSomeIsNotDone nextStateSome)
      let w0_newMatch := newMatch (nextStateSomeIsNotDone nextStateSome)
      if m ≠ m0 ∧ w0_curMatch ≠ some m then state.matching m
      else if m = w0_newMatch then some w0
      else none
  := by
have := matching_nextState' (nextStateSomeIsNotDone nextStateSome) m
simp only [nextStateSome] at this
exact this

lemma becameMatchedIsProposer {state: GaleShapleyState M W} (h: notDone state)
    (m_unmatched_before: state.matching m = none)
    (m_matched_after: ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m ≠ none):
    m = choose h := by
  by_contra bad
  push_neg at bad
  have := matching_nextState' h m
  simp [m_unmatched_before, m_matched_after, bad] at this
  split_ifs at this <;> try contradiction
  case _ m_eq_curMatch _ =>
  have := curMatch_lemma h m_eq_curMatch
  rw [m_unmatched_before] at this
  contradiction

lemma becameMatchedNotOutOfProposals {state: GaleShapleyState M W} (h: notDone state)
    (m_unmatched_before: state.matching m = none)
    (m_matched_after: ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m ≠ none):
    state.proposeIndex m < Fintype.card W := by
  have m_proposed: m = choose h := by
    exact becameMatchedIsProposer h m_unmatched_before m_matched_after
  by_contra bad
  have outOfProposals := (proposeMaxIndex state).mp bad
  have := choose_spec h
  rw [← m_proposed] at this
  omega

lemma becameMatchedProposedTo {state: GaleShapleyState M W} (h: notDone state)
    (m_unmatched_before: state.matching m = none)
    (m_matched_after: ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m = some w):
  proposee h = w := by
  have m_proposed: m = choose h := by
    exact becameMatchedIsProposer h m_unmatched_before  (Option.ne_none_iff_exists'.mpr ⟨w, m_matched_after⟩)
  have := matching_nextState' h m
  simp [m_unmatched_before, m_matched_after, ← m_proposed] at this
  split_ifs at this; try contradiction
  simp at this
  exact this.symm

lemma becameMatchedIncreasesProposerIndex' {state: GaleShapleyState M W} {m: M}
    (h: notDone state)
    (m_unmatched_before: state.matching m = none)
    (m_matched_after: ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m ≠ none):
    state.proposeIndex m < ((galeShapleyNextStep state).get (notDoneIsSome h)).proposeIndex m := by
  have m_proposed: m = choose h := by
    exact becameMatchedIsProposer h m_unmatched_before m_matched_after
  have proposeIndex := proposeIndex_nextState' h m
  simp [m_unmatched_before, m_matched_after, ← m_proposed, proposeIndex]

lemma becameMatchedIncreasesProposerIndex {state: GaleShapleyState M W} {m: M}
    (nextStateSome: galeShapleyNextStep state = some nextState)
    (m_unmatched_before: state.matching m = none)
    (m_matched_after: nextState.matching m ≠ none):
    state.proposeIndex m < nextState.proposeIndex m := by
  have := becameMatchedIncreasesProposerIndex' (nextStateSomeIsNotDone nextStateSome) m_unmatched_before
  simp only [nextStateSome] at this
  exact this m_matched_after

lemma becameSingleImpliesRejected {state: GaleShapleyState M W} {m: M}
    (nextStateSome: galeShapleyNextStep state = some nextState)
    (m_matched_before: state.matching m ≠ none)
    (m_unmatched_after: nextState.matching m = none):
    let nd := (nextStateSomeIsNotDone nextStateSome)
    state.matching m = some (proposee nd) ∧ rejectee nd = some m := by
  intro nd
  have := matching_nextState' nd m
  have m_not_propose := didNotPropose nd m_matched_before
  simp [nextStateSome, m_matched_before, m_unmatched_after, m_not_propose] at this
  split_ifs at this <;> try tauto
  case _ m_eq_curMatch m_not_newMatch =>
  simp [rejectee, m_eq_curMatch, m_not_newMatch]
  simp [curMatch, ← inverseProperty] at m_eq_curMatch
  exact m_eq_curMatch

lemma proposerRemainsSingleImpliesRejected {state: GaleShapleyState M W} {m: M}
    (nextStateSome: galeShapleyNextStep state = some nextState)
    (m_proposed: m = choose (nextStateSomeIsNotDone nextStateSome))
    (m_unmatched_after: nextState.matching m = none):
    rejectee (nextStateSomeIsNotDone nextStateSome) = some m := by
  have := matching_nextState nextStateSome m
  simp [m_unmatched_after] at this
  split_ifs at this <;> tauto
  case _ _ m_ne_newMatch =>
  unfold rejectee
  rcases h: curMatch (nextStateSomeIsNotDone nextStateSome) with _ | m' <;> simp [h]
  · simp [newMatch, h] at m_ne_newMatch
    tauto
  · rw [← m_proposed]
    split_ifs <;> tauto
    have := newMatch_choices (nextStateSomeIsNotDone nextStateSome)
    rw [← m_proposed, h] at this
    simp at this
    tauto

lemma curMatchedNextStepDidntIncreaseProposeIndex' {state: GaleShapleyState M W} {m: M}
    (h: notDone state)
    (m_matched_before: state.matching m ≠ none):
    state.proposeIndex m = ((galeShapleyNextStep state).get (notDoneIsSome h)).proposeIndex m := by
  have := proposeIndex_nextState' h m
  rw [this]
  split
  · case _ mProposed =>
      have := didNotPropose h m_matched_before
      contradiction
  · rfl

lemma curMatchedNextStepDidntIncreaseProposeIndex {state: GaleShapleyState M W} {m: M}
    (nextStateSome: galeShapleyNextStep state = some nextState)
    (m_matched_before: state.matching m ≠ none):
    state.proposeIndex m = nextState.proposeIndex m := by
  have := curMatchedNextStepDidntIncreaseProposeIndex' (nextStateSomeIsNotDone nextStateSome)
    m_matched_before
  simp_rw [nextStateSome] at this
  simp at this
  exact this

lemma onlyOneCanBecomeMatched {state: GaleShapleyState M W}
    (h: notDone state)
    (m_unmatched_before: state.matching m = none)
    (m_matched_after: ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m ≠ none)
    (m'_unmatched_before: state.matching m' = none)
    (m'_matched_after: ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m' ≠ none):
    m = m' := by
  have m_proposed := becameMatchedIsProposer h m_unmatched_before m_matched_after
  have m'_proposed := becameMatchedIsProposer h m'_unmatched_before m'_matched_after
  rwa [← m'_proposed] at m_proposed

lemma matchedEitherSameOrSingleNext' {state: GaleShapleyState M W}
    (h: notDone state)
    (m_matched_before: state.matching m = some w):
    ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m = none ∨
      ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m = some w := by
  have := choose_spec h
  have mDidNotPropose := didNotPropose h (by rw [m_matched_before]; simp)
  have nextState := matching_nextState' h m
  simp [m_matched_before] at nextState
  split_ifs at nextState <;> tauto
  case _ _ m_eq_curMatch m_eq_newMatch =>
  simp [mDidNotPropose] at m_eq_curMatch
  have := curMatch_lemma h m_eq_curMatch
  rw [← this, m_matched_before] at nextState
  tauto

lemma matchedEitherSameOrSingleNext {state: GaleShapleyState M W}
    (nextStateSome: galeShapleyNextStep state = some nextState)
    (m_matched_before: state.matching m = some w):
    nextState.matching m = none ∨ nextState.matching m = some w := by
  have := matchedEitherSameOrSingleNext' (nextStateSomeIsNotDone nextStateSome) m_matched_before
  simp_rw [nextStateSome] at this
  simp at this
  exact this

lemma noMoreProposalsImpliesSingleNextStep {state: GaleShapleyState M W} (h: notDone state) {m: M}
    (unmatched: state.matching m = none) (outOfProposals: state.proposeIndex m = Fintype.card W):
    ((galeShapleyNextStep state).get (notDoneIsSome h)).matching m = none ∧
    ((galeShapleyNextStep state).get (notDoneIsSome h)).proposeIndex m = Fintype.card W := by
  have mDidNotPropose: m ≠ choose h := by
    by_contra bad
    have := choose_spec h
    rw [← bad] at this
    omega
  constructor
  · have := matching_nextState' h m
    simp [unmatched, mDidNotPropose] at this
    rw [this]
    split_ifs <;> try rfl
    case _ m_eq_curMatch _ =>
    have := curMatch_lemma h m_eq_curMatch
    rw [this] at unmatched
    contradiction
  · have := proposeIndex_nextState' h m
    simp [mDidNotPropose] at this
    rwa [outOfProposals] at this

lemma nextStateLastIsSame {state: GaleShapleyState M W}
    (nextStateSome: galeShapleyNextStep state = some nextState):
    (galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty state) =
    (galeShapleyIterate nextState).getLast (galeShapleyIterateNonEmpty _) :=
  iterate_nextStateLastIsSame nextStateSome

-- Lemmas about galeShapleyIterate

@[simp]
lemma galeShapleyHelperHead (state: GaleShapleyState M W):
    (galeShapleyIterate state).head (galeShapleyIterateNonEmpty state) = state :=
  iterateHead galeShapleyTerminator state

@[simp]
lemma initialStateIsInitialElement:
    (galeShapleyList mPref wPref).head (galeShapleyListNonEmpty mPref wPref) =
      initialState mPref wPref := by
  apply galeShapleyHelperHead

lemma tailLast {state: GaleShapleyState M W}:
    ∀ s ∈ (galeShapleyIterate state),
      (galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty state) =
      (galeShapleyIterate s).getLast (galeShapleyIterateNonEmpty s) := by
  apply iterateTailLast

-- Lemmas relating current state to arbitrary prior states or future states

lemma neverRejectedFuture {state: GaleShapleyState M W} {m: M} {w: W}:
    neverRejectedFromState state m w →
     ∀ s ∈ (galeShapleyIterate state), neverRejectedFromState s m w := by
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this]
  | case2 state nextState nextStep ih =>
    unfold neverRejectedFromState at ih ⊢
    have := iterate_next_state nextStep
    simp_rw [this]
    simp [this]
    intros not_rejected_now not_rejected_future
    specialize ih not_rejected_future
    constructor
    · exact ⟨not_rejected_now, not_rejected_future⟩
    · exact ih

lemma proposeIndexMononicity {state state': GaleShapleyState M W} (before: state' ∈ galeShapleyIterate state):
    ∀ (m: M), state.proposeIndex m ≤ state'.proposeIndex m := by
  intro m
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
      simp [iterate_single_state noneStep] at before
      rw [before]
  | case2 state nextState nextStep ih =>
      simp [iterate_next_state nextStep] at before
      rcases before with state'_same | state'_future
      · rw [state'_same]
      · specialize ih state'_future
        have := proposeIndexIsMonotonic_nextState nextStep m
        omega

lemma proposeIndexInequality' (state: GaleShapleyState M W) (m: M) (w: W)
    (h_state: state ∈ galeShapleyList mPref wPref):
    (∃ s ∈ galeShapleyList mPref wPref, ∃ (nd: notDone s), s ≠ state ∧ state ∈ galeShapleyIterate s ∧
      proposedAtState nd m w) ↔
        ↑((mPref m).symm w) < state.proposeIndex m := by
  have := stateStrongInduction galeShapleyTerminator (initialState mPref wPref)
  simp at this
  revert h_state
  specialize this (fun state => ((∃ s ∈ galeShapleyList mPref wPref, ∃ (nd : notDone s),
    s ≠ state ∧ state ∈ galeShapleyIterate s ∧ proposedAtState nd m w) ↔
    ↑((mPref m).symm w) < state.proposeIndex m))
  apply this
  clear this
  intro s hs ih
  by_cases h: s = initialState mPref wPref
  · simp [h]
    intros t ht t_ne_s t_before_s
    have := iterateAntisymmetry
        (iterateReflexivity galeShapleyTerminator (initialState mPref wPref)) ht
        ht t_before_s
    exact False.elim (t_ne_s this.symm)
  · have s_pred := iterate_predecessor hs h
    obtain ⟨s_pred, ⟨h_s_pred, s_pred_is_pred⟩, _⟩ := s_pred
    specialize ih s_pred h_s_pred (iterate_ne_predecessor s_pred_is_pred) (iterateNextState s_pred_is_pred)
    by_cases h2: (mPref m).symm w < s_pred.proposeIndex m
    · simp only [h2, iff_true] at ih
      have: (mPref m).symm w < s.proposeIndex m := by
        have := proposeIndexIsMonotonic_nextState s_pred_is_pred m
        omega
      simp only [this, iff_true]
      obtain ⟨t, ht, nd, _, t_before_s_pred, m_proposed_w_earlier⟩ := ih
      exists t, ht, nd
      simp [m_proposed_w_earlier]
      have := iterateNextState s_pred_is_pred
      constructor
      · by_contra bad
        rw [bad] at t_before_s_pred
        apply global_decreasing at t_before_s_pred
        apply global_decreasing at this
        have := galeShapleyTerminator.decreasing s_pred
        simp_rw [s_pred_is_pred] at this
        simp only [Option.isSome_some, Option.get_some, true_implies] at this
        omega
      · apply iterateTransitivity
        exact t_before_s_pred
        exact this
    · simp only [h2, iff_false, not_exists, not_and] at ih
      have := proposeIndex_nextState s_pred_is_pred m
      by_cases h3: proposedAtState (nextStateSomeIsNotDone s_pred_is_pred) m w
      · have m_proposed_w := h3
        unfold proposedAtState at h3
        obtain ⟨m_proposer, w_proposee⟩ := h3
        simp [proposee, ← m_proposer,
          (pref_invariant' (initialState mPref wPref) s_pred h_s_pred).1] at w_proposee
        simp [← m_proposer] at this
        rw [Equiv.apply_eq_iff_eq_symm_apply] at w_proposee
        simp only [← w_proposee, this, lt_add_iff_pos_right, zero_lt_one, iff_true]
        exists s_pred, h_s_pred, nextStateSomeIsNotDone s_pred_is_pred
        exact ⟨(iterate_ne_predecessor s_pred_is_pred).symm,
                iterateNextState s_pred_is_pred, m_proposed_w⟩
      · rw [this]
        constructor
        · intro m_proposed_w_earlier
          obtain ⟨t, ht, nd, t_ne_s, t_before_s, m_proposed_w_earlier⟩ := m_proposed_w_earlier
          have t_ne_s_pred: t ≠ s_pred := by
            by_contra bad
            simp_rw [bad] at m_proposed_w_earlier -- changes the type of nd from notDone t to notDone s_pred
            exact h3 m_proposed_w_earlier
          specialize ih t ht nd t_ne_s_pred
            (iterate_ne_s_le_s_pred ht h_s_pred t_ne_s s_pred_is_pred t_before_s)
          exact False.elim (ih m_proposed_w_earlier)
        · split_ifs <;> tauto
          case _ m_proposer =>
          intro propose_ineq
          have: (mPref m).symm w = s_pred.proposeIndex m := by omega
          unfold proposedAtState at h3
          simp [← m_proposer, proposee,
            (pref_invariant' (initialState mPref wPref) s_pred h_s_pred).1, ← this] at h3

lemma proposeIndexInequality (m: M) (w: W):
    proposed mPref wPref m w ↔
    ↑((mPref m).symm w) < (galeShapleyFinalState mPref wPref).proposeIndex m := by
  have := proposeIndexInequality' mPref wPref (galeShapleyFinalState mPref wPref) m w
  unfold proposed
  have finalState: ∀ s ∈ galeShapleyList mPref wPref, galeShapleyFinalState mPref wPref ∈ galeShapleyIterate s := by
    simp_rw [← galeShapleyFinalState_rfl, ← galeShapleyList_rfl]
    intro s hs
    rw [tailLast s hs]
    exact List.getLast_mem (galeShapleyIterateNonEmpty s)
  rw [← this (List.getLast_mem (galeShapleyListNonEmpty mPref wPref))]
  clear this
  constructor
  · intro lhs
    obtain ⟨s, hs, nd, proposed⟩ := lhs
    exists s, hs, nd
    simp [proposed]
    constructor
    · by_contra bad
      rw [bad] at nd
      have := finalStateHasNoNextStep mPref wPref
      apply notDoneIsSome at nd
      rw [this] at nd
      contradiction
    · exact finalState s hs
  · tauto

lemma noMoreProposalsImpliesSingle'' {state: GaleShapleyState M W}
    (unmatched: state.matching m = none) (outOfProposals: state.proposeIndex m = Fintype.card W):
    ∀ s ∈ (galeShapleyIterate state), s.matching m = none ∧ s.proposeIndex m = Fintype.card W := by
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
      simp [iterate_single_state noneStep]
      exact ⟨unmatched, outOfProposals⟩
  | case2 state nextState nextStep ih =>
      simp at nextStep
      simp [iterate_next_state nextStep]
      refine ⟨⟨unmatched, outOfProposals⟩, ?_⟩
      suffices nextState.matching m = none ∧ nextState.proposeIndex m = Fintype.card W by
        exact ih this.1 this.2
      have := noMoreProposalsImpliesSingleNextStep
        (someIsNotDone (by apply Option.isSome_iff_exists.mpr ⟨nextState, nextStep⟩))
        unmatched outOfProposals
      simp [nextStep] at this
      exact this

lemma noMoreProposalsImpliesSingle''' {state: GaleShapleyState M W} (m: M):
    (∃ s ∈ galeShapleyIterate state, s.matching m = none ∧ s.proposeIndex m = Fintype.card W) →
    ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty state)).matching m = none ∧
    ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty state)).proposeIndex m = Fintype.card W := by
  intro s_done
  obtain ⟨s, s_in_list, s_done⟩ := s_done
  rw [tailLast s s_in_list]
  apply noMoreProposalsImpliesSingle'' s_done.1 s_done.2
  exact List.getLast_mem (galeShapleyIterateNonEmpty s)

lemma noMoreProposalsImpliesSingle (m: M): (∃ s ∈ galeShapleyList mPref wPref,
    s.matching m = none ∧ s.proposeIndex m = Fintype.card W) → (galeShapley mPref wPref) m = none := by
  intro m_done_at_some_point
  have := noMoreProposalsImpliesSingle''' m m_done_at_some_point
  exact this.1

lemma changedPartnerMustBecomeSingle {m: M} {w: W} (state: GaleShapleyState M W)
    (origPartner: state.matching m = some w)
    (finalPartner: ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).matching m ≠ some w):
      ∃ s ∈ (galeShapleyIterate state), s.matching m = none := by

  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
    simp [iterate_single_state noneStep] at origPartner finalPartner
    contradiction
  | case2 state nextState nextStep ih =>
    have c1 := iterate_next_state nextStep
    simp at nextStep
    simp [c1, List.getLast_cons (galeShapleyIterateNonEmpty _),
      nextStateLastIsSame nextStep] at finalPartner ⊢
    rcases h: nextState.matching m with _ | w'
    · right
      use nextState
      constructor
      · exact iterateReflexivity _ nextState
      · exact h
    · have := matchedEitherSameOrSingleNext nextStep origPartner
      rcases this with m_single_next | m_still_w'
      · rw [h] at m_single_next
        contradiction
      · rw [h] at m_still_w'
        simp at m_still_w'
        rw [m_still_w'] at h
        specialize ih h finalPartner
        tauto

lemma changedPartnerIncreaseProposeIndex
    (state: GaleShapleyState M W) (m: M) (w: W):
      state.proposeIndex m ≤ ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).proposeIndex m ∧
      (state.matching m ≠ some w →
        ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).matching m = some w →
        state.proposeIndex m < ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).proposeIndex m) := by
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this]
  | case2 state nextState nextStep ih =>
    have nextStepMonotonic := proposeIndexIsMonotonic_nextState nextStep m
    simp [iterate_next_state nextStep] at ih ⊢
    rw [List.getLast_cons (galeShapleyIterateNonEmpty nextState)]
    rw [← nextStateLastIsSame nextStep] at ih ⊢
    obtain ⟨ih_weak, ih_strict⟩ := ih
    constructor
    · omega -- weak inequality is easy
    · intros m_not_matches_w finalPartner
      simp [finalPartner] at ih_strict
      rcases h: state.matching m with _ | w'
      · rcases h2: nextState.matching m with _ | w''
        · specialize ih_strict (by rw [h2]; tauto)
          omega
        · have := becameMatchedIncreasesProposerIndex nextStep h (Option.ne_none_iff_exists'.mpr ⟨w'', h2⟩)
          omega
      · simp [h] at m_not_matches_w
        have sameOrSingle := matchedEitherSameOrSingleNext nextStep h
        rcases sameOrSingle with m_single_next | m_still_w'
        · specialize ih_strict (by rw [m_single_next]; tauto)
          omega
        · specialize ih_strict (by rw [m_still_w']; simpa)
          omega

lemma unchangedPartnerDidntIncreaseProposeIndex {m: M} {w: W}
    {state: GaleShapleyState M W}
    (originalPartner: state.matching m = some w)
    (finalPartner: ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).matching m = some w):
    state.proposeIndex m = ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).proposeIndex m := by
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this]
  | case2 state nextState nextStep ih =>
    simp [finalPartner, ← nextStateLastIsSame nextStep] at ih
    rcases (matchedEitherSameOrSingleNext nextStep originalPartner) with m_single_next | m_still_w
    · have := (changedPartnerIncreaseProposeIndex nextState m w).2
      rw [← nextStateLastIsSame nextStep] at this
      specialize this (by rw [m_single_next]; simp) finalPartner

      have := proposeIndexIsMonotonic_nextState nextStep m
      have: state.proposeIndex m <
        ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).proposeIndex m := by omega
      rw [← state.matchedLastProposed m w originalPartner] at this
      rw [← ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).matchedLastProposed m w
        finalPartner] at this
      simp at this
      rw [(pref_invariant' state ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _))
        (List.getLast_mem (galeShapleyIterateNonEmpty state))).1] at this
      omega
    · specialize ih m_still_w
      rw [← ih]
      exact curMatchedNextStepDidntIncreaseProposeIndex nextStep (by simp [originalPartner])

lemma rejectedEndsUpWithWorse {m: M} {w w': W}
    {state: GaleShapleyState M W}
    (nextStateSome: galeShapleyNextStep state = some nextState')
    (originalPartner: state.matching m = some w)
    (w_rejects_m: nextState'.matching m = none)
    (finalPartner: ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).matching m = some w'):
    (state.mPref m).symm w < (state.mPref m).symm w' := by
  have origProposeIndex := state.matchedLastProposed m w originalPartner
  have finalProposeIndex := ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).matchedLastProposed
     m w' finalPartner
  rw [(pref_invariant' state ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _))
    (List.getLast_mem (galeShapleyIterateNonEmpty _))).1] at finalProposeIndex
  suffices state.proposeIndex m < ((galeShapleyIterate state).getLast (galeShapleyIterateNonEmpty _)).proposeIndex m by omega

  induction state using (iterate.induct galeShapleyTerminator) with
    | case1 state noneStep =>
      simp at noneStep
      rw [noneStep] at nextStateSome
      contradiction
    | case2 state nextState nextStep _ =>
      simp at nextStep
      simp [nextStep] at nextStateSome
      rw [← nextStateSome] at w_rejects_m
      have := changedPartnerIncreaseProposeIndex nextState m
      simp [iterate_next_state nextStep] at finalPartner ⊢
      rw [List.getLast_cons (galeShapleyIterateNonEmpty _)] at finalPartner ⊢
      rw [← nextStateLastIsSame nextStep] at this finalPartner ⊢
      specialize this w'
      obtain ⟨_, this⟩ := this
      simp [w_rejects_m, finalPartner] at this
      suffices state.proposeIndex m ≤ nextState.proposeIndex m by omega
      exact proposeIndexIsMonotonic_nextState nextStep m

lemma matchedNeverRejectedImpliesFinalMatch {state: GaleShapleyState M W}:
    state.matching m = some w → neverRejectedFromState state m w →
    ((galeShapleyIterate state).getLast
      (galeShapleyIterateNonEmpty _)).matching m = some w := by
  intros m_matches_w never_rejected
  unfold neverRejectedFromState at never_rejected
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this]
    exact m_matches_w
  | case2 state nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp_rw [this] at ih never_rejected ⊢
    simp [List.getLast_cons (galeShapleyIterateNonEmpty _)] at ih never_rejected ⊢
    rw [← nextStateLastIsSame nextStep] at ih ⊢
    rcases never_rejected with ⟨not_rejected_now, never_rejected_later⟩
    specialize not_rejected_now (nextStateSomeIsNotDone nextStep)
    unfold rejectedAtState at not_rejected_now
    rcases (matchedEitherSameOrSingleNext nextStep m_matches_w) with m_single | m_still_w
    · have := becameSingleImpliesRejected nextStep (by rw [m_matches_w]; simp) m_single
      simp [this.1] at m_matches_w
      tauto
    · specialize ih m_still_w
      apply ih
      exact never_rejected_later

lemma proposedNeverRejectedImpliesFinalMatch {state: GaleShapleyState M W} (h: notDone state):
    proposedAtState h m w → neverRejectedFromState state m w →
    ((galeShapleyIterate state).getLast
      (galeShapleyIterateNonEmpty _)).matching m = some w := by
  induction state using (iterate.induct galeShapleyTerminator) with
  | case1 state noneStep =>
    simp at noneStep
    apply notDoneIsSome at h
    rw [noneStep] at h
    simp at h
  | case2 state nextState nextStep _ =>
    unfold proposedAtState neverRejectedFromState
    simp_rw [iterate_next_state nextStep]
    simp [List.getLast_cons (galeShapleyIterateNonEmpty _)]

    intros m_proposer w_proposee not_rejected_now
    specialize not_rejected_now h
    intro never_rejected_later
    apply matchedNeverRejectedImpliesFinalMatch ?_ (by
      unfold neverRejectedFromState
      exact never_rejected_later
    )

    have := matching_nextState nextStep m
    simp [← m_proposer, w_proposee] at this
    unfold rejectedAtState at not_rejected_now
    push_neg at not_rejected_now
    specialize not_rejected_now w_proposee
    rw [this]
    split_ifs <;> try rfl
    case _ m_not_newMatch =>
    have := newMatch_choices h
    rw [← m_proposer] at this
    rcases this <;> try tauto
    case _ cur_eq_new =>
    unfold rejectee at not_rejected_now
    simp [← m_proposer, ← cur_eq_new] at not_rejected_now

lemma singleImpliesRejectedByAll (m_single: galeShapley mPref wPref m = none):
    ∀ w, ∃ state ∈ galeShapleyList mPref wPref, ∃ (h: notDone state),
        rejectedAtState h m w := by
  by_contra bad
  push_neg at bad
  obtain ⟨w, w_never_rejected'⟩ := bad
  have w_never_rejected: neverRejectedFromState (initialState mPref wPref) m w := by
    unfold neverRejectedFromState
    unfold galeShapleyList at w_never_rejected'
    exact w_never_rejected'
  have m_final_proposeIndex := unmatchedExhaustedProposals mPref wPref m m_single
  have := proposeIndexInequality mPref wPref m w
  simp [m_final_proposeIndex] at this
  unfold proposed at this
  obtain ⟨s, hs, nd, m_proposed_w⟩ := this
  have := proposedNeverRejectedImpliesFinalMatch nd m_proposed_w (neverRejectedFuture w_never_rejected s hs)
  rw [← tailLast s hs] at this
  simp at this
  rw [this] at m_single
  contradiction

lemma matchedImpliesProposedEarlier {state: GaleShapleyState M W}
    (h_state: state ∈ galeShapleyList mPref wPref)
    (matched: state.matching m = some w):
    ∃ s ∈ galeShapleyList mPref wPref, ∃ (nd_s: notDone s),
      s ≠ state ∧ state ∈ galeShapleyIterate s ∧ proposedAtState nd_s m w := by
  have := state.matchedLastProposed m w matched
  simp [(pref_invariant' (initialState mPref wPref) state h_state).1] at this
  have: (mPref m).symm w < state.proposeIndex m := by omega
  rw [← proposeIndexInequality'] at this <;> try assumption

lemma rejectedByPreferred {state: GaleShapleyState M W}
    (h_state: state ∈ galeShapleyList mPref wPref) (m: M):
    let k: Nat := match (state.matching m) with
             | none => state.proposeIndex m
             | some w => (mPref m).symm w
    ∀ w', ↑((mPref m).symm w') < k →
    ∃ s ∈ galeShapleyList mPref wPref, ∃ (nd_s: notDone s),
      state ∈ galeShapleyIterate s ∧ s ≠ state ∧ rejectedAtState nd_s m w' := by
  revert h_state
  apply stateStrongInduction galeShapleyTerminator (initialState mPref wPref)
  simp
  intros s hs ih w' m_prefers_w'

  by_cases h: s = initialState mPref wPref
  -- trivial case where s = initial state
  simp [h] at m_prefers_w'

  -- s ≠ initial state
  have s_pred := iterate_predecessor hs h
  obtain ⟨s_pred, ⟨h_s_pred, s_pred_is_pred⟩, s_pred_uniq⟩ := s_pred
  clear s_pred_uniq
  specialize ih s_pred h_s_pred (iterate_ne_predecessor s_pred_is_pred)
            (iterateNextState s_pred_is_pred) w'
  have s_proposeIndex := proposeIndex_nextState s_pred_is_pred m
  by_cases h:
    ↑((mPref m).symm w') <
    ((match s_pred.matching m with
    | none => s_pred.proposeIndex m
    | some w => ↑((mPref m).symm w)): Nat)
  · -- the case in which ih is applicable
    specialize ih h
    obtain ⟨rejection_state, h_rjs, s_before_s_pred, s_ne_s_pred, nd_rjs, rejected_s⟩ := ih
    refine ⟨rejection_state, h_rjs, ?_, ?_, nd_rjs, rejected_s⟩
    · apply iterateTransitivity
      exact s_before_s_pred
      exact iterateNextState s_pred_is_pred
    · by_contra bad
      rw [bad] at s_before_s_pred
      apply global_decreasing at s_before_s_pred
      have := galeShapleyTerminator.decreasing s_pred (by rw [s_pred_is_pred]; simp)
      simp_rw [s_pred_is_pred] at this
      simp only [Option.get_some] at this
      omega
  · clear ih -- since it's no longer applicable
    rcases h2: s_pred.matching m with _ | w
    · rcases h3: s.matching m with _ | w <;> simp [h2, h3] at m_prefers_w' h
      · split_ifs at s_proposeIndex
        · case _ m_proposed =>
          rw [s_proposeIndex] at m_prefers_w'
          have: s_pred.proposeIndex m = ↑((mPref m).symm w') := by omega
          refine ⟨s_pred, h_s_pred, (iterateNextState s_pred_is_pred),
            (by push_neg; symm; exact iterate_ne_predecessor s_pred_is_pred),
            nextStateSomeIsNotDone s_pred_is_pred, ?_⟩
          have w'_proposee: proposee (nextStateSomeIsNotDone s_pred_is_pred) = w' := by
            unfold proposee
            simp [← m_proposed, this, (pref_invariant' (initialState mPref wPref) s_pred h_s_pred).1]
          have := proposerRemainsSingleImpliesRejected s_pred_is_pred m_proposed h3
          unfold rejectedAtState
          tauto
        · case _ m_not_proposed =>
          rw [s_proposeIndex] at m_prefers_w'
          omega
      · have m_proposed := becameMatchedIsProposer (nextStateSomeIsNotDone s_pred_is_pred)
            h2 (by simp at s_pred_is_pred; simp [s_pred_is_pred, h3])
        have w_proposee := becameMatchedProposedTo (w := w) (nextStateSomeIsNotDone s_pred_is_pred)
            h2 (by simp at s_pred_is_pred; simp [s_pred_is_pred, h3])
        have := matching_nextState s_pred_is_pred m
        simp [← m_proposed, w_proposee, h2, h3] at this
        split_ifs at this; try contradiction
        case _ m_eq_newMatch =>
        have := s.matchedLastProposed m w h3
        simp [(pref_invariant' (initialState mPref wPref) s hs).1] at this
        simp [← m_proposed] at s_proposeIndex
        omega
    · rcases h3: s.matching m with _ | w2 <;> simp [h2, h3] at m_prefers_w' h
      · have m_no_propose := didNotPropose (nextStateSomeIsNotDone s_pred_is_pred) (by rw [h2]; simp)
        simp [m_no_propose] at s_proposeIndex
        have := s_pred.matchedLastProposed m w h2
        simp [(pref_invariant' (initialState mPref wPref) s_pred h_s_pred).1] at this
        have: w' = w := by
          have: (mPref m).symm w' = (mPref m).symm w := by omega
          exact Equiv.injective (mPref m).symm this
        rw [this]
        refine ⟨s_pred, h_s_pred, (iterateNextState s_pred_is_pred),
            (by push_neg; symm; exact iterate_ne_predecessor s_pred_is_pred),
            nextStateSomeIsNotDone s_pred_is_pred, ?_⟩
        have := becameSingleImpliesRejected s_pred_is_pred (by
          rw [Option.ne_none_iff_exists']
          use w
        ) h3
        unfold rejectedAtState
        rw [h2] at this
        simp at this
        tauto
      · have := matchedEitherSameOrSingleNext s_pred_is_pred h2
        simp [h3] at this
        rw [this] at m_prefers_w'
        omega

lemma singleImpliesRejectedByPreferred {state: GaleShapleyState M W} {m: M}
    (h_state: state ∈ galeShapleyList mPref wPref) (single: state.matching m = none):
    ∀ w', (mPref m).symm w' < state.proposeIndex m →
    ∃ s ∈ galeShapleyList mPref wPref, ∃ (nd_s: notDone s),
      state ∈ galeShapleyIterate s ∧ s ≠ state ∧ rejectedAtState nd_s m w' := by
  have := rejectedByPreferred mPref wPref h_state m
  simp only [single] at this
  exact this

lemma matchedImpliesRejectedByPreferred {state: GaleShapleyState M W} {w: W}
    (h_state: state ∈ galeShapleyList mPref wPref) (matched: state.matching m = some w):
    ∀ w', (mPref m).symm w' < (mPref m).symm w →
    ∃ s ∈ galeShapleyList mPref wPref, ∃ (nd_s: notDone s),
      state ∈ galeShapleyIterate s ∧ s ≠ state ∧ rejectedAtState nd_s m w' := by
  have := rejectedByPreferred mPref wPref h_state m
  simp only [matched] at this
  exact this

lemma proposedImpliesRejectedByPreferred {state: GaleShapleyState M W} {w: W} (nd: notDone state)
    (h_state: state ∈ galeShapleyList mPref wPref) (proposed: proposedAtState nd m w):
    ∀ w', (mPref m).symm w' < (mPref m).symm w →
    ∃ s ∈ galeShapleyList mPref wPref, ∃ (nd_s: notDone s),
      state ∈ galeShapleyIterate s ∧ s ≠ state ∧ rejectedAtState nd_s m w' := by
  unfold proposedAtState proposee at proposed
  obtain ⟨m_proposer, w_proposee⟩ := proposed
  have := choose_spec nd
  simp_rw [← m_proposer] at this w_proposee
  have := singleImpliesRejectedByPreferred mPref wPref h_state this.1
  simp [(pref_invariant' (initialState mPref wPref) state h_state).1] at w_proposee
  rw [Equiv.apply_eq_iff_eq_symm_apply] at w_proposee
  apply_fun (fun x => x.val) at w_proposee
  simp at w_proposee
  rw [w_proposee] at this
  exact this
