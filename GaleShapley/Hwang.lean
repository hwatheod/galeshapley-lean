import GaleShapley.Basic
import GaleShapley.Lemmas

/-!

  # Hwang's theorem

  In this file, we prove Hwang's theorem following section 1.5 of Dumont's paper.

  Fix a set of preferences P for M and W. Let gs(P) denote the matching produced
  by the Gale-Shapley algorithm, and let A be an arbitrary matching.

  We say that m in M is a *revendicateur* (with respect to A) if m prefers his
  partner in A to his partner in gs(P).  We denote by R(A) the set of
  revendicateurs.

  Hwang's theorem: If R(A) is non-empty, then there exists a non-revendicateur
  m in M and w in W such that w is the A-partner of a revendicateur, and (m,w)
  form an unstable pair with respect to A.

-/
namespace GaleShapley

universe u
lemma set_ext (α: Type u) {P Q : α → Prop}: {x | P x} = {x | Q x} ↔ ∀ x, P x ↔ Q x := by
  exact Set.ext_iff

open Classical GaleShapley.Iterate
noncomputable section

variable {M W: Type} [Fintype M] [Fintype W]
  (mPref: Pref M W)
  (wPref: Pref W M)

def revendicateur (matching: Matching M W) (m : M): Prop :=
    ∃ w, matching m = some w ∧
      (∀ w', (galeShapley mPref wPref) m = some w' → (mPref m).symm w < (mPref m).symm w')

def revendicateurSpouses (matching: Matching M W): Finset W :=
  {w | ∃ m, revendicateur mPref wPref matching m ∧ matching m = some w}.toFinset

/- The first paragraph of the proof in Dumont. -/
lemma revSpousesMarriedInGs (matching: Matching M W):
    ∀ (w: revendicateurSpouses mPref wPref matching), inverseMatching (galeShapley mPref wPref) w ≠ none := by
  intro w
  by_contra bad
  have := Subtype.prop w
  simp [revendicateurSpouses] at this
  obtain ⟨m, m_rev, m_matches_w⟩ := this
  unfold revendicateur at m_rev
  obtain ⟨w', m_matches_w', m_rev⟩ := m_rev
  have: w' = w := matchingCondition'' m_matches_w' m_matches_w
  rw [this] at m_rev
  clear w' m_matches_w' this
  suffices isUnstablePair mPref wPref (galeShapley mPref wPref) m w by
    apply galeShapleyNoUnstablePair mPref wPref this
  unfold isUnstablePair
  simp [bad]
  rcases h: galeShapley mPref wPref m with _ | w'
  · tauto
  · simp
    exact m_rev w' h

/- The second paragraph of the proof in Dumont, which proves the theorem under the additional
   hypothesis below. -/
def hwang_case1_hypothesis (matching: Matching M W): Prop :=
  ∃ (w: revendicateurSpouses mPref wPref matching), ∃ (m : M),
       ¬ (revendicateur mPref wPref matching m) ∧ (galeShapley mPref wPref) m = some w

theorem hwangTheorem_case1 (matching: Matching M W) (h: hwang_case1_hypothesis mPref wPref matching):
    ∃ m, ∃ m', ∃ w, matching m = some w ∧ (revendicateur mPref wPref matching m) ∧
      ¬ (revendicateur mPref wPref matching m') ∧ isUnstablePair mPref wPref matching m' w := by
  unfold hwang_case1_hypothesis at h
  simp at h
  obtain ⟨w, w_revSpouse, m', m'_nonrev, m'_gs_matches_w⟩ := h
  simp [revendicateurSpouses] at w_revSpouse
  obtain ⟨m, m_rev, m_matches_w⟩ := w_revSpouse
  use m
  use m'
  use w
  simp [m_matches_w, m_rev, m'_nonrev]
  have m_ne_m': m ≠ m' := by
    by_contra bad
    rw [bad] at m_rev
    contradiction
  unfold isUnstablePair
  simp [m_matches_w, (inverseProperty matching m w).mp m_matches_w]
  simp [revendicateur] at m'_nonrev m_rev
  obtain ⟨w', h1, m_rev⟩ := m_rev
  have: w = w' := by
    rw [h1] at m_matches_w
    simp at m_matches_w
    exact m_matches_w.symm
  rw [← this] at m_rev
  clear this h1 w'
  constructor
  · rcases h1: matching m' with _ | w'
    constructor
    · simp
    · simp
      specialize m'_nonrev w' h1
      obtain ⟨w'', m'_gs_matches_w'', m'_weak_prefers_w⟩ := m'_nonrev
      have: w = w'' := by
        rw [m'_gs_matches_w] at m'_gs_matches_w''
        simp at m'_gs_matches_w''
        exact m'_gs_matches_w''
      rw [← this] at m'_weak_prefers_w
      clear this m'_gs_matches_w''
      have w_ne_w': w ≠ w' := by
        by_contra bad
        rw [← bad] at h1
        have := matchingCondition' m_matches_w h1
        contradiction
      have: (mPref m').symm w ≠ (mPref m').symm w' := by
        apply Function.Injective.ne
        apply Equiv.injective
        exact w_ne_w'
      omega
  · by_contra w_weakprefers_m
    push_neg at w_weakprefers_m
    have: (wPref w).symm m ≠ (wPref w).symm m' := by
      apply Function.Injective.ne
      apply Equiv.injective
      exact m_ne_m'
    have w_prefers_m: (wPref w).symm m < (wPref w).symm m' := by omega
    clear w_weakprefers_m this
    suffices isUnstablePair mPref wPref (galeShapley mPref wPref) m w by
      exact galeShapleyNoUnstablePair mPref wPref this
    unfold isUnstablePair
    simp [m'_gs_matches_w, (inverseProperty _ m' w).mp m'_gs_matches_w]
    constructor
    · rcases h2: (galeShapley mPref wPref) m with _ | w'
      · simp
      · specialize m_rev w' h2
        simp
        exact m_rev
    · exact w_prefers_m

/- The rest of the proof assumes the negation of `hwang_case1_hypothesis`.

   The next several lemmas establish the cardinality arguments needed for the
   third paragraph of the proof in Dumont.
-/
lemma revendicateurSpouses_matching_cardinality
    (hR: R = { m | revendicateur mPref wPref matching m}.toFinset)
    (hS: S = revendicateurSpouses mPref wPref matching):
    R.card = S.card := by
  apply matching_equal_cardinality matching
  intro r
  have := Subtype.prop r
  simp [hR] at this
  unfold revendicateur at this
  tauto

  unfold revendicateurSpouses at hS
  rw [hS]
  congr!
  rw [hR]
  simp

lemma revendicateurSpouses_gs_cardinality
    (hS': S' = { w | ∃ m, revendicateur mPref wPref matching m ∧
      galeShapley mPref wPref m = some w}.toFinset)
    (hR': R' = { r: M | revendicateur mPref wPref matching r ∧
      galeShapley mPref wPref r ≠ none }.toFinset): R'.card = S'.card := by

  apply matching_equal_cardinality (galeShapley mPref wPref) R'
  intro r
  have := Subtype.prop r
  simp [hR'] at this
  obtain ⟨_, r_gs_married⟩ := this
  apply Option.ne_none_iff_exists.mp at r_gs_married
  obtain ⟨w, r_gs_matches_w⟩ := r_gs_married
  use w
  exact r_gs_matches_w.symm

  rw [hS']
  congr! with w
  rw [hR']
  simp
  constructor
  · intro w_gs_married
    obtain ⟨m, m_rev, m_gs_matches_w⟩ := w_gs_married
    use m
    refine ⟨⟨m_rev, ?_⟩, m_gs_matches_w⟩
    by_contra bad
    rw [bad] at m_gs_matches_w
    contradiction
  · tauto

/- The third paragraph of the proof in Dumont, which shows that the negation of
   `hwang_case1_hypothesis` implies that the set of revendicateur spouses in
   `galeShapley` and in `matching` are the same.
-/
def both_same_spouses_hypothesis (matching: Matching M W) := ∀ (w: W),
        (∃ m, revendicateur mPref wPref matching m ∧ galeShapley mPref wPref m = some w) ↔
        (∃ m, revendicateur mPref wPref matching m ∧ matching m = some w)

lemma neg_hwang_case1_lemma: ¬ (hwang_case1_hypothesis mPref wPref matching) →
    both_same_spouses_hypothesis mPref wPref matching := by
  intro neg_hwang_case1
  unfold hwang_case1_hypothesis at neg_hwang_case1
  set_option push_neg.use_distrib true in push_neg at neg_hwang_case1
  simp at neg_hwang_case1
  unfold both_same_spouses_hypothesis

  let S' := { w | (∃ m, revendicateur mPref wPref matching m ∧ galeShapley mPref wPref m = some w) }.toFinset
  let S := { w | ∃ m, revendicateur mPref wPref matching m ∧ matching m = some w}.toFinset
  suffices S = S' by (
    simp only [S, S'] at this
    apply_fun (fun x => x.toSet) at this
    simp at this
    apply (set_ext W).mp
    exact this.symm
  )
  simp [revendicateurSpouses] at neg_hwang_case1
  have s_sub_s': S ⊆ S' := by
    simp only [S, S']
    intro w mw
    simp at mw ⊢
    specialize neg_hwang_case1 w
    obtain ⟨m, m_rev, m_matches_w⟩ := mw
    specialize neg_hwang_case1 m m_rev m_matches_w
    have := revSpousesMarriedInGs mPref wPref matching
    simp [revendicateurSpouses] at this
    specialize this w m m_rev m_matches_w
    apply Option.ne_none_iff_exists.mp at this
    obtain ⟨m', w_gs_matches_m'⟩ := this
    have := (inverseProperty (galeShapley mPref wPref) m' w).mpr w_gs_matches_m'.symm
    specialize neg_hwang_case1 m'
    simp [this] at neg_hwang_case1
    use m'

  suffices S.card ≥ S'.card by (
    apply (Finset.subset_iff_eq_of_card_le _).mp
    exact s_sub_s'
    omega
  )

  let R := { m | revendicateur mPref wPref matching m}.toFinset
  have rs: R.card = S.card := by
    apply revendicateurSpouses_matching_cardinality mPref wPref (by rfl)
    simp [revendicateurSpouses, S]

  have s'_le_r: S'.card ≤ R.card := by
    suffices ∃ f: S' → R, Function.Injective f by
      obtain ⟨f, f_inj⟩ := this
      have rcard: Fintype.card R = R.card := by exact Fintype.card_coe R
      have s'card: Fintype.card S' = S'.card := by exact Fintype.card_coe S'
      rw [← rcard, ← s'card]
      exact Fintype.card_le_of_injective f f_inj
    have: ∀ (w : S'), ∃ m, revendicateur mPref wPref matching m ∧ galeShapley mPref wPref m = some w := by simp [S']
    choose f hf using this
    simp at hf
    let f_restrict := Set.codRestrict f R (by {
      intro s'
      specialize hf s' (Subtype.mem s')
      simp [R]
      exact hf.1
    })
    use f_restrict
    intros s1 s2 s1_eq_s2
    have ⟨_, hf1⟩ := hf s1 (Subtype.mem s1)
    have ⟨_, hf2⟩ := hf s2 (Subtype.mem s2)
    simp [f_restrict, Set.codRestrict] at s1_eq_s2
    rw [s1_eq_s2] at hf1
    have := matchingCondition'' hf1 hf2
    exact SetCoe.ext this
  omega

/- An auxillary lemma stating that all revendicateurs are married in `galeShapley` (under the
   `both_same_spouses_hypothesis` which follows from the negation of `hwang_case1_hypothesis).
 -/
lemma all_revendicateurs_gs_married_lemma (matching: Matching M W):
    both_same_spouses_hypothesis mPref wPref matching →
    ∀ (m: M),
        revendicateur mPref wPref matching m → galeShapley mPref wPref m ≠ none := by
  let R := { m | revendicateur mPref wPref matching m}.toFinset
  let R' := { r: M | revendicateur mPref wPref matching r ∧ galeShapley mPref wPref r ≠ none }.toFinset
  intro both_same_spouses
  suffices eq: R' = R by
    intro r r_rev
    have: r ∈ R := by simpa [R]
    rw [← eq] at this
    simp [R'] at this
    exact this.2
  have subset: R' ⊆ R := by
    intros r' hr'
    simp [R'] at hr'
    simp [R]
    tauto

  suffices R'.card = R.card by exact Finset.eq_of_subset_of_card_le subset (by omega)

  /-
    |R| = |rev_spouse(R)| = |gs_spouse(R)| = |R'|
  -/
  let S := revendicateurSpouses mPref wPref matching
  have rs: R.card = S.card := by
    exact revendicateurSpouses_matching_cardinality mPref wPref (by rfl) (by rfl)

  let S' := { w | ∃ m, revendicateur mPref wPref matching m ∧ galeShapley mPref wPref m = some w}.toFinset

  have ss'_eq: S = S' := by
    simp [revendicateurSpouses, S, S']
    congr
    apply funext
    intro x
    unfold both_same_spouses_hypothesis at both_same_spouses
    rw [both_same_spouses x]

  have ss': S.card = S'.card := by
    apply_fun (fun x => x.card) at ss'_eq
    exact ss'_eq

  have s'r': S'.card = R'.card := by
    exact (revendicateurSpouses_gs_cardinality mPref wPref (by rfl) (by rfl)).symm

  rw [← ss', ← rs] at s'r'
  exact s'r'.symm

/- We follow the rest of the proof in Dumont, starting with the fourth paragraph. -/
theorem hwangTheorem (matching: Matching M W) (existsRevendicateur: ∃ m, revendicateur mPref wPref matching m):
    ∃ m, ∃ m', ∃ w, matching m = some w ∧ (revendicateur mPref wPref matching m) ∧
      ¬ (revendicateur mPref wPref matching m') ∧ isUnstablePair mPref wPref matching m' w := by
  by_cases h: hwang_case1_hypothesis mPref wPref matching
  · exact hwangTheorem_case1 mPref wPref matching h
  · have both_same_spouses: both_same_spouses_hypothesis mPref wPref matching := by
      exact neg_hwang_case1_lemma mPref wPref h
    have all_revendicateurs_gs_married: ∀ (m: M),
        revendicateur mPref wPref matching m → galeShapley mPref wPref m ≠ none := by
      exact all_revendicateurs_gs_married_lemma mPref wPref matching both_same_spouses

    -- Let r be the last revendicateur who made a proposal
    let gsList := galeShapleyList mPref wPref
    have exists_last_rev_proposal := last_occurrence
        (fun (state: GaleShapleyState M W) => ∃ r, revendicateur mPref wPref matching r ∧ state.matching r = none )
        (by
          use (gsList.head (galeShapleyListNonEmpty mPref wPref))
          constructor
          · exact List.head_mem (galeShapleyListNonEmpty mPref wPref)
          · simp [gsList]
            exact existsRevendicateur
    )
    simp at exists_last_rev_proposal

    let last_rev_proposal := choose exists_last_rev_proposal
    have last_rev_proposal_property := choose_spec exists_last_rev_proposal
    have last_rev_proposal_rfl: last_rev_proposal = choose exists_last_rev_proposal := by rfl
    rw [← last_rev_proposal_rfl] at last_rev_proposal_property
    rcases last_rev_proposal_property with ⟨h_lrp, ⟨r, r_rev, r_unmatched⟩, tail_condition⟩

    have pref_inv: last_rev_proposal.mPref = mPref ∧
        last_rev_proposal.wPref = wPref := by
      apply pref_invariant' (initialState mPref wPref)
      exact h_lrp

    -- this wasn't the last step of the algorithm
    have notLast: notDone last_rev_proposal := by
      by_contra bad
      unfold notDone at bad
      push_neg at bad
      specialize bad r r_unmatched
      simp at bad
      have := noMoreProposalsImpliesSingle mPref wPref r ⟨last_rev_proposal, h_lrp, r_unmatched, bad⟩
      exact all_revendicateurs_gs_married r r_rev this

    let nextState := (galeShapleyNextStep last_rev_proposal).get (notDoneIsSome notLast)
    have nextStep: galeShapleyNextStep last_rev_proposal = some nextState := by
      unfold_let nextState
      exact Option.eq_some_of_isSome (notDoneIsSome notLast)
    have nextState_ne: nextState ≠ last_rev_proposal := iterate_ne_predecessor (by
      rw [← galeShapleyTerminatorNextStep] at nextStep
      exact nextStep
    )
    have tail_condition_nextState :=
      tail_condition nextState (iterateNextState nextStep) nextState_ne
    have h_nextState: nextState ∈ galeShapleyList mPref wPref := by
      apply iterateTransitivity
      exact h_lrp
      exact iterateNextState (step := galeShapleyTerminator) nextStep
    have ne_last_rev_proposal {s: GaleShapleyState M W}
        (h: s ∈ galeShapleyIterate nextState): s ≠ last_rev_proposal := by
      by_contra bad
      rw [bad] at h
      have := iterateAntisymmetry h_nextState h_lrp h (iterateNextState nextStep)
      exact iterate_ne_predecessor (step := galeShapleyTerminator) nextStep this

    -- let w be r's match at the next step of the algorithm
    let w := Option.get (nextState.matching r) (by
      specialize tail_condition_nextState r r_rev
      exact Option.ne_none_iff_isSome.mp tail_condition_nextState
    )

    have w_rfl: nextState.matching r = some w := by simp [w]

    -- r was the proposer
    have r_proposer: choose notLast = r := by
      symm
      apply becameMatchedIsProposer notLast r_unmatched
      simp_rw [nextStep]
      simp
      exact Option.ne_none_iff_exists'.mpr ⟨w, w_rfl⟩

    -- r proposed to w
    have r_proposed_to_w: proposee notLast = w := by
      have := becameMatchedProposedTo (w := w) notLast r_unmatched
      simp_rw [nextStep] at this
      specialize this w_rfl
      exact this

    -- w is the spouse of r in GS
    have r_gs_matches_w: galeShapley mPref wPref r = some w := by
      by_contra bad
      have changed_partner := changedPartnerMustBecomeSingle nextState w_rfl (by
        rw [← nextStateLastIsSame nextStep, ← tailLast last_rev_proposal h_lrp]
        simpa
      )
      obtain ⟨s, hs⟩ := changed_partner
      refine tail_condition s ?_ (ne_last_rev_proposal hs.1) r r_rev hs.2

      apply iterateTransitivity
      exact iterateNextState nextStep
      exact hs.1

    -- w is the spouse of some revendicateur r' ≠ r in matching
    have: ∃ r', revendicateur mPref wPref matching r' ∧ matching r' = some w := by
      exact (both_same_spouses w).mp ⟨r, r_rev, r_gs_matches_w⟩
    obtain ⟨r', r'_rev, r'_matches_w⟩ := this
    have r'_ne_r: r' ≠ r := by
      by_contra r'_eq_r
      rw [r'_eq_r] at r'_matches_w
      unfold revendicateur at r_rev
      obtain ⟨w', r_matches_w', h1⟩ := r_rev
      have: w' = w := matchingCondition'' r_matches_w' r'_matches_w
      rw [this] at h1
      specialize h1 w r_gs_matches_w
      omega

    -- Let w' be the spouse of r' in GS
    have: ∃ w', galeShapley mPref wPref r' = some w' := by
      have := all_revendicateurs_gs_married r' r'_rev
      rcases h1: galeShapley mPref wPref r'
      · contradiction
      · tauto
    obtain ⟨w', r'_gs_matches_w'⟩ := this

    /- since r' is a revendicateur, r' prefers w to w'. -/
    have r'_prefers_w_to_w': (mPref r').symm w < (mPref r').symm w' := by
      unfold revendicateur at r'_rev
      obtain ⟨w'', r'_matches_w'', r'_rev⟩ := r'_rev
      have: w'' = w := matchingCondition'' r'_matches_w'' r'_matches_w
      rw [this] at r'_rev
      exact r'_rev w' r'_gs_matches_w'

    /- Therefore r' proposed to w before ending up with w'. -/
    have r'_proposed_w: (mPref r').symm w < (galeShapleyFinalState mPref wPref).proposeIndex r' := by
      have r'_proposeIndex_w' := (galeShapleyFinalState mPref wPref).matchedLastProposed r' w' r'_gs_matches_w'
      simp at r'_proposeIndex_w'
      omega

    have lastInvariant := tailLast last_rev_proposal h_lrp

    /- Since r' ends up with w', his proposal to w' is his final proposal. -/
    have r'_final_proposeIndex: (galeShapleyFinalState mPref wPref).proposeIndex r' = last_rev_proposal.proposeIndex r' := by
      have r'_gs_matched_w'': ∃ w'', last_rev_proposal.matching r' = some w'' := by
        by_contra bad
        rw [← Option.ne_none_iff_exists'] at bad
        push_neg at bad
        have r_matched_next := tail_condition_nextState r r_rev
        have r'_matched_next := tail_condition_nextState r' r'_rev
        have: r' = r := by
          refine onlyOneCanBecomeMatched notLast bad ?r' r_unmatched ?r <;> (
            simp_rw [nextStep]
            simpa
          )
        exact r'_ne_r this
      obtain ⟨w'', r'_gs_matched_w''⟩ := r'_gs_matched_w''
      have: w' = w'' := by
        by_contra bad
        have := changedPartnerMustBecomeSingle last_rev_proposal r'_gs_matched_w''
        rw [← tailLast last_rev_proposal h_lrp] at this
        simp [r'_gs_matches_w'] at this
        specialize this bad
        obtain ⟨s, ⟨s_in_suffix, r'_nomatch_in_s⟩⟩ := this
        rw [iterate_next_state nextStep] at s_in_suffix
        simp at s_in_suffix
        rcases s_in_suffix with s_head | s_tail
        · rw [s_head] at r'_nomatch_in_s
          rw [r'_nomatch_in_s] at r'_gs_matched_w''
          contradiction
        · refine tail_condition s ?_ (ne_last_rev_proposal s_tail) r' r'_rev r'_nomatch_in_s
          apply iterateTransitivity
          exact iterateNextState nextStep
          exact s_tail


      rw [← this] at r'_gs_matched_w''

      have := unchangedPartnerDidntIncreaseProposeIndex r'_gs_matched_w'' (by
          rw [← lastInvariant]
          exact r'_gs_matches_w'
        )
      rw [← lastInvariant] at this
      exact this.symm

    /- Both r and r' proposed to w during the algorithm.
       Since r made the last revendicateur proposal, r' proposed to w before r did.
       Therefore, at the time r proposed to w, w had a match. Let m be this match.
    -/
    have: ∃ m, last_rev_proposal.matching m = some w := by
      rw [r'_final_proposeIndex] at r'_proposed_w
      have := last_rev_proposal.noWorseThanProposedTo r' w
      rw [pref_inv.1, pref_inv.2] at this
      specialize this r'_proposed_w
      obtain ⟨m', w_inverse_matches_m', _⟩ := this
      use m'
      exact (inverseProperty last_rev_proposal.matching m' w).mpr w_inverse_matches_m'

    obtain ⟨m, w_penultimate_gs_match_m⟩ := this
    have m_matched_w := (inverseProperty last_rev_proposal.matching m w).mp w_penultimate_gs_match_m

    /- We show that m is not a revendicateur. -/
    have m_ne_r: m ≠ r := by
      by_contra bad
      rw [bad] at w_penultimate_gs_match_m
      rw [w_penultimate_gs_match_m] at r_unmatched
      contradiction

    have w_prefers_r_to_m: (wPref w).symm r < (wPref w).symm m := by
      have := matching_nextState' notLast r
      simp_rw [nextStep] at this
      simp [m_ne_r, m_matched_w, pref_inv.1, pref_inv.2, r_proposer, r_proposed_to_w, w_rfl] at this
      split_ifs at this
      · case _ c1 =>
          simp [newMatch, curMatch, m_matched_w, pref_inv.2, r_proposer, r_proposed_to_w] at c1
          split_ifs at c1
          · by_contra bad
            have: (wPref w).symm r = (wPref w).symm m := by omega
            exact m_ne_r.symm ((wPref w).symm.injective this)
          · exact False.elim (m_ne_r c1.symm)

    have m_unmatched_next: nextState.matching m = none := by
      have := matching_nextState' notLast m
      simp_rw [nextStep] at this
      simp [pref_inv.1, pref_inv.2, r_proposer, r_proposed_to_w, m_matched_w, newMatch, curMatch,
        show (wPref w).symm r ≤ (wPref w).symm m by omega, m_ne_r] at this
      exact this

    have m_notrev: ¬ (revendicateur mPref wPref matching m) := by
      by_contra bad
      rcases h: (galeShapley mPref wPref) m with _ | w''
      · have := all_revendicateurs_gs_married m bad
        contradiction
      · exact tail_condition_nextState m bad m_unmatched_next

    /- Show that (m, w) is the unstable pair we are looking for. Note that w is the spouse
       in `matching` of the revendicateur r'. -/
    use r'
    use m
    use w
    refine ⟨r'_matches_w, r'_rev, m_notrev, ?_⟩

    unfold isUnstablePair
    constructor
    · rcases h: matching m with _ | w''
      · simp
      · simp [h]
        -- w rejected m so m prefers w to his final gs match w''', whom he weak-prefers to his
        -- `matching` match w'' since m is a non-revendicateur.
        unfold revendicateur at m_notrev
        push_neg at m_notrev
        specialize m_notrev w'' h
        obtain ⟨w0, m_gs_matches_w0, w0_inequality⟩ := m_notrev
        rcases h2: (galeShapley mPref wPref) m with _ | w'''
        · rw [h2] at m_gs_matches_w0
          contradiction
        · have: w0 = w''' := matchingCondition'' m_gs_matches_w0 h2
          rw [this] at w0_inequality m_gs_matches_w0
          suffices (mPref m).symm w < (mPref m).symm w''' by omega
          have := rejectedEndsUpWithWorse (w' := w''') nextStep
            w_penultimate_gs_match_m m_unmatched_next
          rw [pref_inv.1, ← lastInvariant] at this
          exact this m_gs_matches_w0
    · right
      simp [(inverseProperty matching r' w).mp r'_matches_w]
      /- We must show that w prefers m to r'.

         Since m is the penultimate partner of w, then we must have the events
          r' proposed to w
          ...
          w rejects r' for m0
          ...
          w accepts m
          ...
          w rejects m for r
          (possibly m0 = m)

          In terms of the preferences of w:
          (most preferred) r, m, m0, r' (least preferred)
      -/
      have noWorse_ineq := last_rev_proposal.noWorseThanProposedTo r' w
      simp [pref_inv.1, pref_inv.2] at noWorse_ineq
      have: ((mPref r').symm w) < last_rev_proposal.proposeIndex r' := by
        rwa [r'_final_proposeIndex] at r'_proposed_w
      specialize noWorse_ineq this
      obtain ⟨m', w_inverse_matches_m', w_weakprefers_m'⟩ := noWorse_ineq
      have := (inverseProperty last_rev_proposal.matching m' w).mpr w_inverse_matches_m'
      have: m = m' := matchingCondition' w_penultimate_gs_match_m this
      rw [← this] at w_weakprefers_m'
      by_contra bad
      have: (wPref w).symm m = (wPref w).symm r' := by omega
      have := ((wPref w).symm.injective this)
      rw [this] at m_notrev
      contradiction

-- An alternate proof of the proposer optimality theorem
theorem proposerOptimal' (matching: Matching M W) (stable: isStableMatching mPref wPref matching):
    ∀ (m: M), ¬ (revendicateur mPref wPref matching m) := by
  intro m
  by_contra bad
  have := hwangTheorem mPref wPref matching ⟨m, bad⟩
  obtain ⟨m, m', w, _, _, _, unstable⟩ := this
  unfold isStableMatching at stable
  specialize stable m' w
  contradiction

/- Pareto optimality, here stated in the form: If M is nonempty, there exists a non-revendicateur for
   any matching (stable or not). -/
theorem paretoOptimality (matching: Matching M W) (h: Nonempty M): ∃ m, ¬ (revendicateur mPref wPref matching m) := by
  by_contra bad
  push_neg at bad
  let m := Classical.choice h
  have := hwangTheorem mPref wPref matching ⟨m, bad m⟩
  obtain ⟨m, m', w, _, _, nonRevendicateur, _⟩ := this
  specialize bad m'
  contradiction

-- unstable pair condition depends only on the preferences of the two people in the unstable pair
-- This lemma only states one implication, then the converse immediately follows in the next lemma.
lemma unstablePairLemma' (mPref': Pref M W) (wPref': Pref W M)
    (matching: Matching M W) (m: M) (w: W) (agree_m: mPref m = mPref' m) (agree_w: wPref w = wPref' w):
    isUnstablePair mPref wPref matching m w → isUnstablePair mPref' wPref' matching m w := by
  intro origUnstable
  unfold isUnstablePair at origUnstable ⊢
  rwa [← agree_m, ← agree_w]

-- iff version of the above
lemma unstablePairLemma (mPref': Pref M W) (wPref': Pref W M)
    (matching: Matching M W) (m: M) (w: W) (agree_m: mPref m = mPref' m) (agree_w: wPref w = wPref' w):
    isUnstablePair mPref wPref matching m w ↔ isUnstablePair mPref' wPref' matching m w := by
  constructor <;> apply unstablePairLemma' <;> tauto

/- A result from Dubins-Freedman, as stated in Dumont Theorem 2.3. We have generalized the result
   from Dumont to allow more than one liar from M.

   Let P is a set of preferences and P' be a set of preferences which differs from P by modifying
   one or more preferences in `mPref` but keeping `wPref` the same. We call the m in M who have
   modified their preferences `liars`. If the set of liars is non-empty, then at least one liar is a
   non-revendicateur with respect to gs(P').
 -/
theorem menShouldntLie (mPref': Pref M W) (existsLiar: mPref ≠ mPref'):
    ∃ m, mPref m ≠ mPref' m ∧ ¬ (revendicateur mPref wPref (galeShapley mPref' wPref) m) := by
  by_contra bad
  push_neg at bad
  have: ∃ m, mPref m ≠ mPref' m := by
    by_contra bad2
    push_neg at bad2
    have := funext bad2
    contradiction
  obtain ⟨m, mLied⟩ := this
  have bad_m := bad m mLied
  have := hwangTheorem mPref wPref (galeShapley mPref' wPref) ⟨m, bad_m⟩
  obtain ⟨_, m', w, _, _, m'_nonRevendicateur, m'_w_unstable⟩ := this
  specialize bad m'
  simp [m'_nonRevendicateur] at bad
  have := (unstablePairLemma mPref wPref mPref' wPref (galeShapley mPref' wPref) m' w bad rfl).mp m'_w_unstable
  exact galeShapleyNoUnstablePair mPref' wPref this
