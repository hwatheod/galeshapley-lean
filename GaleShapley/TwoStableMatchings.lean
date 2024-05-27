import GaleShapley.Matching
import GaleShapley.Basic
import GaleShapley.GeneralLattice
import Mathlib.Order.Lattice

/-!

 # Two stable matchings for a fixed set of preferences

 In this file, we fix a set of preferences `P` and two stable matching `f` and `g`
 with respect to P. The results are stated in terms of the natural lattice on
 `M → Option W` (defined in `GeneralLattice`).

 Note that there are two natural commuting symmetries: reversing `f` and `g`,
 and reversing `M` and `W` (using the inverse matchings). Thus each theorem
 has several symmetric versions. The symmetries are defined by `fg` and `mw`.
 We prove one version of a theorem, then deduce the symmetric versions
 using the symmetries.

 The first theorem in Dumont, section 1.3 is proven in `asymmetric_preference_f` and
 `asymmetric_preference_f'`. It says that if `f` sends `m` to `w`, then `m`
 prefers `f` to `g` if and only if `w` prefers `g` to `f`.  The `if` direction
 (`asymmetric_preference_f'`) is harder than the other and requires a
 finiteness arugment.

 The second theorem in Dumont, section 1.3 is proven in `sameSinglesM`.
 It is a result of Gale and Sotomayor, stating that the set of unmatched
 persons is the same for all stable matchings.

 Finally, we use these results to prove Conway's theorem (Dumont, section 1.4)
 that the set of stable matchings is closed under the natural `inf` and `sup`
 lattice operations, thus forming a complete lattice.

 In `StableLattice`, the results are assembled to construct the complete lattice.

-/
namespace GaleShapley

variable {M W: Type} [Fintype M] [Fintype W]

open Classical
noncomputable section

/- We fix a set of preferences and two stable matchings throughout. -/
structure TwoStableMatchings (M W: Type) [Fintype M] [Fintype W] where
  mPref: Pref M W
  wPref: Pref W M
  f: Matching M W
  g: Matching M W
  f_stable: isStableMatching mPref wPref f
  g_stable: isStableMatching mPref wPref g

/- The `isUnstablePair` condition expressed in terms of the lattice ordering. -/
def isUnstablePair' (mPref: Pref M W) (wPref: Pref W M)
    (matching: Matching M W) (m: M) (w: W): Prop :=
  let _ := m_order mPref m
  let _ := m_order wPref w
  some w > matching m ∧ some m > (inverseMatching matching) w

lemma isUnstableEquiv (mPref: Pref M W) (wPref: Pref W M)
    (matching: Matching M W) (m: M) (w: W):
    isUnstablePair mPref wPref matching m w ↔ isUnstablePair' mPref wPref matching m w := by
  unfold isUnstablePair isUnstablePair'
  simp

  let _ := m_order' mPref m
  let _ := m_order' wPref w
  have _ := WithBot.none_lt_some w -- writing none < some w would go through instLTOption. we just give the proof
  have _ := WithBot.none_lt_some m

  constructor
  · rcases matching m with _ | w'
    · simp
      rcases (inverseMatching matching) w with _ | m'
      · tauto
      · rw [WithBot.some_lt_some]
        simp [m_order'_lt_def]
        tauto
    · simp only [Option.getD_some, false_or]
      rcases (inverseMatching matching) w with _ | m'
      · rw [WithBot.some_lt_some]
        simp [m_order'_lt_def]
        tauto
      · simp only [Option.getD_some, false_or]
        rw [WithBot.some_lt_some, WithBot.some_lt_some]
        simp [m_order'_lt_def]
  · rcases h: matching m with _ | w'
    · simp
      rcases (inverseMatching matching) w with _ | m'
      · simp
      . simp
        rw [WithBot.some_lt_some]
        simp [m_order'_lt_def]
    · simp only [Option.getD_some, false_or, h]
      rcases (inverseMatching matching) w with _ | m'
      · rw [WithBot.some_lt_some]
        simp [m_order'_lt_def]
        tauto
      · simp only [Option.getD_some, false_or]
        rw [WithBot.some_lt_some, WithBot.some_lt_some]
        simp [m_order'_lt_def]

/- The inverse of a stable matching is stable. -/
lemma stableSymmetry {f: Matching M W} (f_stable: isStableMatching mPref wPref f):
    isStableMatching wPref mPref (inverseMatching f) := by
  unfold isStableMatching at f_stable ⊢
  simp [isUnstableEquiv] at f_stable ⊢
  intros w m
  specialize f_stable m w
  unfold isUnstablePair' at f_stable ⊢
  simp only [gt_iff_lt, inverseInvolution] at f_stable ⊢
  tauto

variable (tsm: TwoStableMatchings M W)

-- symmetry reversing M and W
@[simps]
def mw (tsm: TwoStableMatchings M W): TwoStableMatchings W M := {
  mPref := tsm.wPref
  wPref := tsm.mPref
  f := inverseMatching tsm.f
  g := inverseMatching tsm.g
  f_stable := stableSymmetry tsm.f_stable
  g_stable := stableSymmetry tsm.g_stable
}
@[simp] lemma mw_of_mw: mw (mw tsm) = tsm := by simp [mw]

-- symmetry reversing f and g
@[simps]
def fg (tsm: TwoStableMatchings M W): TwoStableMatchings M W := {
  mPref := tsm.mPref
  wPref := tsm.wPref
  f := tsm.g
  g := tsm.f
  f_stable := tsm.g_stable
  g_stable := tsm.f_stable
}
@[simp] lemma fg_of_fg: fg (fg tsm) = tsm := by rfl
@[simp] lemma fg_of_mw: fg (mw tsm) = mw (fg tsm) := by rfl

/- We define what it means for m to prefer f to g.
   We prove that if f and g disagree of m, then m prefers exactly one of f and g.
-/
def m_prefers_f (m: M): Prop :=
    have := m_order tsm.mPref m
    tsm.f m > tsm.g m

def m_prefers_g (m: M): Prop := m_prefers_f (fg tsm) m

def w_prefers_f (w: W): Prop := m_prefers_f (mw tsm) w

def w_prefers_g (w: W): Prop := m_prefers_g (mw tsm) w

@[simp] lemma m_prefers_f_fg: m_prefers_f (fg tsm) = m_prefers_g tsm := by rfl
@[simp] lemma m_prefers_g_fg: m_prefers_g (fg tsm) = m_prefers_f tsm := by rfl
@[simp] lemma w_prefers_f_fg: w_prefers_f (fg tsm) = w_prefers_g tsm := by rfl
@[simp] lemma w_prefers_g_fg: w_prefers_g (fg tsm) = w_prefers_f tsm := by rfl
@[simp] lemma m_prefers_f_mw: m_prefers_f (mw tsm) = w_prefers_f tsm := by rfl
@[simp] lemma m_prefers_g_mw: m_prefers_g (mw tsm) = w_prefers_g tsm := by rfl
@[simp] lemma w_prefers_f_mw: w_prefers_f (mw tsm) = m_prefers_f tsm := by unfold w_prefers_f; simp
@[simp] lemma w_prefers_g_mw: w_prefers_g (mw tsm) = m_prefers_g tsm := by
  unfold m_prefers_g w_prefers_g; simp

lemma m_prefers_f_or_g {m: M} (ne: tsm.f m ≠ tsm.g m):
    m_prefers_f tsm m ∨ m_prefers_g tsm m := by
  by_contra bad
  push_neg at bad
  rcases bad with ⟨not_mf, not_mg⟩
  simp [m_prefers_f] at not_mf
  simp [m_prefers_g, fg, m_prefers_f] at not_mg

  let _ := m_order tsm.mPref m
  have: tsm.g m = tsm.f m := le_antisymm not_mg not_mf
  exact ne.symm this

lemma w_prefers_f_or_g {w: W} (ne: inverseMatching tsm.f w ≠ inverseMatching tsm.g w):
    w_prefers_f tsm w ∨ w_prefers_g tsm w :=
  m_prefers_f_or_g (mw tsm) ne

lemma m_prefers_not_f {m: M} (ne: tsm.f m ≠ tsm.g m): ¬ m_prefers_f tsm m → m_prefers_g tsm m := by
  have := m_prefers_f_or_g tsm ne
  tauto

lemma m_prefers_not_g {m: M} (ne: tsm.f m ≠ tsm.g m): ¬ m_prefers_g tsm m → m_prefers_f tsm m := by
  have := m_prefers_f_or_g tsm ne
  tauto

lemma m_cannot_prefer_f_and_g {m: M} (mf: m_prefers_f tsm m) (mg: m_prefers_g tsm m): False := by
  simp [m_prefers_f] at mf
  simp [m_prefers_g, fg, m_prefers_f] at mg
  let _ := m_order tsm.mPref m
  exact (lt_irrefl _) (lt_trans mf mg)

lemma w_cannot_prefer_f_and_g {w: W} (wf: w_prefers_f tsm w) (wg: w_prefers_g tsm w): False :=
  m_cannot_prefer_f_and_g (mw tsm) wf wg

lemma w_prefers_not_f {w: W} (ne: inverseMatching tsm.f w ≠ inverseMatching tsm.g w):
    ¬ w_prefers_f tsm w → w_prefers_g tsm w :=
  m_prefers_not_f (mw tsm) ne

lemma w_prefers_not_g {w: W} (ne: inverseMatching tsm.f w ≠ inverseMatching tsm.g w):
    ¬ w_prefers_g tsm w → w_prefers_f tsm w :=
  m_prefers_not_g (mw tsm) ne

/- One direction of the first theorem in Dumont, section 1.3 -/
lemma asymmetric_preference_f {m: M} {w: W} (hf: tsm.f m = some w):
    m_prefers_f tsm m → w_prefers_g tsm w := by
  intro m_f

  by_contra bad
  suffices isUnstablePair tsm.mPref tsm.wPref tsm.g m w by
    have := tsm.g_stable
    unfold isStableMatching at this
    specialize this m w
    contradiction
  simp [isUnstableEquiv]
  unfold isUnstablePair'
  simp
  simp [m_prefers_f] at m_f
  simp [w_prefers_g, m_prefers_g, mw, fg, m_prefers_f] at bad
  rw [hf] at m_f
  rw [(inverseProperty tsm.f m w).mp hf] at bad
  simp [m_f]
  have: (inverseMatching tsm.g) w ≠ some m := by
    by_contra bad2
    rw [← inverseProperty tsm.g m w] at bad2
    rw [bad2] at m_f
    let _ := m_order tsm.mPref m
    exact (lt_irrefl _) m_f
  let _ := m_order tsm.wPref w
  exact lt_of_le_of_ne bad this

lemma asymmetric_preference_g {m: M} {w: W} (hg: tsm.g m = some w):
    m_prefers_g tsm m → w_prefers_f tsm w :=
  asymmetric_preference_f (fg tsm) (by simpa)

/-
   For the converse of result to `asymmetric_preference_f`, we need a counting
   argument to show that that restriction of `f` gives a bijection from the
   subset of M preferring f to the subset of W preferring g, and symmetrically
   reversing M and W, f and g.
-/
def all_m_prefer_f := {m : M | m_prefers_f tsm m}.toFinset
def all_w_prefer_g := all_m_prefer_f (mw (fg tsm))
@[simp] lemma all_m_prefer_f_mw_fg: all_m_prefer_f (mw (fg tsm)) = all_w_prefer_g tsm := by rfl
@[simp] lemma all_w_prefer_g_mw_fg: all_w_prefer_g (mw (fg tsm)) = all_m_prefer_f tsm := by simp [all_w_prefer_g]

lemma image_prefer_f_prefer_g {m: M} (h: m ∈ all_m_prefer_f tsm):
    ∃ w, tsm.f m = some w ∧ w ∈ all_w_prefer_g tsm := by
  simp [all_m_prefer_f] at h
  have h' := h
  simp [m_prefers_f] at h
  obtain ⟨w, m_f_matches_w, _⟩ := h
  use w
  constructor
  · exact m_f_matches_w
  · simp [all_w_prefer_g, all_m_prefer_f]
    exact asymmetric_preference_f tsm m_f_matches_w h'

lemma image_prefer_g_prefer_f {w: W} (h: w ∈ all_w_prefer_g tsm):
    ∃ m, (inverseMatching tsm.g) w = some m ∧ m ∈ all_m_prefer_f tsm := by
  have := image_prefer_f_prefer_g (mw (fg tsm)) h
  simp at this
  exact this

def tsm_f_restrict: all_m_prefer_f tsm → all_w_prefer_g tsm :=
  fun m => ⟨(tsm.f m).get (by
    have := Subtype.prop m
    have := image_prefer_f_prefer_g tsm this
    obtain ⟨w, hw, _⟩ := this
    simp [hw]
  ), (by
    have := Subtype.prop m
    have := image_prefer_f_prefer_g tsm this
    obtain ⟨w, hw, pref_g⟩ := this
    simp [hw]
    exact pref_g
  )⟩

def tsm_g_restrict: all_w_prefer_g tsm → all_m_prefer_f tsm :=
  fun w =>
    let result := tsm_f_restrict (mw (fg tsm)) w
    ⟨result.val, (by
      have := Subtype.prop result
      simp [all_w_prefer_g] at this
      exact this
    )⟩

lemma tsm_f_restrict_injective: Function.Injective (tsm_f_restrict tsm) := by
  intros m1 m2
  unfold tsm_f_restrict
  intro eq
  generalize_proofs p1 p2 p3 p4 at eq
  rw [Option.isSome_iff_exists] at p1 p3
  obtain ⟨w, hw⟩ := p1
  obtain ⟨w', hw'⟩ := p3
  simp_rw [hw, hw'] at eq
  simp at eq
  rw [eq] at hw
  have := matchingCondition' hw hw'
  exact Subtype.val_injective this

lemma tsm_g_restrict_injective: Function.Injective (tsm_g_restrict tsm) := by
  have := tsm_f_restrict_injective (mw (fg tsm))
  unfold tsm_g_restrict
  simp [Function.Injective, Subtype.val_inj] at this ⊢
  exact this

lemma two_sets_eq_cardinality: (all_m_prefer_f tsm).card = (all_w_prefer_g tsm).card := by
  have f_to_g := Fintype.card_le_of_injective (tsm_f_restrict tsm) (tsm_f_restrict_injective tsm)
  have g_to_f := Fintype.card_le_of_injective (tsm_g_restrict tsm) (tsm_g_restrict_injective tsm)
  simp at f_to_g g_to_f
  omega

lemma tsm_f_restrict_bijective: Function.Bijective (tsm_f_restrict tsm) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact tsm_f_restrict_injective tsm
  · simp [two_sets_eq_cardinality]

lemma tsm_g_restrict_bijective: Function.Bijective (tsm_g_restrict tsm) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact tsm_g_restrict_injective tsm
  · simp [two_sets_eq_cardinality]

/- This is the converse of asymmetric_preference_f and is much harder to prove. It depends
   on finiteness and needs the tsm_f_restrict function defined above. It is the
   other direction of the first theorem in Dumont section 1.3.
-/
lemma asymmetric_preference_f' {m: M} {w: W} (hf: tsm.f m = some w):
    w_prefers_g tsm w → m_prefers_f tsm m := by
  intro w_g

  by_contra m_g
  apply m_prefers_not_f tsm (by
    by_contra bad
    rw [hf] at bad
    simp [w_prefers_g, m_prefers_g, fg, mw, m_prefers_f] at w_g
    rw [(inverseProperty tsm.f _ _).mp hf, (inverseProperty tsm.g _ _).mp bad.symm] at w_g
    let _ := m_order tsm.wPref w
    exact lt_irrefl _ w_g
  ) at m_g

  have: Function.Surjective (tsm_f_restrict tsm) :=
    Function.Bijective.surjective (tsm_f_restrict_bijective tsm)

  unfold Function.Surjective at this
  specialize this ⟨w, (by
    unfold all_w_prefer_g
    simp [all_m_prefer_f]
    exact w_g
  )⟩

  obtain ⟨m', m'_f_matches_w⟩ := this
  have m_f := Subtype.prop m'
  unfold all_m_prefer_f at m_f
  simp at m_f

  unfold tsm_f_restrict at m'_f_matches_w
  simp at m'_f_matches_w
  generalize_proofs p at m'_f_matches_w
  have := Option.eq_some_iff_get_eq.mpr ⟨p, m'_f_matches_w⟩
  have := matchingCondition' hf this

  rw [← this] at m_f
  exact m_cannot_prefer_f_and_g tsm m_f m_g

lemma asymmetric_preference_g' {m: M} {w: W} (hg: tsm.g m = some w):
    w_prefers_f tsm w → m_prefers_g tsm m :=
  asymmetric_preference_f' (fg tsm) hg

/- Gale and Sotomayor's result that the same people are single in all stable matchings.
   This is sometimes called the bachelor or bachelorette theorem. This is the second
   theorem in Dumont section 1.3. -/
def sameSinglesM (m: M): tsm.f m = none ↔ tsm.g m = none := by
  suffices ∀ (tsm: TwoStableMatchings M W) (m: M), tsm.g m = none → tsm.f m = none by
    constructor
    · exact this (fg tsm) m
    · exact this tsm m

  intro tsm m m_g_unmatched
  by_contra m_f_matched
  push_neg at m_f_matched
  rw [Option.ne_none_iff_exists] at m_f_matched
  obtain ⟨w, m_f_matches_w⟩ := m_f_matched

  have m_f: m_prefers_f tsm m := by
    simp [m_prefers_f]
    use w
    simp [m_f_matches_w, m_g_unmatched]

  have: Function.Surjective (tsm_g_restrict tsm) :=
    Function.Bijective.surjective (tsm_g_restrict_bijective tsm)
  unfold Function.Surjective at this
  specialize this ⟨m, (by unfold all_m_prefer_f; simp [m_f])⟩
  obtain ⟨w, m_g_matches_w⟩ := this
  unfold tsm_g_restrict mw fg tsm_f_restrict at m_g_matches_w
  simp at m_g_matches_w
  generalize_proofs p1 p2 p3 at m_g_matches_w
  have := Option.eq_some_iff_get_eq.mpr ⟨p3, m_g_matches_w⟩
  rw [← inverseProperty tsm.g _ _] at this
  rw [this] at m_g_unmatched
  contradiction

def sameSinglesW (w: W): (inverseMatching tsm.f) w = none ↔ (inverseMatching tsm.g) w = none :=
  sameSinglesM (mw tsm) w

/- Now we prove several lemmas to establish Conway's result that stable matchings
   are closed under `inf` and `sup`. This theorem is stated in Dumont, section 1.4.

   In `supMatchingClosed`, we show that the `sup` of two stable matchings
   is a matching. Note that the `sup` of two arbitrary matchings is not necessarily
   a matching.

   In `supMatchingStable`, we show that the `sup` of two stable matchings
   is a *stable* matching.

   Then we deduce the symmetrical results for `inf`.  The key lemma relating the
   `inf` and `sup` matchings is the `supMatching_inverse_lemma`.
-/
lemma supMatchingClosed (tsm: TwoStableMatchings M W):
    have := mPref_lattice tsm.mPref
    isMatching (tsm.f ⊔ tsm.g) := by

  simp [Pi.sup_def, sup_eq_max]

  unfold isMatching
  simp
  intros m1 m2
  let _ := m_order tsm.mPref m2
  wlog h2: tsm.f m2 ≤ tsm.g m2 generalizing tsm
  · have gf: tsm.g m2 ≤ tsm.f m2 := le_of_not_ge h2
    specialize this (fg tsm) gf
    simp at this
    rw [max_comm] at this
    let _ := m_order tsm.mPref m1
    rwa [max_comm] at this
  intros w m2_matches_w m1_eq_m2
  rcases hf2: (tsm.f m2) with _ | wf2
  · have: tsm.g m2 = none := (sameSinglesM tsm m2).mp hf2
    simp [hf2, this] at m2_matches_w
  · rcases hg2: (tsm.g m2) with _ | wg2
    · have: tsm.f m2 = none := (sameSinglesM tsm m2).mpr hg2
      simp [this] at hf2
    · rcases hf1: (tsm.f m1) with _ | wf1
      · have: tsm.g m1 = none := (sameSinglesM tsm m1).mp hf1
        simp [hf2, hg2, hf1, this] at m2_matches_w m1_eq_m2
        let _ := m_order tsm.mPref m1
        simp [m2_matches_w] at m1_eq_m2
      · rcases hg1: (tsm.g m1) with _ | wg1
        · have: tsm.f m1 = none := (sameSinglesM tsm m1).mpr hg1
          simp [this] at hf1
        · -- the real proof starts here
          simp [hf2, hg2, hf1, hg1] at m2_matches_w m1_eq_m2 h2
          rw [m2_matches_w] at m1_eq_m2

          simp [h2] at m2_matches_w
          let _ := m_order tsm.mPref m1
          by_cases h1: some wf1 ≤ some wg1 -- m1 prefers g
          · simp [h1] at m1_eq_m2
            rw [m2_matches_w] at hg2
            rw [m1_eq_m2] at hg1
            exact matchingCondition' hg1 hg2
          · simp [max_def, h1] at m1_eq_m2 -- m1 prefers f
            push_neg at h1
            rw [m2_matches_w] at h2 hg2
            rw [m1_eq_m2] at h1 hf1

            by_cases h: tsm.f m2 ≠ some w ∧ tsm.g m1 ≠ some w
            · have m1_f: m_prefers_f tsm m1 := by
                simp [m_prefers_f]
                rwa [hf1, hg1]
              have m2_g: m_prefers_g tsm m2 := by
                simp [m_prefers_g, fg, m_prefers_f]
                rw [hg2, hf2]
                by_contra bad
                have: w = wf2 := by
                  let _ := m_order tsm.mPref m2
                  let _ := m_order' tsm.mPref m2
                  simp at bad
                  rw [WithBot.some_le_some] at h2 bad
                  exact le_antisymm bad h2
                rw [← this] at hf2
                exact h.1 hf2

              have w_g: w_prefers_g tsm w := asymmetric_preference_f tsm hf1 m1_f
              have w_f: w_prefers_f tsm w := asymmetric_preference_g tsm hg2 m2_g
              exact False.elim (w_cannot_prefer_f_and_g tsm w_f w_g)
            · set_option push_neg.use_distrib true in push_neg at h
              rcases h with c1 | c2
              · exact matchingCondition' hf1 c1
              · exact matchingCondition' c2 hg2

def supMatching: Matching M W :=
  let lattice := mPref_lattice tsm.mPref
  {
    matching := tsm.f ⊔ tsm.g
    matchingCondition := (by
      have closed := supMatchingClosed tsm
      simp at closed
      exact closed
    )
  }

@[simp]
lemma supMatchingSymmetry: supMatching (fg tsm) = supMatching tsm := by
  unfold supMatching fg
  simp
  let _ := mPref_lattice tsm.mPref
  exact sup_comm _ _

lemma supMatching_mf (m: M): m_prefers_f tsm m → supMatching tsm m = tsm.f m := by
  intro m_f
  simp [m_prefers_f] at m_f
  simp [supMatching]
  let _ := m_order tsm.mPref m
  exact le_of_lt m_f

lemma supMatching_mf' (m: M): supMatching tsm m = tsm.f m → tsm.f m ≠ tsm.g m → m_prefers_f tsm m  := by
  simp [supMatching, m_prefers_f]
  let _ := m_order tsm.mPref m
  exact fun a a_1 => lt_of_le_of_ne a fun a => a_1 (id a.symm)

lemma supMatching_mg (m: M): m_prefers_g tsm m → supMatching tsm m = tsm.g m := by
  intro m_g
  simp [supMatching]
  let _ := m_order tsm.mPref m
  exact le_of_lt m_g

lemma supMatching_mg' (m: M): supMatching tsm m = tsm.g m → tsm.f m ≠ tsm.g m → m_prefers_g tsm m := by
  simp [supMatching, m_prefers_g, m_prefers_f]
  let _ := m_order tsm.mPref m
  exact fun a a_1 => lt_of_le_of_ne a a_1

lemma supMatching_inverse_lemma:
    have := mPref_lattice tsm.mPref
    have := mPref_lattice (M := W) (W := M) tsm.wPref
    inverseMatching (supMatching tsm) =
      (inverseMatching tsm.f).matching ⊓ (inverseMatching tsm.g).matching := by
  apply funext
  intro w
  simp [Pi.inf_def, inf_eq_min]
  let _ := m_order tsm.wPref w

  wlog h2: (inverseMatching tsm.f) w ≤ (inverseMatching tsm.g) w
  · by_cases h: (inverseMatching tsm.f) w ≠ (inverseMatching tsm.g) w
    · have gfw: (inverseMatching tsm.g) w ≤ (inverseMatching tsm.f) w := by exact le_of_not_ge h2
      specialize this (fg tsm) w gfw
      simp at this
      rwa [min_comm]
    · simp at h
      rw [h] at h2
      simp at h2
  simp [min_def, h2]

  by_cases h: (inverseMatching tsm.f) w ≠ (inverseMatching tsm.g) w
  · have w_g: w_prefers_g tsm w := by
      simp [w_prefers_g, m_prefers_g, mw, m_prefers_f]
      exact lt_of_le_of_ne h2 h

    rcases h3: (inverseMatching tsm.f) w with _ | m
    · simp [w_prefers_g, m_prefers_g, mw, m_prefers_f] at w_g
      rw [h3] at w_g
      have: (inverseMatching tsm.g) w ≠ none := by
        by_contra bad
        rw [bad] at w_g
        exact lt_irrefl _ w_g
      exact False.elim (this ((sameSinglesW tsm w).mp h3))
    . have := asymmetric_preference_f' tsm ((inverseProperty tsm.f _ _).mpr h3) w_g
      rw [← inverseProperty _ _ _] at h3 ⊢
      have := supMatching_mf tsm m this
      rwa [h3] at this
  · push_neg at h
    rcases h3: (inverseMatching tsm.f) w with _ | m
    · rw [h3] at h
      symm at h
      rw [← inversePropertyNone] at h h3 ⊢
      intro m
      specialize h m
      specialize h3 m
      simp [supMatching, Pi.sup_def, sup_eq_max]
      by_contra bad
      simp [max_def] at bad
      split_ifs at bad <;> contradiction
    · rw [h3] at h
      symm at h
      rw [← inverseProperty _ _ _] at h h3 ⊢
      simp [supMatching, Pi.sup_def, sup_eq_max]
      rw [h, h3]
      simp

lemma supMatchingStable (tsm: TwoStableMatchings M W):
    have := mPref_lattice tsm.mPref
    isStableMatching tsm.mPref tsm.wPref (supMatching tsm) := by
  intro
  unfold isStableMatching
  intros m w
  by_contra unstable
  simp [isUnstableEquiv] at unstable
  unfold isUnstablePair' at unstable
  simp at unstable
  obtain ⟨mUnstable, wUnstable⟩ := unstable

  simp [supMatching, Pi.sup_def] at mUnstable
  simp [supMatching_inverse_lemma tsm, Pi.inf_def] at wUnstable

  have f_stable := tsm.f_stable
  simp [isStableMatching, isUnstableEquiv, isUnstablePair'] at f_stable
  specialize f_stable m w mUnstable.1

  have g_stable := tsm.g_stable
  simp [isStableMatching, isUnstableEquiv, isUnstablePair'] at g_stable
  specialize g_stable m w mUnstable.2

  let _ := m_order tsm.wPref w
  apply not_lt.mpr at f_stable
  apply not_lt.mpr at g_stable
  tauto

lemma infMatchingClosed (tsm: TwoStableMatchings M W):
    have := mPref_lattice tsm.mPref
    isMatching (tsm.f ⊓ tsm.g) := by

  intro lattice
  have := supMatching_inverse_lemma (mw tsm)
  simp at this
  rw [← this]
  exact (inverseMatching (supMatching (mw tsm))).matchingCondition

def infMatching: Matching M W :=
  let lattice := mPref_lattice tsm.mPref
  {
    matching := tsm.f ⊓ tsm.g
    matchingCondition := (by
      have closed := infMatchingClosed tsm
      simp at closed
      exact closed
    )
  }

lemma infMatching_lemma (tsm: TwoStableMatchings M W):
    let _ := mPref_lattice tsm.mPref
    let _ := mPref_lattice (mw tsm).mPref
    infMatching tsm = inverseMatching (supMatching (mw tsm)) := by
  have := supMatching_inverse_lemma (mw tsm)
  simp at this ⊢
  apply_fun (fun x => x.matching)
  simp
  rw [this]
  rfl

  exact matching_coe_injective

lemma infMatchingStable (tsm: TwoStableMatchings M W):
    have := mPref_lattice tsm.mPref
    isStableMatching tsm.mPref tsm.wPref (infMatching tsm) := by
  simp
  rw [infMatching_lemma]

  have supStable := supMatchingStable (mw tsm)
  simp at supStable
  apply stableSymmetry at supStable
  exact supStable
