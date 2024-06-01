import Mathlib.Data.Set.Finite

namespace GaleShapley.Compute

variable {M W: Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

def isMatching (matching: M → Option W): Prop := ∀ {{m1}} {{m2}},
  (∃ w, matching m2 = some w) → matching m1 = matching m2 → m1 = m2

@[ext]
structure Matching (M W: Type) where
  matching: M → Option W
  matchingCondition: isMatching matching

instance : CoeFun (Matching M W) (fun _ ↦ M -> Option W) where
  coe := fun m => m.matching

attribute [coe] Matching.matching

theorem matchingCondition' {matching: Matching M W}: ∀ {w}, matching m1 = some w → matching m2 = some w → m1 = m2 := by
  intro w c1 c2
  rw [← c2] at c1
  exact matching.matchingCondition ⟨w, c2⟩ c1

theorem matching_coe_injective (a: Matching M W) (b: Matching M W):
    (↑a : M → Option W) = (↑b: M → Option W) → a = b := by
  exact fun a_1 => (fun x y => (Matching.ext_iff x y).mpr) a b a_1

@[simps]
def emptyMatching: Matching M W := {
  matching := fun _ => none
  matchingCondition := by tauto
}

def matchingUniquePreimage (matching: Matching M W)
    (w: W): (∃ m, matching m = some w) → ∃! m, matching m = some w := by
  intro h
  obtain ⟨m', hm'⟩ := h
  use m'
  simp [hm']

  intro y
  rw [← hm']
  apply matching.matchingCondition

  rw [hm']
  tauto

def inverseMatching' (matching: Matching W M): M → Option W :=
  fun m =>
      let acceptedM := fun w => matching w = some m
      if h : ∃ w, acceptedM w then
        have: ∃! w, acceptedM w := by
          simp [acceptedM] at h ⊢
          exact matchingUniquePreimage matching m h
        some (Finset.chooseX acceptedM (Finset.univ (α := W)) (by
          simp
          exact this
        ))
      else none

theorem inverseProperty' (matching: Matching M W):
    ∀ m, ∀ w, matching m = some w ↔ (inverseMatching' matching) w = (some m) := by
  intros m w
  constructor
  · intro mw
    have: ∃ m, matching m = some w := by use m
    set m'Option := inverseMatching' matching w with m'Option_rfl
    simp [inverseMatching', this] at m'Option_rfl
    rcases m'Option with _ | m'
    tauto

    simp at m'Option_rfl
    symm at m'Option_rfl
    apply Subtype.coe_eq_iff.mp at m'Option_rfl
    obtain ⟨h', _⟩ := m'Option_rfl
    simp at h'
    rw [← h'] at mw
    apply matching.matchingCondition at mw
    rw [mw]

    rw [h']
    tauto

  · intro w_matches_m
    simp [inverseMatching'] at w_matches_m
    by_cases h : ∃ m, matching m = some w
    · simp [h] at w_matches_m
      apply Subtype.coe_eq_iff.mp at w_matches_m
      obtain ⟨h', _⟩ := w_matches_m
      tauto
    · simp [h] at w_matches_m

def inverseMatching (matching: Matching W M): Matching M W := {
  matching := inverseMatching' matching
  matchingCondition := by
    simp only [isMatching, forall_exists_index]
    intros w1 w2 m h2 h1
    rw [h2] at h1
    apply (inverseProperty' matching m w2).mpr at h2
    apply (inverseProperty' matching m w1).mpr at h1
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    exact h2
}

theorem inverseProperty (matching: Matching M W):
    ∀ m, ∀ w, matching m = some w ↔ (inverseMatching matching) w = (some m) := by
  exact inverseProperty' matching

theorem inversePropertyNone (matching: Matching M W):
    ∀ w, (∀ m, matching m ≠ some w) ↔ (inverseMatching matching) w = none := by
  intro w
  constructor
  · intros w_matches_none
    by_contra bad
    push_neg at bad
    rw [Option.ne_none_iff_exists] at bad
    obtain ⟨m, m_matches_w⟩ := bad
    specialize w_matches_none m
    symm at m_matches_w
    rw [← inverseProperty matching m w] at m_matches_w
    exact w_matches_none m_matches_w
  · intros w_matches_none m
    by_contra bad
    rw [inverseProperty matching m w] at bad
    rw [bad] at w_matches_none
    contradiction

@[simp]
theorem inverseInvolution (matching: Matching M W):
    inverseMatching (inverseMatching matching) = matching := by
  apply matching_coe_injective
  apply funext
  intro m
  rcases h: matching m with _ | w
  · rw [← inversePropertyNone _ m]
    intro w
    have := (inverseProperty matching m w)
    rw [Iff.symm Decidable.not_iff_not] at this
    simp
    rw [← this]
    by_contra bad
    rw [bad] at h
    contradiction
  · apply (inverseProperty (inverseMatching matching) w m).mp
    exact (inverseProperty matching m w).mp h

def createMatching (matching: M → Option W) (invMatching: W → Option M)
    (invCondition: ∀ m, ∀ w, matching m = some w → invMatching w = some m): Matching M W := {
  matching := matching
  matchingCondition := by
    unfold isMatching
    intro m1 m2 ⟨w, m2_matches_w⟩ m1_matches_w
    rw [m2_matches_w] at m1_matches_w
    have c1 := invCondition m1 w m1_matches_w
    have c2 := invCondition m2 w m2_matches_w
    rw [c1] at c2
    simp at c2
    exact c2
}

lemma matching_equal_cardinality (matching: Matching M W) (R: Finset M)
    (matched: ∀ (r: R), ∃ w, matching r = some w)
    (hS: S = {w | ∃ (r : R), matching r = some w}.toFinset): R.card = S.card := by
  let S0 := (some '' S.toSet).toFinset
  let matching_restrict' := Set.restrict R matching
  let matching_restrict := Set.codRestrict matching_restrict' S0 (by
    intro r
    simp at r
    simp [matching_restrict', hS, S0]
    specialize matched r
    obtain ⟨w, r_matches_w⟩ := matched
    use w
    refine ⟨⟨r, (by simp), r_matches_w⟩, r_matches_w.symm⟩
  )

  have inj: Function.Injective matching_restrict := by
    intro r1 r2
    simp only [matching_restrict, Set.codRestrict, matching_restrict', Set.restrict]
    simp
    conv in (r1 = r2) => {
      rw [← Subtype.val_inj]
    }
    apply Matching.matchingCondition matching
    exact matched ⟨r2, (by simp)⟩

  have surj: Function.Surjective matching_restrict := by
    intro s
    simp at s
    simp only [matching_restrict, Set.codRestrict, matching_restrict', Set.restrict]
    have := Subtype.prop s
    simp [hS, S0] at this
    obtain ⟨w, ⟨m, m_in_R, m_matches_w⟩, h1⟩ := this
    simp
    use m
    use m_in_R
    simp [m_matches_w]
    exact Subtype.val_injective h1

  have rs0: R.card = S0.card := by
    have rcard: Fintype.card R = R.card := by exact Fintype.card_coe R
    have s0card: Fintype.card S0 = S0.card := by exact Fintype.card_coe S0
    rw [← rcard, ← s0card]
    apply Fintype.card_of_bijective
    exact ⟨inj, surj⟩

  have: S0.card = S.card := by
    simp [S0]
    refine Finset.card_image_iff.mpr ?_
    apply Function.Injective.injOn
    exact Option.some_injective _

  rwa [this] at rs0
