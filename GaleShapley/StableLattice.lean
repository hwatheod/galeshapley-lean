import GaleShapley.GeneralLattice
import GaleShapley.TwoStableMatchings
import GaleShapley.Optimality
import Mathlib.Order.Basic
import Mathlib.Order.Sublattice

/-!

  # Complete lattice of stable matchings

  We complete the proof of Conway's result that for a fixed set of preferences,
  the set of stable matchings forms a complete lattice under the natural `inf`
  and `sup` operations.  The lattice is defined as `mPref_stableCompleteLattice`.
  All the hard work has already been done in `TwoStableMatchings` and this file
  merely assembles the pieces.

-/

namespace GaleShapley

open Classical
noncomputable section

export WithBot (some)

variable {M W: Type} [Fintype M] [Fintype W]
  (mPref: Pref M W)
  (wPref: Pref W M)


def StableMatching := {f : M → WithBot W |
  ∃ h : isMatching f, isStableMatching mPref wPref ⟨f, h⟩}

def toStableMatching (f: Matching M W) (stable: isStableMatching mPref wPref f):
  StableMatching mPref wPref := ⟨f.matching, ⟨f.matchingCondition, stable⟩⟩

def toMatching (f: StableMatching mPref wPref): Matching M W := {
  matching := f.val
  matchingCondition := by
    have := f.property
    unfold StableMatching at this
    obtain ⟨h, _⟩ := this
    exact h
}

def toStableCondition (f: StableMatching mPref wPref): isStableMatching mPref wPref
    (toMatching mPref wPref f) := by
  unfold StableMatching at f
  simp at f
  have := Subtype.prop f
  obtain ⟨_, f_stable⟩ := this
  unfold toMatching
  exact f_stable

def gsStableMatching: StableMatching mPref wPref :=
  toStableMatching mPref wPref
  (galeShapley mPref wPref)
  (galeShapleyGivesStableMatching mPref wPref)

instance : Inhabited (StableMatching mPref wPref) where
  default := gsStableMatching mPref wPref

set_option linter.unusedVariables false in
lemma stableMatchings_supClosed:
  have := mPref_lattice mPref
  SupClosed (StableMatching mPref wPref) := by
  unfold SupClosed
  intros lattice f0 hf0 g0 hg0

  let f := toMatching mPref wPref ⟨f0, hf0⟩
  let g := toMatching mPref wPref ⟨g0, hg0⟩
  obtain ⟨_, f_stable⟩ := hf0
  obtain ⟨_, g_stable⟩ := hg0

  let tsm: TwoStableMatchings M W := {
    mPref := mPref
    wPref := wPref
    f := f
    g := g
    f_stable := f_stable
    g_stable := g_stable
  }

  have closed := supMatchingClosed tsm
  unfold StableMatching
  simp at closed ⊢
  use closed

  have stable := supMatchingStable tsm
  exact stable

set_option linter.unusedVariables false in
def stableMatchings_infClosed:
  have := mPref_lattice mPref
  InfClosed (StableMatching mPref wPref) := by
  intros lattice f0 hf0 g0 hg0

  let f := toMatching mPref wPref ⟨f0, hf0⟩
  let g := toMatching mPref wPref ⟨g0, hg0⟩
  obtain ⟨_, f_stable⟩ := hf0
  obtain ⟨_, g_stable⟩ := hg0

  let tsm: TwoStableMatchings M W := {
    mPref := mPref
    wPref := wPref
    f := f
    g := g
    f_stable := f_stable
    g_stable := g_stable
  }

  have closed := infMatchingClosed tsm
  unfold StableMatching
  simp at closed ⊢
  use closed

  have stable := infMatchingStable tsm
  exact stable

def mPref_stableSublattice: @Sublattice (M → WithBot W) (mPref_lattice mPref).toLattice :=
  @Sublattice.mk (M → WithBot W) (mPref_lattice mPref).toLattice (StableMatching mPref wPref)
  (by apply stableMatchings_supClosed) (by apply stableMatchings_infClosed)

instance [Fintype α]: Fintype (WithBot α) := inferInstanceAs (Fintype (Option α))

instance mPref_stableCompleteLattice: CompleteLattice (StableMatching mPref wPref) :=
  let _: Lattice (StableMatching mPref wPref) := by
    let _ := mPref_lattice mPref
    let sublattice := Sublattice.instLatticeCoe (mPref_stableSublattice mPref wPref)
    simp [mPref_stableSublattice] at sublattice
    exact sublattice
  let _ := Fintype.toBoundedOrder (StableMatching mPref wPref)
  Fintype.toCompleteLattice (StableMatching mPref wPref)

lemma gsEqualsTop: gsStableMatching mPref wPref = ⊤ := by
  have: ∀ (a : StableMatching mPref wPref), a = ⊤ ↔ ∀ b, b ≤ a := by
    intro a
    constructor
    · intro a_top
      rw [a_top]
      exact fun b => OrderTop.le_top b
    · intro b_le_a
      specialize b_le_a ⊤
      exact eq_top_iff.mpr b_le_a
  rw [this]
  intro f
  rw [← left_eq_sup]
  apply_fun (fun x => x.val)
  simp
  let _ := mPref_lattice mPref
  conv_rhs => change ↑(gsStableMatching mPref wPref) ⊔ ↑f
  simp [Pi.sup_def, sup_eq_max]

  let f_matching := toMatching mPref wPref f
  let f_stable := toStableCondition mPref wPref f
  unfold toMatching at f_stable

  have := proposerOptimal mPref wPref f_matching f_stable
  unfold gsStableMatching toStableMatching
  simp
  unfold_let f_matching at this
  unfold toMatching at this
  simp at this
  apply funext
  intro m
  specialize this m
  cases h: (galeShapley mPref wPref) m
  · simp [h] at this
    simp [this]
  · case _ w =>
    simp [h] at this
    cases h2: (f: M → WithBot W) m
    · let _ := m_order mPref m
      simp [WithBot.none_eq_bot, max, CompleteLattice.bot_le]
    · case _ w' =>
      specialize this w' h2
      simp [max]
      let _ := m_order' mPref m
      simp [m_order'_le_def]
      exact this

  exact Subtype.val_injective
