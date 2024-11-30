import GaleShapley.Matching
import GaleShapley.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Option

/-!
  # Lattice structure on M → Option W

  This file defines the canonical complete lattice structure on all functions (not necessarily
  matchings) `M → Option W`. For each m in M, `m_order' m` defines a linear order on W by
  the preferences of m. Then `m_order m` extends this to `Option W` as
  `WithBot W` since being single is the worst option for the Gale-Shapley algorithm.
  All of this is then assembled into the canonical pointwise lattice structure on
  `M → Option W` in the function `mPref_lattice`.

  In `TwoStableMatchings` we prove that the set of stable matchings forms a sublattice of
  this larger lattice.

-/

namespace GaleShapley

open Classical
noncomputable section

variable {M W: Type} [Fintype M] [Fintype W]
  (mPref: Pref M W)
  (wPref: Pref W M)

def m_order' (m: M): LinearOrder W where
  le := fun w1 w2 => (mPref m).symm w1 ≥ (mPref m).symm w2  -- this is intentionally reversed
  le_refl := by simp
  le_trans := by
    simp
    omega
  le_antisymm := by
    simp
    intros a b _ _
    have: (mPref m).symm a = (mPref m).symm b := by omega
    exact Equiv.injective (mPref m).symm this
  le_total := by
    simp
    exact fun a b => LinearOrder.le_total ((mPref m).symm b) ((mPref m).symm a)
  decidableLE := inferInstance

lemma m_order'_le_def (m: M) (w1 w2: W):
    let _ := m_order' mPref m
    w1 ≤ w2 ↔ (mPref m).symm w1 ≥ (mPref m).symm w2 := by rfl

lemma m_order'_lt_def (m: M) (w1 w2: W):
    let _ := m_order' mPref m
  w1 < w2 ↔ (mPref m).symm w1 > (mPref m).symm w2 := by
  let ord := m_order' mPref m
  simp
  rw [lt_iff_le_not_le]
  simp [m_order'_le_def]
  omega

def m_order (m: M): CompleteLinearOrder (WithBot W) :=
  let _ : Fintype (WithBot W) := inferInstanceAs (Fintype (Option W))
  let _ := @WithBot.linearOrder W (m_order' mPref m)
  Fintype.toCompleteLinearOrderOfNonempty (WithBot W)

def mPref_lattice: CompleteLattice (M → WithBot W) :=
  @Pi.instCompleteLattice M (fun _ => WithBot W) (fun m => (m_order mPref m).toCompleteLattice)
