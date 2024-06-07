import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Nat

/-!

  # GaleShapley.Iterate

  This file defines generic utility functions and lemmas useful for working
  with an algorithm that repeatedly applies a step to a state until some
  condition is reached in the state.

  `α`: an arbitrary type which holds the state

  `Terminator α`: a structure containing the fields
      `nextStep`: a function `α` → `Option α` which returns either the next
         state or `⊥` to indicate termination
      `termination`: a function `α` → `ℕ` to prove termination.
      `decreasing`: A proof that the `termination` function decreases at each step.

  `iterate` repeatedly applies `nextStep` until termination is reached,
    and collects the states into a list in `List α`.

  Induction principles are provided in `stateInduction` and `stateStrongInduction`.
-/
namespace GaleShapley.Iterate

variable {α: Type} [Inhabited α]

export WithBot (some)

structure Terminator (α: Type) where
  nextStep: α → WithBot α
  termination: α → ℕ
  decreasing: ∀ s, (h: nextStep s ≠ ⊥) →
    termination ((nextStep s).unbot h) < termination s

set_option linter.unusedVariables false in
def iterate (step: Terminator α) (state: α) : List α :=
  match h: step.nextStep state with
  | ⊥ => [state]
  | some newState => state :: iterate step newState
termination_by
  step.termination state
decreasing_by
  simp_wf
  have := step.decreasing state (by simp [h])
  simp [h] at this
  exact this

lemma iterate.induct' {α : Type} (step : Terminator α) (motive : α → Prop)
    (case1 : ∀ (x : α), step.nextStep x = ⊥ → motive x)
    (case2 : ∀ (x newState : α), step.nextStep x = some newState → motive newState → motive x) (state : α) :
    motive state := by
  exact iterate.induct step motive case1 case2 state

lemma iterateIsNonEmpty (step: Terminator α) (state: α):
    iterate step state ≠ [] := by
  unfold iterate
  split <;> simp

lemma iterate_single_state {step: Terminator α} {state: α}
    (noneStep: step.nextStep state = ⊥):
    iterate step state = [state] := by
  unfold iterate
  rw [noneStep]

lemma iterate_next_state {step: Terminator α} {state: α}
    (nextStep: step.nextStep state = some nextState):
    iterate step state = state :: iterate step nextState := by
  conv_lhs => unfold iterate
  rw [nextStep]

lemma decreasing_nextStepSome {step: Terminator α} (nextStep: step.nextStep state = some nextState):
    step.termination nextState < step.termination state := by
  have := step.decreasing state (by simp [nextStep])
  simp_rw [nextStep] at this
  simp at this
  exact this

lemma global_decreasing {step: Terminator α} {s state: α}
    (h: s ∈ iterate step state): step.termination s ≤ step.termination state := by
  induction state using (iterate.induct' step) with
| case1 state noneStep =>
  have := iterate_single_state noneStep
  simp [this] at h
  simp [h]
| case2 state nextState nextStep ih =>
  have := iterate_next_state nextStep
  simp [this] at h
  rcases h with s_state | s_next
  · simp [s_state]
  · specialize ih s_next
    have := step.decreasing state (by simp [nextStep])
    simp [nextStep] at this
    omega

lemma termination_injective {step: Terminator α} {state s t: α}
    (hs: s ∈ iterate step state) (ht: t ∈ iterate step state)
    (eq: step.termination s = step.termination t): s = t := by
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    rw [this] at hs ht
    simp at hs ht
    rw [hs, ht]
  | case2 state nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp [this] at hs ht
    rcases hs with s_state | s_next
    · rcases ht with t_state | t_next
      · rw [s_state, t_state]
      · apply global_decreasing at t_next
        have := decreasing_nextStepSome nextStep
        rw [← s_state] at this
        omega
    · rcases ht with t_state | t_next
      · apply global_decreasing at s_next
        have := decreasing_nextStepSome nextStep
        rw [← t_state] at this
        omega
      · exact ih s_next t_next

set_option linter.unusedVariables false in
lemma iterateHead (step: Terminator α) (state: α):
    (iterate step state).head (iterateIsNonEmpty step state) = state := by
  unfold iterate
  let motive := fun x => (match h: x with
    | none => [state]
    | some newState => state :: iterate step newState).head (by split <;> simp) = state
  by_cases h: step.nextStep state = ⊥
  · have: motive (step.nextStep state) = motive none := by rw [h]
    simp [motive] at this
    exact this
  · push_neg at h
    rw [WithBot.ne_bot_iff_exists] at h
    obtain ⟨newState, nextStep⟩ := h
    have: motive (step.nextStep state) = motive ↑newState := by rw [← nextStep]
    simp [motive] at this
    exact this

lemma iterateReflexivity (step: Terminator α) (state: α):
    state ∈ iterate step state := by
  rw (config := {occs := .pos [1]}) [← iterateHead step state]
  exact List.head_mem (iterateIsNonEmpty step state)

lemma iterateAntisymmetry {step: Terminator α} {state s t: α}
    (hs: s ∈ iterate step state) (ht: t ∈ iterate step state)
    (s_le_t: t ∈ iterate step s) (t_le_s: s ∈ iterate step t): s = t := by
  apply global_decreasing at s_le_t
  apply global_decreasing at t_le_s
  have: step.termination s = step.termination t := by omega
  apply termination_injective hs ht at this
  exact this

lemma iterateTransitivity {s t u: α}
    (h1: t ∈ iterate step s) (h2: u ∈ iterate step t): u ∈ iterate step s := by
  induction s using (iterate.induct' step) with
  | case1 s noneStep =>
    have := iterate_single_state noneStep
    simp [this] at h1 ⊢
    rw [h1, this] at h2
    simp at h2
    exact h2
  | case2 s nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp [this] at h1 ⊢
    rcases h1
    case _ t_eq_s =>
      rw [t_eq_s] at h2
      simp [this] at h2
      exact h2
    case _ t_in_nextState =>
      right
      exact ih t_in_nextState

lemma iterateNextState {state: α}
    (nextStateSome: step.nextStep state = some nextState):
    nextState ∈ iterate step state := by
  unfold iterate
  rw [nextStateSome]
  simp
  right
  exact iterateReflexivity step nextState

lemma iterateNextState' {s state t: α}
    (s_in_state: s ∈ iterate step state)
    (nextStateSome: step.nextStep s = some t):
    t ∈ iterate step state := by
  apply iterateTransitivity
  exact s_in_state
  exact iterateNextState nextStateSome

lemma iterate_nextStateLastIsSame {state: α}
    (nextStateSome: step.nextStep state = some nextState):
    (iterate step state).getLast (iterateIsNonEmpty step state) =
    (iterate step nextState).getLast (iterateIsNonEmpty step _) := by
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
      rw [noneStep] at nextStateSome
      contradiction
  | case2 state newState nextStep =>
      simp [iterate_next_state nextStep,
        List.getLast_cons (iterateIsNonEmpty step _)]
      rw [nextStep] at nextStateSome
      simp at nextStateSome
      rw [nextStateSome]

lemma iterateTail {state: α}
    (nextStateSome: step.nextStep state = some nextState):
    iterate step nextState = (iterate step state).tail := by
  conv_lhs => unfold iterate
  conv_rhs => unfold iterate iterate
  rw [nextStateSome]
  simp

lemma iterateTailLast {state: α}:
    ∀ s ∈ (iterate step state),
      (iterate step state).getLast (iterateIsNonEmpty step state) =
      (iterate step s).getLast (iterateIsNonEmpty step s) := by
  intro s s_in_state
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
      have single_state := iterate_single_state noneStep
      simp_rw [single_state] at s_in_state ⊢
      simp at s_in_state ⊢
      simp [s_in_state, single_state]
  | case2 state nextState nextStep ih =>
      simp_rw [iterate_next_state nextStep] at s_in_state ⊢
      simp [List.getLast_cons (iterateIsNonEmpty step _)] at s_in_state ⊢
      rw [← iterate_nextStateLastIsSame nextStep] at ih ⊢
      rcases s_in_state with head | tail
      · rw [head]
      · specialize ih tail
        exact ih

lemma iterate_predecessor {state s: α}:
    s ∈ iterate step state → s ≠ state → ∃! t ∈ iterate step state, step.nextStep t = some s := by
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this]
    tauto
  | case2 state nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp_rw [this]
    simp [this]
    intro s_options
    rcases s_options with s_state | s_next
    · tauto
    · specialize ih s_next
      intro _
      by_cases h: s = nextState
      · use state
        simp
        rw [h]
        simp [nextStep]
        intros a nextState_le_a a_lt_nextState
        apply global_decreasing at nextState_le_a
        have := step.decreasing a (by simp [a_lt_nextState])
        simp [a_lt_nextState] at this
        omega
      · specialize ih h
        obtain ⟨t, t_cond, t_uniq⟩ := ih
        use t
        simp at t_uniq ⊢
        constructor
        · tauto
        · constructor
          · rw [nextStep]
            simp
            tauto
          · exact t_uniq

lemma iterate_ne_predecessor {s s_pred: α} {step: Terminator α} (h: step.nextStep s_pred = some s): s ≠ s_pred := by
  by_contra bad
  rw [← bad] at h
  have := step.decreasing s (by simp [h])
  simp [h] at this

lemma iterate_ne_s_le_s_pred {t s s_pred state: α}:
    t ∈ iterate step state → s_pred ∈ iterate step state →
    t ≠ s → step.nextStep s_pred = some s → s ∈ iterate step t → s_pred ∈ iterate step t := by
  intros t_in_state s_in_state t_ne_s s_pred_is_pred t_le_s
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this] at t_in_state s_in_state
    rw [← s_in_state] at noneStep
    rw [noneStep] at s_pred_is_pred
    contradiction
  | case2 state nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp [this] at t_in_state s_in_state
    rcases t_in_state with t_eq_state | t_nextState
    · rcases s_in_state with s_eq_state | s_nextState
      · rw [t_eq_state, s_eq_state]
        exact iterateReflexivity step state
      · rw [t_eq_state]
        apply iterateTransitivity
        exact iterateNextState nextStep
        exact s_nextState
    · specialize ih t_nextState
      rcases s_in_state with s_eq_state | s_nextState
      · rw [s_eq_state] at s_pred_is_pred
        rw [nextStep] at s_pred_is_pred
        simp at s_pred_is_pred
        clear ih
        rw [s_eq_state]
        rw [← s_pred_is_pred] at t_ne_s t_le_s
        clear s_eq_state s_pred_is_pred
        have t_nextState' := t_nextState
        apply global_decreasing at t_le_s
        apply global_decreasing at t_nextState'
        have: step.termination nextState = step.termination t := by omega
        apply termination_injective (iterateReflexivity step nextState) t_nextState at this
        exact False.elim (t_ne_s this.symm)
      · exact ih s_nextState

lemma last_occurrence {step: Terminator α} {state: α} (P: α → Prop)
    (ex: ∃ s ∈ iterate step state, P s):
    ∃ s ∈ iterate step state, P s ∧ ∀ t ∈ iterate step s, t ≠ s → ¬ P t := by
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this] at ex ⊢
    exact ex
  | case2 state nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp [this] at ex ⊢
    by_cases h: ∃ s ∈ iterate step nextState, P s  -- exists in tail ?
    · specialize ih h
      right
      exact ih
    · simp [h] at ex -- doesn't exist in tail, so must be the first element
      left
      push_neg at h
      exact ⟨ex, by tauto⟩

lemma stateInduction (step: Terminator α)
    (state: α) (P: α → Prop)
    (base: P state)
    (weak: ∀ s ∈ iterate step state,
        (nd: step.nextStep s ≠ ⊥) → P s → P ((step.nextStep s).unbot nd)):
    ∀ s ∈ iterate step state, P s := by
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this] at weak ⊢
    exact base
  | case2 state nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp [this] at weak ⊢
    simp [nextStep] at ih weak
    constructor
    · exact base
    · apply ih
      · exact weak.1 base
      · exact weak.2

lemma stateStrongInduction (step: Terminator α)
    (state: α) (P: α → Prop)
    (strong: (∀ s ∈ iterate step state,
        (∀ t ∈ iterate step state, s ≠ t ∧
          s ∈ iterate step t → P t) → P s)):
    ∀ s ∈ iterate step state, P s := by
  induction state using (iterate.induct' step) with
  | case1 state noneStep =>
    have := iterate_single_state noneStep
    simp [this] at strong ⊢
    exact strong
  | case2 state nextState nextStep ih =>
    have := iterate_next_state nextStep
    simp [this] at strong ⊢
    obtain ⟨strong1, strong2⟩ := strong
    constructor
    · apply strong1
      intro s hs _ c2
      apply global_decreasing at hs
      apply global_decreasing at c2
      have := step.decreasing state (by simp [nextStep])
      simp [nextStep] at this
      omega
    · apply ih
      intro s hs
      specialize strong2 s hs
      simp
      apply strong2
      intros _ _
      apply strong1
      intro a ha _ c2
      apply global_decreasing at ha
      apply global_decreasing at c2
      have := step.decreasing state (by simp [nextStep])
      simp [nextStep] at this
      omega
