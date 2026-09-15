/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.NumberTheory.Extended

/-!
# Prefix states of the original bounded extended-Euclidean trajectory

Every scheduled prefix is either an active pre-state or the final state of
the original run. A further genuine update belongs to that same list while
fuel remains. The original uniform coefficient theorem therefore supplies
all signed ranges needed by each actual loop step.
-/

namespace QuantumAlg.ClassicalAlgorithms.NumberTheory.XGCD

/-- Additional fuel leaves an already stopped original state unchanged. -/
theorem xgcdRun_of_stopped (fuel : Nat) (state : State) (stopped : state.first = 0) :
    run fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [run, if_pos stopped]

/-- Splitting the original fuel schedule composes the same terminating mathematical run. -/
theorem xgcdRun_add (first second : Nat) (state : State) :
    run (first + second) state = run second (run first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih =>
      by_cases stopped : state.first = 0
      · simp only [Nat.succ_add, run, if_pos stopped]
        exact (xgcdRun_of_stopped second state stopped).symm
      · simp only [Nat.succ_add, run, if_neg stopped]
        exact ih (step state)

/-- One additional public slot advances precisely when the current prefix is still active. -/
theorem xgcdRun_succ_last (fuel : Nat) (state : State) :
    run (fuel + 1) state =
      if (run fuel state).first = 0 then run fuel state else step (run fuel state) := by
  rw [xgcdRun_add]
  rfl

/-- Every bounded scheduled prefix occurs among the original active pre-states and final state. -/
theorem xgcdRun_prefix_mem (fuel index : Nat) (state : State) (within : index ≤ fuel) :
    run index state ∈ path fuel state ++ [run fuel state] := by
  induction fuel generalizing index state with
  | zero =>
      have same : index = 0 := by omega
      subst index
      simp only [run, path, List.nil_append, List.mem_singleton]
  | succ fuel ih =>
      by_cases stopped : state.first = 0
      · rw [xgcdRun_of_stopped index state stopped]
        simp only [path, if_pos stopped, run, List.nil_append, List.mem_singleton]
      · cases index with
        | zero =>
            simp only [run, path, if_neg stopped, List.cons_append,
              List.mem_cons, true_or]
        | succ index =>
            simp only [run, path, if_neg stopped, List.cons_append]
            exact List.mem_cons_of_mem state (ih index (step state) (by omega))

/-- A genuine next update with available fuel is another state of the same original trajectory. -/
theorem xgcdStep_run_mem (fuel index : Nat) (state : State) (within : index < fuel)
    (active : (run index state).first ≠ 0) :
    step (run index state) ∈ path fuel state ++ [run fuel state] := by
  have member := xgcdRun_prefix_mem fuel (index + 1) state (by omega)
  rw [xgcdRun_succ_last, if_neg active] at member
  exact member

/-- Every prefix of the original width-derived run lies in its original coefficient-bound domain. -/
theorem xgcdRun_initial_mem_executionStates {width : Nat} (input : Input width)
    (index : Nat) (within : index ≤ Euclid.gcdFuel width) :
    run index (initialState input) ∈ executionStates input :=
  xgcdRun_prefix_mem (Euclid.gcdFuel width) index (initialState input) within

/-- The next genuine prefix update stays inside the original fixed-width execution states. -/
theorem xgcdStep_run_initial_mem_executionStates {width : Nat} (input : Input width)
    (index : Nat) (within : index < Euclid.gcdFuel width)
    (active : (run index (initialState input)).first ≠ 0) :
    step (run index (initialState input)) ∈ executionStates input :=
  xgcdStep_run_mem (Euclid.gcdFuel width) index (initialState input) within active

/-- All four actual prefix coefficients satisfy the original uniform signed-width bounds. -/
theorem xgcdRun_initial_coefficients_representable {width : Nat} (input : Input width)
    (index : Nat) (within : index ≤ Euclid.gcdFuel width) :
    let current := run index (initialState input)
    signedRepresentable (executionCoefficientWidth width) current.firstLeftCoefficient ∧
      signedRepresentable (executionCoefficientWidth width) current.firstRightCoefficient ∧
      signedRepresentable (executionCoefficientWidth width) current.secondLeftCoefficient ∧
      signedRepresentable (executionCoefficientWidth width) current.secondRightCoefficient :=
  xgcdExecutionState_coefficients_representable input
    (xgcdRun_initial_mem_executionStates input index within)

/-- The two newly computed coefficients need no range promise beyond the original input and fuel. -/
theorem xgcdStep_run_initial_coefficients_representable {width : Nat} (input : Input width)
    (index : Nat) (within : index < Euclid.gcdFuel width)
    (active : (run index (initialState input)).first ≠ 0) :
    let next := step (run index (initialState input))
    signedRepresentable (executionCoefficientWidth width) next.firstLeftCoefficient ∧
      signedRepresentable (executionCoefficientWidth width) next.firstRightCoefficient ∧
      signedRepresentable (executionCoefficientWidth width) next.secondLeftCoefficient ∧
      signedRepresentable (executionCoefficientWidth width) next.secondRightCoefficient :=
  xgcdExecutionState_coefficients_representable input
    (xgcdStep_run_initial_mem_executionStates input index within active)

end QuantumAlg.ClassicalAlgorithms.NumberTheory.XGCD
