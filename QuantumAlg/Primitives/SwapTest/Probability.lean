/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.SwapTest.Execution
import all QuantumAlg.Primitives.SwapTest.Specification
import all QuantumAlg.Primitives.SwapTest.Basic
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Probability
import all QuantumAlg.Primitives.HadamardTest.Preparation
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Exact probability of the actual stored SWAP-test outcome

The elementary program has the complete source experiment's execution state.
Summing its actual measured-result fiber preserves the original exact overlap
formula [BCWdW01, main.tex:287-328].
-/

namespace QuantumAlg.SwapTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

theorem code_one_mass {width : Nat} (left right : NormalizedVector (Qubits width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference History)
    (promised : inputPromise left right state.quantumMarginal.marginalLeft) :
    ((((code width).execute Reference state).mapClassical
      (fun value => value.1.read
        (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))).block
      (.finite 1)).mass = probabilityOne left right := by
  let observed (output : State (post width) Reference (History × (code width).Path)) : Real :=
    ((output.mapClassical (fun value => value.1.read
      (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))).block (.finite 1)).mass
  have transfer := congrArg observed (code_execute width state)
  have mass := transfer.trans
    (HadamardTest.code_block_mass (swapRegistersOp width) (left.tensor right)
      state promised (.finite 1))
  change observed ((code width).execute Reference state) = _
  rw [mass]
  let evolved := HadamardTest.evolvedState (swapRegistersOp width) (left.tensor right)
  let fiber (basis : Fin (2 ^ (1 + (width + width)))) : Real :=
    if CShape.Value.finite (cardinality := 2)
      ((prodEquiv (m := 1) (n := width + width)).symm basis).1 =
        CShape.Value.finite (cardinality := 2) (1 : Fin 2) then ‖evolved basis‖ ^ 2 else 0
  change (∑ basis, fiber basis) = _
  calc
    _ = ∑ pair : Fin (2 ^ 1) × Fin (2 ^ (width + width)), fiber (prodEquiv pair) :=
      ((prodEquiv (m := 1) (n := width + width)).sum_comp fiber).symm
    _ = evolved.probQubit0 1 := by
      change _ = ∑ value : Fin (2 ^ (width + width)), ‖evolved (prodEquiv (1, value))‖ ^ 2
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro value _
      change (∑ controlValue : Fin 2, fiber (prodEquiv (controlValue, value))) = _
      rw [Fin.sum_univ_two]
      have different : CShape.Value.finite (cardinality := 2) (0 : Fin 2) ≠
          CShape.Value.finite (cardinality := 2) (1 : Fin 2) := by decide
      simp only [fiber, Equiv.symm_apply_apply, different, if_false, if_true, zero_add]
    _ = _ :=
      (hadamardTest_probQubit0_one (U := swapRegistersOp width) (left.tensor right)).trans
        (congrArg (fun value : Real => (1 - value) / 2) (re_inner_swapRegisters left right))

/-- The complete run reads its actual binary cell with exactly the source probability. -/
theorem outputDistribution_one {width : Nat} (left right : NormalizedVector (Qubits width))
    {Reference : Register} (input : Input (pre width) Reference)
    (promised : inputPromise left right input.localState.quantumMarginal) :
    (run width).outputDistribution input (.finite 1) =
      ENNReal.ofReal (probabilityOne left right) := by
  have actual := congrArg (fun distribution : PMF (CShape.Value (.finite 2)) =>
      distribution (.finite 1))
    (ExecutionState.toPMF_mapClassical ((run width).execute Reference input.state)
      ((run width).execute_normalized input) (run width).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code width).execute Reference (input.state.mapClassical (fun store => (store, store)))
      |>.mapClassical (fun value => value.1.read
        (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))
      |>.block (.finite 1)).mass) = _
  apply congrArg ENNReal.ofReal
  apply code_one_mass left right
  rw [ExecutionState.mapClassical_quantumMarginal, ← Input.localState_quantumMarginal]
  exact promised

/-- The relational success event is the same exact measured one-result probability. -/
theorem actual_success {width : Nat} (left right : NormalizedVector (Qubits width))
    {Reference : Register} (input : Input (pre width) Reference)
    (promised : inputPromise left right input.localState.quantumMarginal) :
    ENNReal.ofReal (probabilityOne left right) =
      ((run width).relationalDistribution input).toOuterMeasure {pair | pair.2 = .finite 1} := by
  have projection :
      ((run width).relationalDistribution input).toOuterMeasure {pair | pair.2 = .finite 1} =
        ((run width).outputDistribution input).toOuterMeasure
          {CShape.Value.finite (cardinality := 2) (1 : Fin 2)} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, PMF.toOuterMeasure_apply_singleton]
  exact (outputDistribution_one left right input promised).symm

end

end QuantumAlg.SwapTest
