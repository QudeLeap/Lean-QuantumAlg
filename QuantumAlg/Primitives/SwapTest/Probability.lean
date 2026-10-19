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
formula [BCWdW01, main.tex:287-329].
-/

namespace QuantumAlg.SwapTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

lemma code_one_mass (actual : model.Environment) {width : Nat} (left right : NormalizedVector
    (Qubits width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (promised : inputPromise left right state.quantumMarginal.marginalLeft) :
    ((((code width).execute actual Reference state).mapClassical
      (fun value => value.1.read
        (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))).block
      (.finite 1)).mass = probabilityOne left right := by
  let observed (output : State (post width) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × (code width).Path))) : Real :=
    ((output.mapClassical (fun value => value.1.read
      (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))).block (.finite 1)).mass
  have transfer := congrArg observed (code_execute width actual state)
  have mass := transfer.trans
    (HadamardTest.code_block_mass (swapRegistersOp width) (left.tensor right)
      state promised (.finite 1))
  change observed ((code width).execute actual Reference state) = _
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
lemma outputDistribution_one (actual : model.Environment) {width : Nat} (left right :
    NormalizedVector (Qubits width))
    {Reference : Register} (input : OracleInput .empty (pre width) Reference)
    (promised : inputPromise left right input.caller.localState.quantumMarginal) :
    (run width).outputDistribution actual input (.finite 1) =
      ENNReal.ofReal (probabilityOne left right) := by
  have measured := congrArg (fun distribution : PMF (CShape.Value (.finite 2)) =>
      distribution (.finite 1))
    (ExecutionState.toPMF_mapClassical ((run width).execute actual Reference input.state)
      ((run width).execute_normalized actual input) (run width).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine measured.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code width).execute actual Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      |>.mapClassical (fun value => value.1.read
        (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))
      |>.block (.finite 1)).mass) = _
  apply congrArg ENNReal.ofReal
  apply code_one_mass actual left right
  rw [ExecutionState.mapClassical_quantumMarginal,
    ← OracleInput.oracleInput_caller_quantumMarginal input, ← Input.localState_quantumMarginal]
  exact promised

/-- The relational success event is the same exact measured one-result probability. -/
lemma actual_success (actual : model.Environment) {width : Nat} (left right : NormalizedVector
    (Qubits width))
    {Reference : Register} (input : OracleInput .empty (pre width) Reference)
    (promised : inputPromise left right input.caller.localState.quantumMarginal) :
    ENNReal.ofReal (probabilityOne left right) =
      ((run width).relationalDistribution actual input).toOuterMeasure {pair | pair.2
        = .finite 1} := by
  have projection :
      ((run width).relationalDistribution actual input).toOuterMeasure {pair | pair.2 = .finite 1} =
        ((run width).outputDistribution actual input).toOuterMeasure
          {CShape.Value.finite (cardinality := 2) (1 : Fin 2)} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, PMF.toOuterMeasure_apply_singleton]
  exact (outputDistribution_one actual left right input promised).symm

end

end QuantumAlg.SwapTest
