/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.State.Body
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Construction
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Input.Oracle

/-!
# Complete actual semiclassical Fourier output requirements

The actual retained-cell allocation, identity-placed fine native body and
original run histories are followed through the one interpreter. All input
quantum-reference states are admitted. The full bank-reference density equals
the independent dephased Fourier target, while each actual stored vector
selects its own pure physical bank at the original outcome probability mass.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma allocated_basis_label (n : Nat) (basis : (inputContext n).register.Index) :
    outputBasisEquiv n (MeasurementCells.basisEquiv (inputContext n) 2 n basis) =
      inputBasisEquiv n basis := by
  apply congrArg (BinaryBasis.bigEndianEquiv n)
  funext i
  apply Fin.ext
  let before := (basisOfEqualWires (bankLayout n) (inputContext n).quantumLayout
    (qftSemiclassical_input_wires n)).symm basis
  let after := (basisOfEqualWires (bankLayout n) (outputContext n).quantumLayout
    (qftSemiclassical_output_wires n)).symm
      (MeasurementCells.basisEquiv (inputContext n) 2 n basis)
  have beforeValue := basisOfEqualWires_value (bankLayout n) (inputContext n).quantumLayout
    (qftSemiclassical_input_wires n) before i
  have afterValue := basisOfEqualWires_value (bankLayout n) (outputContext n).quantumLayout
    (qftSemiclassical_output_wires n) after i
  have samePosition : MeasurementCells.wireEquiv (inputContext n) 2 n
      (positionsOfEqualWires (bankLayout n) (inputContext n).quantumLayout
        (qftSemiclassical_input_wires n) i) =
      positionsOfEqualWires (bankLayout n) (outputContext n).quantumLayout
        (qftSemiclassical_output_wires n) i := by
    apply Fin.ext
    exact MeasurementCells.wireEquiv_val (inputContext n) 2 n _
  have preserved := MeasurementCells.basisEquiv_value (inputContext n) 2 n basis
    (positionsOfEqualWires (bankLayout n) (inputContext n).quantumLayout
      (qftSemiclassical_input_wires n) i)
  rw [samePosition] at preserved
  simp only [before, after, Equiv.apply_symm_apply] at beforeValue afterValue
  exact afterValue.symm.trans (preserved.trans beforeValue)

private lemma allocated_joint_basis (n : Nat) (Reference : Register) :
    (MeasurementCells.jointBasisEquiv (inputContext n) 2 n Reference).trans
        (outputJointBasis n Reference) =
      (inputBasisEquiv n).prodCongr (Equiv.refl Reference.Index) := by
  ext basis
  exact Prod.ext (allocated_basis_label n basis.1) rfl

/-- The original input Store is retained only as the run's existing mathematical history. -/
def recordedInput (n : Nat) {Reference : Register}
    (input : OracleInput .empty (inputContext n) Reference) :
    State (inputContext n) Reference
      (ClassicalOracleModel.empty.HiddenState × Store (inputContext n)) :=
  input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))

/-- Execute the endpoint's actual retained-cell allocator before the same fine body. -/
def allocatedInput {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (n : Nat) {Reference : Register}
    (input : OracleInput .empty (inputContext n) Reference) :
    State (outputContext n) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (Store (inputContext n) × (MeasurementCells.allocate
          (model := model) (inputContext n) 2 n).Path)) :=
  ((MeasurementCells.allocate (model := model) (inputContext n) 2 n).execute environment)
    Reference (recordedInput n input)

/-- Actual allocation preserves the complete binary bank-reference input density. -/
lemma allocatedInput_binary {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (n : Nat) {Reference : Register}
    (input : OracleInput .empty (inputContext n) Reference) :
    (allocatedInput (environment := environment) n input).quantumMarginal.reindex
      (outputJointBasis n Reference) =
      binaryInput n Reference input.caller := by
  have allocated : (allocatedInput (environment := environment) n input).quantumMarginal =
      (recordedInput n input).quantumMarginal.reindex
        (S := (outputContext n).register.prod Reference)
        (MeasurementCells.jointBasisEquiv (inputContext n) 2 n Reference) :=
    MeasurementCells.allocate_quantumMarginal (model := model) environment
      (inputContext n) 2 n (recordedInput n input)
  rw [allocated, DensityOperator.reindex_trans, allocated_joint_basis]
  unfold recordedInput binaryInput
  simp only [ExecutionState.mapClassical_quantumMarginal, OracleInput.caller]

/-- All actual final stores of the full parent are precisely those produced by its placed body. -/
lemma algorithm_finalState {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (inverse : Bool) (n : Nat) {Reference : Register}
    (input : OracleInput .empty (inputContext n) Reference) :
    ((algorithm inverse n).run.finalState environment) Reference input.state =
      (((body inverse n).execute environment) Reference (allocatedInput
        (environment := environment) n input)).mapClassical Prod.fst := by
  change ((((MeasurementCells.allocate (model := model) (inputContext n) 2 n).seq
    (Circuit.embed (ContextEmbedding.identity (outputContext n)) (body inverse n))).execute
      environment)
      Reference (recordedInput n input)).mapClassical Prod.fst = _
  rw [Circuit.execute_seq, Circuit.execute_identity_embed]
  unfold State.mapHistory
  refine (ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance) _ _ _).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  rfl

/-- The complete real run has the full independent no-SWAP Fourier instrument density. -/
lemma algorithm_jointState {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (inverse : Bool) (n : Nat) {Reference : Register}
    (input : OracleInput .empty (inputContext n) Reference) :
    (((algorithm inverse n).run.finalState environment) Reference input.state).quantumMarginal =
      idealOutputState inverse n Reference input.caller := by
  rw [algorithm_finalState, ExecutionState.mapClassical_quantumMarginal, body_quantumMarginal]
  unfold bodyIdealState
  rw [allocatedInput_binary]
  rfl

/-- The unit observation retains the complete output bank jointly with the arbitrary reference. -/
lemma algorithm_instrumentRequirement {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat) {Reference :
    Register}
    (input : OracleInput .empty (inputContext n) Reference) :
    (instrumentRequirement inverse n).Holds input.caller
      (((algorithm inverse n).run.finalState environment) Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (targetState inverse n Reference input.caller) _).Holds
        (DensityOperator.observeSelectionWithReference (outputContext n).quantumLayout
          Finset.univ Reference
          (((((algorithm inverse n).run.finalState environment) Reference input.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block, algorithm_jointState]
      change (targetState inverse n Reference input.caller).matrix =
        (targetState inverse n Reference input.caller).mass •
          (targetState inverse n Reference input.caller).matrix
      rw [targetState_normalized, one_smul]

/-- The required pure ket is conditioned on precisely the actual retained-cell vector. -/
lemma algorithm_storedResultRequirement {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat) {Reference :
    Register}
    (input : OracleInput .empty (inputContext n) Reference) :
    (storedResultRequirement n).Holds input.caller
      (((algorithm inverse n).run.finalState environment) Reference input.state) := by
  rw [algorithm_finalState]
  unfold storedResultRequirement StateRequirement.Holds
  intro value
  rw [ExecutionState.executionState_mapClassical_comp]
  exact body_result_pure inverse n (allocatedInput (environment := environment) n input) value

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
