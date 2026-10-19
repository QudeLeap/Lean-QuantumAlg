/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Runtime.Frame
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Execute the complete native arithmetic beside retained payload

The native gate addresses select their matching physical wires in the full
prepared context. Zero allocation and literal fixed-seed X gates precede the
body; all supplied payload bits remain live throughout the same execution
[LYL+26, sec_EEA/sub_regshare.tex:16-26].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PayloadRuntime

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

variable {runtimeEnvironment :
  (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution PayloadPreparation

/-- The actual native body on the entire prepared physical frame. -/
def program (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source width payloadWidth)) :
    UnitaryCircuit AlgorithmGate.model .empty (after width payloadWidth).quantumLayout :=
  PayloadRuntimeFrame.program width payloadWidth body

lemma payloadRuntime_program_eventTrace (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source width payloadWidth)) :
    (program width payloadWidth body).eventTrace = body.eventTrace :=
  PayloadRuntimeFrame.program_eventTrace width payloadWidth body

lemma payloadRuntime_program_eventCost (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source width payloadWidth)) :
    (program width payloadWidth body).eventCost = body.eventCost :=
  PayloadRuntimeFrame.program_eventCost width payloadWidth body

lemma payloadRuntime_program_depth (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source width payloadWidth))
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (program width payloadWidth body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration :=
  UnitaryCircuit.placeAt_evaluatedEventDepth
    (PayloadRuntimeFrame.source width payloadWidth) (after width payloadWidth).quantumLayout
    (PayloadRuntimeFrame.position width payloadWidth)
    (PayloadRuntimeFrame.position_dimensions width payloadWidth) duration body

/-- The native basis action is preserved at every physical coordinate. -/
lemma payloadRuntime_program_apply_ket (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source width payloadWidth))
    (input output : (PayloadRuntimeFrame.source width payloadWidth).Basis)
    (action : body.applyNormalized environment (NormalizedVector.ket input) =
      NormalizedVector.ket output)
    (targetInput targetOutput : (after width payloadWidth).register.Index)
    (inputSelected : UnitaryCircuit.selectedInput
      (PayloadRuntimeFrame.source width payloadWidth)
      (after width payloadWidth).quantumLayout
      (PayloadRuntimeFrame.position width payloadWidth)
      (PayloadRuntimeFrame.position_dimensions width payloadWidth) targetInput = input)
    (outputSelected : UnitaryCircuit.selectedInput
      (PayloadRuntimeFrame.source width payloadWidth)
      (after width payloadWidth).quantumLayout
      (PayloadRuntimeFrame.position width payloadWidth)
      (PayloadRuntimeFrame.position_dimensions width payloadWidth) targetOutput = output) :
    (program width payloadWidth body).applyNormalized environment (NormalizedVector.ket
      targetInput) =
      NormalizedVector.ket targetOutput :=
  PayloadRuntimeFrame.program_apply_ket width payloadWidth body input output action
    targetInput targetOutput inputSelected outputSelected

/-- One current-model instruction runs the complete placed body. -/
def circuit (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source width payloadWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (after width payloadWidth) (after width payloadWidth) :=
  .unitary (program width payloadWidth body)

variable {Reference : Register} {H : Type} [Fintype H]

lemma payloadRuntime_circuit_block_matrix (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source width payloadWidth))
    (state : State (after width payloadWidth) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (store : Store (after width payloadWidth))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : H) :
    (((circuit width payloadWidth body).execute runtimeEnvironment Reference state).block
      (store, (hidden, (history, ())))).matrix =
      let operator := UnitaryOperator.prodTensor ((program width payloadWidth body).matrix
        runtimeEnvironment.quantum)
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator ((after width payloadWidth).register.prod Reference)) *
        (state.block (store, (hidden, history))).matrix *
          (operator : HilbertOperator
            ((after width payloadWidth).register.prod Reference)).conjTranspose :=
  PayloadRuntimeFrame.circuit_block_matrix width payloadWidth body state store hidden history

/-- One physical preparation followed by the supplied native body. -/
def code (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (before modulus.size payloadWidth) (after modulus.size payloadWidth) :=
  (PayloadPreparation.circuit modulus payloadWidth).seq
    (circuit modulus.size payloadWidth body)

lemma payloadRuntime_code_eventTrace (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth))
    (path : (code modulus payloadWidth body).Path) :
    (code modulus payloadWidth body).eventTrace path =
      (ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
        (PayloadPreparation.loadProgram modulus payloadWidth).eventTrace) ++
        body.eventTrace := by
  change (PayloadPreparation.circuit modulus payloadWidth).eventTrace path.1 ++
    (program modulus.size payloadWidth body).eventTrace = _
  rw [PayloadPreparation.payloadPreparation_circuit_eventTrace,
    payloadRuntime_program_eventTrace]

lemma payloadRuntime_code_resourcePool (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth))
    (path : (code modulus payloadWidth body).Path) :
    (code modulus payloadWidth body).resourcePool path =
      ZeroPreparation.eventCost AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) +
      (PayloadPreparation.loadProgram modulus payloadWidth).eventCost + body.eventCost := by
  change ResourcePool.ofList ((code modulus payloadWidth body).eventTrace path) = _
  rw [payloadRuntime_code_eventTrace, ResourcePool.ofList_append,
    ResourcePool.ofList_append]
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  rfl

lemma payloadRuntime_code_depth (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth))
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (code modulus payloadWidth body).Path) :
    (code modulus payloadWidth body).depth duration path =
      DepthExpr.depthEval duration
        (ZeroPreparation.eventDepth AlgorithmGate.model .empty
          (InputPreparation.auxiliaryLayout modulus.size)) +
      (PayloadPreparation.loadProgram modulus payloadWidth).evaluatedEventDepth duration +
      body.evaluatedEventDepth duration := by
  change DepthExpr.depthEval duration
      (ZeroPreparation.eventDepth AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size)) +
    (PayloadPreparation.loadProgram modulus payloadWidth).evaluatedEventDepth duration +
    (program modulus.size payloadWidth body).evaluatedEventDepth duration = _
  rw [payloadRuntime_program_depth]

lemma payloadRuntime_code_visitedContexts (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth))
    (path : (code modulus payloadWidth body).Path) :
    (code modulus payloadWidth body).visitedContexts path =
      [before modulus.size payloadWidth, after modulus.size payloadWidth,
        after modulus.size payloadWidth, after modulus.size payloadWidth] := rfl

private lemma input_le (width payloadWidth : Nat) :
    OwnedQubits.space (width + payloadWidth) ≤
      OwnedQubits.space (frameEncoding width payloadWidth).width := by
  have count : width + payloadWidth ≤ (frameEncoding width payloadWidth).width := by
    have complete := payloadPreparation_total_width width payloadWidth
    omega
  intro axis
  cases axis with
  | classicalBits => exact le_rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then _ else 0) ≤
        if (2 : ℕ+) = dimension then _ else 0
      split_ifs
      · exact count
      · exact le_rfl

lemma payloadRuntime_code_resident (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth))
    (path : (code modulus payloadWidth body).Path) :
    (code modulus payloadWidth body).peakResidentSpace path ≤
      OwnedQubits.space (frameEncoding modulus.size payloadWidth).width := by
  unfold Circuit.peakResidentSpace
  rw [payloadRuntime_code_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil,
    payloadPreparation_after_resident, SpacePool.max_zero, SpacePool.max_self,
    payloadPreparation_before_resident]
  exact SpacePool.max_le (input_le modulus.size payloadWidth) le_rfl

lemma payloadRuntime_code_auxiliary (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth))
    (path : (code modulus payloadWidth body).Path) :
    (code modulus payloadWidth body).peakAuxiliarySpace path ≤
      OwnedQubits.space (frameEncoding modulus.size payloadWidth).width := by
  unfold Circuit.peakAuxiliarySpace
  rw [payloadRuntime_code_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil,
    payloadPreparation_after_auxiliary, SpacePool.max_zero, SpacePool.max_self,
    payloadPreparation_before_auxiliary]
  exact SpacePool.max_le (input_le modulus.size payloadWidth) le_rfl

lemma payloadRuntime_code_quantumMarginal (modulus payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (PayloadRuntimeFrame.source modulus.size payloadWidth))
    (state : State (before modulus.size payloadWidth) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((code modulus payloadWidth body).execute runtimeEnvironment Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor ((program modulus.size payloadWidth body).matrix
          runtimeEnvironment.quantum)
          (1 : UnitaryOperator Reference))
        ((PayloadPreparation.circuit modulus payloadWidth).execute runtimeEnvironment
          Reference state).quantumMarginal := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal, circuit,
    Circuit.unitary_jointDensity]

end

end QuantumAlg.MAU.Inversion.SharedEEA.PayloadRuntime
