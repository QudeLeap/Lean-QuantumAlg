/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Recovery
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store
import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Core.Execution.Reference.Support

/-!
# Actual full recovery transports the complete parent Store on its real source support

The native recovery keeps its lexical allocation, all pair computations,
original early-factor precedence and emitted record. Source agreement is
established by the actual preceding source program. On that actual support,
the recovered factor and every other parent cell have the original value
[EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

open Execution ClassicalRoutines EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {outer inner : RuntimeCtx .quantum} {N additionalMembers : Nat}

/-- Structural transport leaves every original terminal bit and complete batch value unchanged. -/
lemma rsaMeasuredParent_recovery_batchValue_transport
    (transport : ClassicalWorkspace.Transport outer inner)
    (sample : Fin (2 ^ residueSamplingBits N))
    (terminals : LatticePairRecoveryBatch.Terminals outer N additionalMembers)
    (before : Store inner) :
    LatticeFixedBatchRecoveryMachine.batchValue sample
      (fun index => transport.liftInput (terminals index)) before =
      LatticeFixedBatchRecoveryMachine.batchValue sample terminals (transport.restrict before) := by
  unfold LatticeFixedBatchRecoveryMachine.batchValue
  congr 2
  apply List.Vector.ext
  intro index
  simp only [LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map,
    List.Vector.get_ofFn]
  congr 1
  funext bit
  unfold BatchMachine.sourceBits
  exact congrArg CShape.Value.toBool
    (transport.workspaceTransport_restrict_readsAs before (.bitsGet (terminals index) bit))

/-- The complete actual recovery record writes exactly its original parent factor destination. -/
lemma rsaMeasuredParent_recovery_record_restrict
    (transport : ClassicalWorkspace.Transport outer inner) (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (parameter : CInputRef outer (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals outer N additionalMembers)
    (result : CWriteRef outer (LatticeBatchRecoveryOutput.OutputShape N)) (before : Store inner)
    (agrees : (transport.restrict before).read parameter = parameterValue input sample) :
    transport.restrict
      (LatticeFixedBatchRecoveryMachine.step (model := MeasuredRSAModel) input
        (transport.liftInput parameter) (fun index => transport.liftInput (terminals index))
        (transport.liftWrite result) before).1 =
      (transport.restrict before).write result
        (LatticeFixedBatchRecoveryMachine.batchValue sample terminals
          (transport.restrict before)) := by
  let actual := LatticeFixedBatchRecoveryMachine.step (model := MeasuredRSAModel) input
    (transport.liftInput parameter) (fun index => transport.liftInput (terminals index))
    (transport.liftWrite result) before
  have correct := LatticeFixedBatchRecoveryMachine.into_correct (model := MeasuredRSAModel)
    input sample (transport.liftInput parameter)
    (fun index => transport.liftInput (terminals index)) (transport.liftWrite result) before
    ⟨(transport.workspaceTransport_restrict_readsAs before parameter).trans agrees⟩
  apply Store.store_eq_write_of_read_frame (transport.restrict before)
    (transport.restrict actual.1) result _
  · exact ((transport.workspaceTransport_restrict_readsAs actual.1
      (.storage result.toCStorageRef)).symm.trans correct.output).trans
        (rsaMeasuredParent_recovery_batchValue_transport transport sample terminals before)
  · intro shape other different
    have avoids : (transport.liftWrite result).key ∉
        (transport.liftInput (.storage other)).storageKeys := by
      simpa only [ClassicalWorkspace.Transport.liftWrite_key,
        ClassicalWorkspace.Transport.liftInput_storageKeys,
        CInputRef.storageKeys, List.mem_singleton] using different
    exact (transport.workspaceTransport_restrict_readsAs actual.1 (.storage other)).symm.trans
      ((correct.callerFrame (transport.liftInput (.storage other)) avoids).trans
        (transport.workspaceTransport_restrict_readsAs before (.storage other)))

/-- Real recovery transports parent/reference weights through its factor write on actual support. -/
lemma rsaMeasuredParent_recovery_parent_referenceFiberSum
    (transport : ClassicalWorkspace.Transport outer inner) (input : Input N)
    (sampleOf : Store outer → Fin (2 ^ residueSamplingBits N))
    (parameter : CInputRef outer (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals outer N additionalMembers)
    (result : CWriteRef outer (LatticeBatchRecoveryOutput.OutputShape N))
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State inner Reference (MeasuredRSAModel.HiddenState × History))
    (admitted : ∀ record, 0 < (state.block record).mass →
      (transport.restrict record.1).read parameter =
        parameterValue input (sampleOf (transport.restrict record.1)))
    (weight : Store outer → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((LatticeFixedBatchRecoveryMachine.into (model := MeasuredRSAModel) inner input
        (transport.liftInput parameter) (fun index => transport.liftInput (terminals index))
        (transport.liftWrite result)).execute environment Reference state)
      (fun entry _ => weight (transport.restrict entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight ((transport.restrict entry.1).write result
          (LatticeFixedBatchRecoveryMachine.batchValue (sampleOf (transport.restrict entry.1))
            terminals (transport.restrict entry.1)))) left right := by
  rw [LatticeFixedBatchRecoveryMachine.into_execute,
    ExecutionState.referenceFiberSum_mapClassical]
  apply ExecutionState.referenceFiberSum_congr_on_positive
  intro record positive _basis
  exact congrArg weight (rsaMeasuredParent_recovery_record_restrict transport input
    (sampleOf (transport.restrict record.1)) parameter terminals result record.1
      (admitted record positive))

end

end QuantumAlg.Factoring.RSA.Measured.Program
