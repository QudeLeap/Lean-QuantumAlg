/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Repeated
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.State.Readout

/-!
# Full output-state promise for the completed EH batch schedule

The proved joint matrix entry is transported through the generic readout
bridge with the concrete run sealed at this boundary. This prevents the
kernel from repeatedly expanding the complete finite circuit while checking
the dependent final-state type.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private irreducible_def sealedRun (laterCount : Nat) : AlgorithmRun (model input) base
    (Retry.context base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N) :=
  completedRun base noQuantum N input laterCount

private theorem sealedRun_code (laterCount : Nat) :
    (sealedRun base noQuantum N input laterCount).code =
      completedCode base noQuantum N input laterCount := by
  rw [sealedRun_def]
  exact completedRun_code base noQuantum N input laterCount

private theorem sealedRun_output (laterCount : Nat) :
    (sealedRun base noQuantum N input laterCount).output =
      (completedRun base noQuantum N input laterCount).output := by
  rw [sealedRun_def]

set_option Elab.async false in
private theorem sealed_statePromise (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed
      (BasisReference.target (R := (Retry.context base noQuantum N).register)
        (Retry.context base noQuantum N).quantumLayout.zeroLabel
        original.caller.state.referenceMarginal)
      (BasisReference.target_normalized
        (R := (Retry.context base noQuantum N).register)
        (Retry.context base noQuantum N).quantumLayout.zeroLabel
        original.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass original.caller.state).trans
          original.caller.normalized))).Holds
      ((ExecutionState.mapClassical
        ((sealedRun base noQuantum N input laterCount).finalState Reference original.state)
        (sealedRun base noQuantum N input laterCount).output.eval).block value) := by
  apply AlgorithmRun.basisReference_readout_of_executionEntries
    (sealedRun base noQuantum N input laterCount)
    (Retry.context base noQuantum N).quantumLayout.zeroLabel
    (Optional.Distribution.selectedDistribution
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
      (laterCount + 1)) _ original value
  intro reference history _ state normalized output left right leftRef rightRef
  rw [sealedRun_code, sealedRun_output]
  exact completed_joint_entry base noQuantum N input laterCount
    state normalized output left right leftRef rightRef

private theorem sealedReadout_eq (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (ExecutionState.mapClassical
      ((sealedRun base noQuantum N input laterCount).finalState Reference original.state)
      (sealedRun base noQuantum N input laterCount).output.eval).block value =
    (ExecutionState.mapClassical
      ((completedRun base noQuantum N input laterCount).finalState Reference original.state)
      (completedRun base noQuantum N input laterCount).output.eval).block value := by
  rw [sealedRun_def]

/-- The actual completed execution has the same full zero-bank/reference
promise at each output as the preserved positive finite run. -/
theorem completed_statePromise (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed
      (BasisReference.target (R := (Retry.context base noQuantum N).register)
        (Retry.context base noQuantum N).quantumLayout.zeroLabel
        original.caller.state.referenceMarginal)
      (BasisReference.target_normalized
        (R := (Retry.context base noQuantum N).register)
        (Retry.context base noQuantum N).quantumLayout.zeroLabel
        original.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass original.caller.state).trans
          original.caller.normalized))).Holds
      ((ExecutionState.mapClassical
        ((completedRun base noQuantum N input laterCount).finalState Reference original.state)
        (completedRun base noQuantum N input laterCount).output.eval).block value) := by
  have canonical := sealed_statePromise base noQuantum N input laterCount original value
  rw [sealedReadout_eq base noQuantum N input laterCount original value] at canonical
  exact canonical

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
