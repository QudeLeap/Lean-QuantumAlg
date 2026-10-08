/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.SelectionAll.Reference

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.State.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Readout

/-!
# Completed-batch full-state requirement

The completed schedule has the same complete bank/reference promise at its
retained factor readout as the original finite schedule.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

theorem completed_stateRequirement_holds (input : Input N) (laterCount : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    (stateRequirement base noQuantum N (laterCount + 1)).Holds original.caller
      ((completedRun base noQuantum N input laterCount).finalState Reference original.state) := by
  intro value
  have canonical :
      (StatePromise.mixed (stateTarget base noQuantum N original.caller)
        (stateTarget_normalized base noQuantum N original.caller)).Holds
        ((ExecutionState.mapClassical
          ((completedRun base noQuantum N input laterCount).finalState Reference original.state)
          (completedRun base noQuantum N input laterCount).output.eval).block value) := by
    simpa only [stateTarget, RuntimeCtx.register] using
      (completed_statePromise base noQuantum N input laterCount original value)
  apply StatePromise.mixed_fullSelection
    (Retry.context base noQuantum N).quantumLayout Reference
    (stateTarget base noQuantum N original.caller)
    (stateTarget_normalized base noQuantum N original.caller) _
  exact canonical

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
