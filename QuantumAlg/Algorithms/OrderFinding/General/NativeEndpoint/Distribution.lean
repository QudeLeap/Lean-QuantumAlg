/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Recovery.Stage
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native.Distribution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution
import all QuantumAlg.Core.Execution.MappedTail
import all QuantumAlg.Core.Execution.Probability

/-!
# Actual recovery as a deterministic tail of the source sample

The selected native recovery executes on the same retained store and service
state produced by the source sampler. This exposes the actual complete
execution as a map over the sampling records, including all caller histories.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution
open ClassicalRoutines.OrderRecovery.Native

/-- Extend each actual sampling record by its own finite recovery path. -/
def recoveredRecord {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (record : (SourceNativeSampling.run t width).Record) :
    (run spec t).Record :=
  ((recoveryStep spec t record.1).1,
    (record.2.1, (record.2.2.1,
      (record.2.2.2, (recoveryStep spec t record.1).2))))

/-- The final run maps the very same source-sample density blocks. -/
lemma execute_eq_map {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (environment : (Sampling.Native.model t width).Environment) (Reference : Register)
    (state : ExecutionState
      (Store (pre width) × (Sampling.Native.Framed.model t width).HiddenState)
      (Register.prod (pre width).register Reference)) :
    (run spec t).execute environment Reference state =
      ((SourceNativeSampling.run t width).execute environment Reference state).mapClassical
        (recoveredRecord spec t) := by
  refine (Circuit.execute_seq_retained_mapClassical_tail
    (model := Sampling.Native.Framed.model t width)
    (resultKey t width) (outputShape t) (resultFresh t width)
    (SourceNativeSampling.code t width) (recoveryStage spec t) environment
    (fun entry =>
      (((recoveryStep spec t entry.1).1, entry.2),
        (recoveryStep spec t entry.1).2))
    (recoveryStage_execute spec t environment) Reference
    (state.mapClassical (fun store => (store.1, (store.2, store.1))))).trans ?_
  exact congrArg (fun decision : DecidableEq (run spec t).Record =>
    @ExecutionState.mapClassical (SourceNativeSampling.run t width).Record
      (run spec t).Record _ _
      (Register.prod (SourceNativeSampling.post t width).register Reference) decision
      ((SourceNativeSampling.run t width).execute environment Reference state)
      (recoveredRecord spec t))
    (Subsingleton.elim _ _)

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
