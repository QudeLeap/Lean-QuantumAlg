/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.InputProtocol
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Classical
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.ReuseBoundary
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint

/-!
# Independent native factoring batch depth

The first and reused batches retain their complete unit-event allowances.
Zero trials remain an actual event-free classical execution.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.Finite

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {N : Nat}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

lemma emptyClassical : Circuit.IsClassical (NativeRetryEmpty.code base N) := by
  intro path event present
  rw [NativeRetryEmpty.code_eventTrace] at present
  exact False.elim (List.not_mem_nil present)

/-- Independent ceiling for either the first or a reused complete batch. -/
def batchDepthBound (N : Nat) : Nat :=
  max (NativeBatchRecovery.depthBound N) (NativeBatchReuseRecovery.depthBound N)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.Finite
