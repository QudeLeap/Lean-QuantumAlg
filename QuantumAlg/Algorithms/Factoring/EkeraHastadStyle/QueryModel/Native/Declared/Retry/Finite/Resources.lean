/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Space

/-!
# Independent scalar allowances and fixed EH storage

Zero count uses one initialized optional result and no event. Positive
storage keeps the same original-width bank, sample slots and selector,
including the caller's original resident and auxiliary roles. The event
and duration templates charge every batch and one final result pack;
completed execution composes separate per-batch pack and reset allowances.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable {N : Nat}

/-- Zero emits no native event; positive counts pay for every actual declared retry stage. -/
def eventBudget (input : Input N) : Nat → ResourcePool (model input)
  | 0 => 0
  | laterCount + 1 => Retry.eventBudget input laterCount

/-- Every positive branch retains its original dependency allowance for arbitrary durations. -/
def durationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat → Nat
  | 0 => 0
  | laterCount + 1 => Retry.durationBudget input laterCount duration

/-- The independent zero allowance is one optional word; positive counts share fixed storage. -/
def additionalSpace (N : Nat) : Nat → SpacePool .quantum
  | 0 => SpacePool.ofShape (.option (.unsignedWord (modulusBits N)))
  | _ + 1 => Retry.additionalSpace N

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
