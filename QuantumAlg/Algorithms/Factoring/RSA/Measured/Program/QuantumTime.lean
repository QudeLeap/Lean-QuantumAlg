/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Actual quantum-time upper bound from the independent native event allowance

The weighted native work bounds the actual scheduled dependency duration of
the same path. This is an upper bound and makes no depth-optimality claim
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution EkeraHastadStyle.Canonical

/-- Independent native quantum work bounds the actual schedule from above. -/
def quantumTimeLimit (N count : Nat) : Nat :=
  ResourcePool.weightedCount Resource.Event.quantumDuration (eventBudget N count)

/-- The actual complete run's quantum duration obeys that same independent allowance. -/
lemma rsaMeasuredParent_run_quantumTime_le
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
    (input : Input N) (large : 5 ≤ arithmeticBits N) (odd : Odd N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.quantumTime path ≤ quantumTimeLimit N count :=
  Circuit.depth_le_weightedCount_of_pool_le (run base noQuantum N input count).code
    Resource.Event.quantumDuration (eventBudget N count) path
    (rsaMeasuredParent_run_pool_le base noQuantum N input large odd count path)

end

end QuantumAlg.Factoring.RSA.Measured.Program
