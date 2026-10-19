/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Endpoint
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA2048.Recycling.Resources
import all QuantumAlg.Algorithms.Factoring.RSA2048.Recycling.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Calibration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context

/-!
# Fixed-width conditional-success calibration

The original good-key model calibrates the canonical complete seven-batch
problem. Native resource bounds remain separate exact-width results without
a good-key hypothesis. The seven-batch conditional floor is unchanged.
-/

namespace QuantumAlg.Factoring.RSA2048.Recycling

noncomputable section

open Execution
open EkeraHastadStyle.Canonical

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The original fixed seven-batch conditional floor is at least 99 percent. -/
lemma model_successFloor_ge_99
    (environment : ShortDLP.CompiledMAU.Recycling.model.Environment) (model :
      NativeRSA2048.FixedKeyModel N) :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      ((RSA.Recycling.Program.fixedRoundProblem
        base noQuantum N NativeRSA2048.rounds).successLB environment model.1).value := by
  change ENNReal.ofReal ((99 : Real) / 100) ≤
    1 - NativeFiniteRetry.Calibration.batchFailure model.1.bitWidth ^ NativeRSA2048.rounds
  rw [model.2]
  exact NativeRSA2048.Calibration.conditionalSuccess_seven_ge_99

end

end QuantumAlg.Factoring.RSA2048.Recycling
