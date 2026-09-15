/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Distribution

/-!
# Original sample distribution at empty input

The empty-input endpoint specializes the single Framed sampler.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

open QuantumAlg.Execution

/-- The original Born distribution is derived from the same actual run. -/
theorem outputDistribution_eq {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (run A).outputDistribution input =
      ((measurement t n).outcomePMF (BornBridge.evolvedState A)).map CShape.Value.bits :=
  Framed.outputDistribution_eq pre pre_quantumWires A input

end

end QuantumAlg.OrderFinding.Sampling
