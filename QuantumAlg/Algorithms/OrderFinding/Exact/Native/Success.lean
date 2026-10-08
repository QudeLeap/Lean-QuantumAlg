/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Distribution
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.SourceSupport
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Specification
import all QuantumAlg.Core.Measure.Distribution

/-!
# Exact-grid success of the actual native decoder

The decoded word is the image of the same measured source outcome. Its exact
dyadic success probability follows from the native Born support theorem.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

/-- Every valid native exact-dyadic instance returns an exact-grid word. -/
theorem successProbability_eq_one {N x t width r : Nat}
    (access : ModExpOracleAccess N x t width)
    (hinput : OrderFinding.Input N x r) (dyadic : r ∣ 2 ^ t)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model access).classicalOracles Sampling.Native.pre Reference) :
    ((run access).outputDistribution input).toOuterMeasure
      {output | SuccessfulOutcome r output} = 1 := by
  rw [outputDistribution_eq_source, PMF.toOuterMeasure_map_apply]
  have grid :
      (fun outcome => decodedValue (.bits outcome)) ⁻¹'
          {output | SuccessfulOutcome r output} =
        {outcome | OrderFinding.Native.ExactOutcome r t outcome} := by
    ext outcome
    rfl
  rw [grid]
  exact OrderFinding.Native.exactMeasurementModel hinput access dyadic

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
