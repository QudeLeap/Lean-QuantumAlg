/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Distribution
import all QuantumAlg.Core.Execution.Retained.Distribution

/-!
# Full-record PMF after the actual recovery tail

The selected-model execution carries the actual sample's weighted state
through the finite recovery map. Normalization follows from that same run.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- The complete record law maps the genuine sample law through finite recovery. -/
theorem executionDistribution_eq_map {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model access).classicalOracles (pre width) Reference) :
    (run hinput access).executionDistribution input =
      ((SourceNativeSampling.run access).executionDistribution input).map
        (recoveredRecord hinput access) := by
  exact AlgorithmRun.RetainedRecord.executionDistribution_eq_map
    (key := resultKey t width) (shape := outputShape t)
    (fresh := resultFresh t width)
    (SourceNativeSampling.run access) (run hinput access)
    (recoveredRecord hinput access)
    (fun Reference state => execute_eq_map hinput access Reference state)
    input

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
