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
lemma executionDistribution_eq_map {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (environment : (Sampling.Native.model t width).Environment)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model t width).classicalOracles (pre width) Reference) :
    (run spec t).executionDistribution environment input =
      ((SourceNativeSampling.run t width).executionDistribution environment input).map
        (recoveredRecord spec t) := by
  exact AlgorithmRun.RetainedRecord.executionDistribution_eq_map
    (key := resultKey t width) (shape := outputShape t)
    (fresh := resultFresh t width)
    (SourceNativeSampling.run t width) (run spec t) environment
    (recoveredRecord spec t)
    (fun Reference state => execute_eq_map spec t environment Reference state)
    input

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
