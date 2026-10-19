/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Distribution.Readout
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native.Distribution
import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Distribution

/-!
# Native source Born law followed by actual finite recovery

The complete general-order circuit begins with the accepted native source
word, measures and packs its phase bits, then runs finite recovery on those
same stored bits and original borrowed base.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- The full endpoint returns the native source Born law after genuine recovery. -/
lemma outputDistribution_eq {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model t width).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput access input.caller.localState) :
    (run (modulusSpec hinput access) t).outputDistribution (Sampling.Native.environment access)
      input =
      (OrderFinding.Native.sourceOutcomePMF access).map
        (fun outcome => recoveredValue hinput access (.bits outcome)) := by
  rw [outputDistribution_eq_recovery hinput access input valid,
    SourceNativeSampling.distribution, PMF.map_comp]
  rfl

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
