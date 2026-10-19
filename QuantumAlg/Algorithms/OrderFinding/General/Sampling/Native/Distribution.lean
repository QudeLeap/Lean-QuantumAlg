/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Distribution

/-!
# Born law of the source sample beside the borrowed base

The original borrowed canonical residue remains live while actual quantum
preparation, native gates, Z writes and packing produce the phase word. The
result law is independent of the base's reference correlations.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling

noncomputable section

open QuantumAlg.Execution

/-- The borrowed-base sample has the native source phase distribution. -/
lemma distribution {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model t width).classicalOracles (pre width) Reference) :
    (run t width).outputDistribution (Sampling.Native.environment access) input =
      (OrderFinding.Native.sourceOutcomePMF access).map CShape.Value.bits :=
  Sampling.Native.Framed.outputDistribution_eq
    (pre width) (pre_quantumWires width) access input

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling
