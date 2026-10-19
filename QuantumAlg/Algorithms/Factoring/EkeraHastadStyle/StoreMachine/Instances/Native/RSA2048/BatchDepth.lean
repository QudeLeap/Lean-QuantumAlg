/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.BatchDepth.Scalar
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Depth

/-!
# Complete native factoring batch depth at RSA-2048 widths

The decimal bound is the exact evaluation of the independent first/reused
complete-batch scalar ceiling. Whole-run accounting charges every actual batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- Independent unit-event ceiling for either complete sixteen-round factoring batch. -/
def batchDepthBound : Nat := 2_399_834_962_524_657_350

attribute [local irreducible] RSA.ShortLogWidths.coordinateWidth
attribute [local irreducible] NativeFiniteRetry.roundDepthWidthBound
  NativeFiniteRetry.recoveryDepthWidthBound

/-- The batch decimal is the exact evaluation of the independent complete-batch scalar ceiling. -/
lemma model_batchDepthScalarBound_eq {N : Nat} (model : FixedWidthModel N) :
    NativeCycles.Finite.batchDepthScalarBound N = batchDepthBound := by
  unfold NativeCycles.Finite.batchDepthScalarBound
  rw [model_coordinateWidth_eq model, model_modulusBits_eq model,
    model_shortLogBits_eq model, model_tradeoffBits_eq model, model_arithmeticBits_eq model]
  change 44 * 2_048 + 163 +
    16 * NativeFiniteRetry.roundDepthWidthBound 1_025 513 2_048 +
      NativeFiniteRetry.recoveryDepthWidthBound 2_048 1_025 513 7_522_484_226 = _
  rw [roundDepthWidthBound_eq, recoveryDepthWidthBound_eq]
  norm_num [roundDepthBound, recoveryDepthBound, batchDepthBound]

/-- The maximum first/reused complete-batch budget obeys the fixed RSA ceiling. -/
lemma model_batchDepthBound_le {N : Nat} (model : FixedWidthModel N) :
    NativeCycles.Finite.batchDepthBound N ≤ batchDepthBound :=
  (NativeCycles.Finite.batchDepthBound_le_scalar N).trans_eq
    (model_batchDepthScalarBound_eq model)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048
