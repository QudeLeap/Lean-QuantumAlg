/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Finite
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Depth

/-!
# Parameterized scalar depth of a complete native factoring cycle

One completed trial includes the sampler, sixteen measured rounds and full
classical recovery. The same width-only ceiling bounds both the first and
reused trial, before any fixed RSA modulus is substituted.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.Finite

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- Independent scalar ceiling for either complete batch at arbitrary modulus width. -/
def batchDepthScalarBound (N : Nat) : Nat :=
  44 * Canonical.modulusBits N + 163 +
    16 * NativeFiniteRetry.roundDepthWidthBound
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) +
    NativeFiniteRetry.recoveryDepthWidthBound (Canonical.modulusBits N)
      (shortLogBits N) (tradeoffBits N)
      (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))

/-- Both actual complete-batch allowances obey the same symbolic width formula. -/
theorem batchDepthBound_le_scalar (N : Nat) :
    batchDepthBound N ≤ batchDepthScalarBound N := by
  have round := NativeFiniteRetry.round_unitDepthBound_le_widthBound
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  have recovery := NativeFiniteRetry.recovery_depthBound_le_widthBound N
  have repeated := Nat.add_le_add (Nat.mul_le_mul_left 16 round) recovery
  have reload := NativeFiniteRetry.seedReload_count_le_one
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  have preparation : (if ShortDLP.totalQubits
      (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) = 0
      then 0 else 1) ≤ 1 := by
    split <;> omega
  apply max_le
  · unfold NativeBatchRecovery.depthBound NativeBatch.unitDepthBound batchDepthScalarBound
    omega
  · unfold NativeBatchReuseRecovery.depthBound NativeBatchReuse.unitDepthBound
      batchDepthScalarBound
    omega

/-- Zero trials have no completed cycle; all positive counts use one batch ceiling. -/
def maximumCycleScalarBound (N : Nat) : Nat → Nat
  | 0 => 0
  | _ + 1 => batchDepthScalarBound N

/-- The original independent cycle allowance fits the symbolic scalar ceiling. -/
theorem maximumCycleDepthBound_le_scalar (N count : Nat) :
    maximumCycleDepthBound N count ≤ maximumCycleScalarBound N count := by
  cases count with
  | zero => exact le_refl 0
  | succ count => exact batchDepthBound_le_scalar N

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.Finite
