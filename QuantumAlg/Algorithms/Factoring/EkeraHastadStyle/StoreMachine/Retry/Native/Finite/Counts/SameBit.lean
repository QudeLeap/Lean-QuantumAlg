/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Counts
import all QuantumAlg.Util.RSA.ShortLog.Widths.SameBit

/-!
# Same-bit classical-operation bounds for the actual native retry

The complete independent classical allowance is affine in the same-bit
width and its tradeoff width. Its linear ceiling implies the cubic ceiling
for every batch count. Each classical instruction retains its existing unit
weight, including word operations; this is not a bit-operation complexity
claim. Quantum instructions are not reclassified as classical operations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

open Execution LatticeRecoveryResources

noncomputable section

private theorem recovery_affine (modulusWidth m ell coordinateWidth : Nat) :
    LatticeFixedBatchRecoveryMachine.eventCountBound modulusWidth m ell coordinateWidth =
      97_125_852 * modulusWidth + 3_183_480 * m + 3_183_840 * ell +
        291_374_880 * coordinateWidth + 8_695_564_699 := by
  norm_num [LatticeFixedBatchRecoveryMachine.eventCountBound,
    LatticeFixedBatchRecoveryMachine.nearestPlaneEnvelopeBound, RSA.shortLogRecoveryFuel,
    modularSetupCardBound, candidateScanCardBound, candidateScanWork, candidateSlotCardBound,
    quadraticGuardedCardBound, natSqrtCardBound, QuadraticPrefix.discriminantWidth,
    QuadraticPrefix.centerWidth]
  omega

private theorem batch_affine (n ell : Nat) :
    44 * (2 * n) + 182 + LatticeFixedBatchRecoveryMachine.eventCountBound
        (2 * n) (n + 1) ell (2 ^ 21 * (3 * n + ell + 2) + 2) =
      1_833_172_434_460_552 * n + 611_057_415_525_600 * ell +
        1_222_124_106_181_641 := by
  rw [recovery_affine]
  ring

/-- Exact affine formula for the complete classical ceiling at every positive batch count. -/
theorem scalarClassicalOperationBound_sameBit_eq {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) (count : Nat) :
    scalarClassicalOperationBound pair.modulus (count + 1) =
      (count + 1) * (1_833_172_434_460_552 * n +
        611_057_415_525_600 * ((n + 2) / 2) + 1_222_124_106_181_641) + 1 := by
  rw [scalarClassicalOperationBound, modulusBits_sameBit pair positive,
    shortLogBits_sameBit pair positive, tradeoffBits_sameBit pair positive,
    RSA.ShortLogWidths.coordinateWidth_sameBit_parameters pair positive]
  change (count + 1) * (44 * (2 * n) + 182 +
    LatticeFixedBatchRecoveryMachine.eventCountBound (2 * n) (n + 1)
      ((n + 2) / 2) (2 ^ 21 * (3 * n + (n + 2) / 2 + 2) + 2)) + 1 = _
  rw [batch_affine]

/-- The existing independent classical allowance has a linear ceiling, including zero batches. -/
theorem scalarClassicalOperationBound_sameBit_le_linear {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (count : Nat) :
    scalarClassicalOperationBound pair.modulus count ≤ 2 ^ 52 * count * n + 1 := by
  cases count with
  | zero => simp [scalarClassicalOperationBound]
  | succ count =>
      rw [scalarClassicalOperationBound_sameBit_eq pair positive]
      have tradeoff : (n + 2) / 2 ≤ n := by omega
      have batch : 1_833_172_434_460_552 * n + 611_057_415_525_600 * ((n + 2) / 2) +
          1_222_124_106_181_641 ≤ 2 ^ 52 * n := by
        norm_num
        omega
      have repeated := Nat.mul_le_mul_left (count + 1) batch
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.add_le_add_right repeated 1

/-- The original cubic constant follows for the same allowance on the entire same-bit domain. -/
theorem scalarClassicalOperationBound_sameBit_le_cubic {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (count : Nat) :
    scalarClassicalOperationBound pair.modulus count ≤ 2 ^ 54 * count * n ^ 3 + 2 := by
  have linear := scalarClassicalOperationBound_sameBit_le_linear pair positive count
  have power : n ≤ n ^ 3 := by nlinarith [Nat.le_mul_self n]
  have constants : 2 ^ 52 ≤ (2 ^ 54 : Nat) := by norm_num
  have repeated := Nat.mul_le_mul
    (Nat.mul_le_mul_right count constants) power
  exact linear.trans (by omega)

-- Keep the dependent actual execution tree abstract when reusing its established path bound.
attribute [local irreducible] run code context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Literal classical operations on each complete actual path obey the stronger linear bound. -/
theorem run_classicalOperation_sameBit_le_linear {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) (input : Input pair.modulus) (count : Nat)
    (path : (run base noQuantum input count).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum input count).code.resourcePool path) ≤ 2 ^ 52 * count * n + 1 :=
  (run_classicalOperation_le_widthBound base noQuantum input count path).trans
    (scalarClassicalOperationBound_sameBit_le_linear pair positive count)

/-- The original cubic ceiling charges the same actual run, with arbitrary existing input state. -/
theorem run_classicalOperation_sameBit_le_cubic {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) (input : Input pair.modulus) (count : Nat)
    (path : (run base noQuantum input count).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum input count).code.resourcePool path) ≤ 2 ^ 54 * count * n ^ 3 + 2 :=
  (run_classicalOperation_le_widthBound base noQuantum input count path).trans
    (scalarClassicalOperationBound_sameBit_le_cubic pair positive count)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
