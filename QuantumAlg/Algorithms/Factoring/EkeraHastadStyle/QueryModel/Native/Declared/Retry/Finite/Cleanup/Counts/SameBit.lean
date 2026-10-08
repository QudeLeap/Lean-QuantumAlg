/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Counts.SameBit

/-!
# Same-bit scalar classical ceilings

The two sample packs contribute thirty-two classical instructions per batch.
The pure allowance with one final result pack admits linear and cubic
ceilings. These scalar inequalities remain independent mathematical facts;
the completed execution's actual path bounds account separately for its
additional result packs.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

private theorem scalar_additional_packs (N count : Nat) :
    scalarClassicalOperationBound N count =
      NativeFiniteRetry.scalarClassicalOperationBound N count + 16 * count := by
  cases count with
  | zero => rfl
  | succ count =>
      unfold scalarClassicalOperationBound NativeFiniteRetry.scalarClassicalOperationBound
      ring

/-- The actual original-bank allowance includes all sixteen additional slot packs per batch. -/
theorem declaredCleanup_classicalCeiling_sameBit_eq {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (count : Nat) :
    scalarClassicalOperationBound pair.modulus (count + 1) =
      (count + 1) * (1_833_172_434_460_552 * n +
        611_057_415_525_600 * ((n + 2) / 2) + 1_222_124_106_181_657) + 1 := by
  rw [scalar_additional_packs,
    NativeFiniteRetry.scalarClassicalOperationBound_sameBit_eq pair positive]
  ring

/-- The full original-bank literal-classical ceiling retains a linear bound for every count. -/
theorem declaredCleanup_classicalCeiling_sameBit_le_linear {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (count : Nat) :
    scalarClassicalOperationBound pair.modulus count ≤ 2 ^ 52 * count * n + 1 := by
  cases count with
  | zero => simp [scalarClassicalOperationBound]
  | succ count =>
      rw [declaredCleanup_classicalCeiling_sameBit_eq pair positive]
      have tradeoff : (n + 2) / 2 ≤ n := by omega
      have batch : 1_833_172_434_460_552 * n + 611_057_415_525_600 * ((n + 2) / 2) +
          1_222_124_106_181_657 ≤ 2 ^ 52 * n := by
        norm_num
        omega
      have repeated := Nat.mul_le_mul_left (count + 1) batch
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.add_le_add_right repeated 1

/-- The original cubic constant covers the same-bit allowance including the paid slot writes. -/
theorem declaredCleanup_classicalCeiling_sameBit_le_cubic {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (count : Nat) :
    scalarClassicalOperationBound pair.modulus count ≤ 2 ^ 54 * count * n ^ 3 + 2 := by
  have linear := declaredCleanup_classicalCeiling_sameBit_le_linear pair positive count
  have power : n ≤ n ^ 3 := by nlinarith [Nat.le_mul_self n]
  have constants : 2 ^ 52 ≤ (2 ^ 54 : Nat) := by norm_num
  have repeated := Nat.mul_le_mul (Nat.mul_le_mul_right count constants) power
  exact linear.trans (by omega)

-- No compiled arithmetic execution theorem is used for the original oracle run.

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
