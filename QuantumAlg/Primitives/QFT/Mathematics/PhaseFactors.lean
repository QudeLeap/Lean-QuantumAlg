/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Components.Gates.ControlledPhase.Operator
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.FinPow
import Mathlib.Algebra.BigOperators.Fin

/-!
# Fourier phase factors in binary coordinates

The original scalar product of addressed controlled phases equals the
Fourier root raised to the lower input bits when the leading bit is set.
These identities are independent of the native execution model.
-/

namespace QuantumAlg

noncomputable section

/-- Rotation angle used between the leading wire and the `(offset+1)`st wire
of one recursive QFT stage. -/
def qftPhaseAngle (offset : Nat) : Real :=
  2 * Real.pi / (2 : Real) ^ (offset + 2)

/-- Scalar accumulated by the first `count` controlled phases of one QFT
stage on a computational-basis label. -/
def qftPhaseLayerFactorPrefix (n : Nat) :
    (count : Nat) → count ≤ n → Fin (2 ^ (n + 1)) → Complex
  | 0, _, _ => 1
  | count + 1, hcount, label =>
      qftControlledPhaseFactor 0
          ⟨count + 1, by omega⟩ (qftPhaseAngle count) label *
        qftPhaseLayerFactorPrefix n count (by omega) label

/-- One phase-layer factor, indexed in source-circuit order. -/
def qftPhaseFactorAt (n : Nat) (offset : Fin n)
    (label : Fin (2 ^ (n + 1))) : Complex :=
  qftControlledPhaseFactor 0
    ⟨offset.val + 1, Nat.succ_lt_succ offset.isLt⟩
    (qftPhaseAngle offset.val) label

/-- Reconstruct a natural number as the weighted sum of its finite bit vector. -/
lemma natOfBits_eq_sum {n : Nat} (bits : Fin n → Bool) :
    Nat.ofBits bits = ∑ bit : Fin n, (bits bit).toNat * 2 ^ bit.val := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.ofBits_succ, Fin.sum_univ_succ]
      rw [ih (bits ∘ Fin.succ)]
      simp only [Function.comp_apply]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have hsum :
          (∑ bit : Fin n,
              (bits bit.succ).toNat * 2 ^ (bit.val + 1)) =
            2 * ∑ bit : Fin n, (bits bit.succ).toNat * 2 ^ bit.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro bit _
        rw [pow_succ]
        ring
      rw [hsum]
      omega

/-- The recursive scalar accumulator is exactly the product of the phase
factors represented by its first `count` structural leaves. -/
lemma qftPhaseLayerFactorPrefix_eq_prod (n count : Nat)
    (hcount : count ≤ n) (label : Fin (2 ^ (n + 1))) :
    qftPhaseLayerFactorPrefix n count hcount label =
      ∏ offset : Fin count,
        qftPhaseFactorAt n
          ⟨offset.val, lt_of_lt_of_le offset.isLt hcount⟩ label := by
  induction count with
  | zero => simp [qftPhaseLayerFactorPrefix]
  | succ count ih =>
      rw [qftPhaseLayerFactorPrefix, Fin.prod_univ_castSucc, ih (by omega)]
      rw [mul_comm]
      rfl

/-- The source angle of one phase leaf is the corresponding binary-weight
power of the common `(n+1)`-qubit Fourier root. -/
lemma qftPhaseAngle_exp_eq_omega_pow (n : Nat) (offset : Fin n) :
    Complex.exp (qftPhaseAngle offset.val * Complex.I) =
      ω (n + 1) ^ (2 ^ (Fin.rev offset).val) := by
  rw [ω, ← Complex.exp_nat_mul]
  congr 1
  simp only [qftPhaseAngle]
  push_cast
  have hsum : (Fin.rev offset).val + (offset.val + 2) = n + 1 := by
    simp [Fin.rev]
    omega
  field_simp
  rw [← pow_add, add_comm (offset.val + 2) (Fin.rev offset).val, hsum]

/-- Each actual controlled-phase leaf contributes the Fourier-root power of
its addressed input bit, and contributes one when the leading bit is zero. -/
lemma qftPhaseFactorAt_eq_omega_pow (n : Nat) (offset : Fin n)
    (label : Fin (2 ^ (n + 1))) :
    qftPhaseFactorAt n offset label =
      if label.val.testBit n then
        ω (n + 1) ^
          ((label.val.testBit (Fin.rev offset).val).toNat *
            2 ^ (Fin.rev offset).val)
      else 1 := by
  have htarget : n - (offset.val + 1) = (Fin.rev offset).val := by
    simp [Fin.rev]
  unfold qftPhaseFactorAt qftControlledPhaseFactor
  change
    (if label.val.testBit n &&
          label.val.testBit (n - (offset.val + 1)) then
        Complex.exp (qftPhaseAngle offset.val * Complex.I)
      else 1) = _
  by_cases hhead : label.val.testBit n
  · simp only [hhead, Bool.true_and, if_true]
    by_cases htargetBit : label.val.testBit (n - (offset.val + 1))
    · rw [if_pos htargetBit]
      rw [qftPhaseAngle_exp_eq_omega_pow]
      simp [htargetBit]
    · rw [if_neg htargetBit]
      simp [htargetBit]
  · simp [hhead]

/-- The complete phase layer contributes the Fourier root raised to the lower
`n` input bits whenever the leading output branch is one. -/
lemma qftPhaseLayerFactor_eq (n : Nat)
    (label : Fin (2 ^ (n + 1))) :
    qftPhaseLayerFactorPrefix n n le_rfl label =
      if label.val.testBit n then
        ω (n + 1) ^ (label.val % 2 ^ n)
      else 1 := by
  rw [qftPhaseLayerFactorPrefix_eq_prod]
  have hcast (offset : Fin n) :
      (⟨offset.val, lt_of_lt_of_le offset.isLt le_rfl⟩ : Fin n) = offset :=
    Fin.ext rfl
  simp_rw [hcast]
  by_cases hhead : label.val.testBit n
  · simp_rw [qftPhaseFactorAt_eq_omega_pow, if_pos hhead]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))]
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    rw [← natOfBits_eq_sum]
    exact Nat.ofBits_testBit label.val n
  · simp [qftPhaseFactorAt_eq_omega_pow, hhead]

end

end QuantumAlg
