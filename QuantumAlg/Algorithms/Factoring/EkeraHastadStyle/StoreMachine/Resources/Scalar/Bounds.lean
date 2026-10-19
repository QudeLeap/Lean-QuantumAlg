/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.SameBit.Definitions
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources

/-!
# Polynomial bounds for the original width-only resource formulas

These inequalities preserve the numerical certificate independently of the
retired execution wrapper. They do not identify the formula with another
algorithm's actual resource accounting.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel

noncomputable section

private lemma tradeoffWidth_le_self_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.tradeoffWidth b ≤ b := by
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  unfold Canonical.PublicResourceBounds.tradeoffWidth
  omega

private lemma qftEventBound_le_three_mul_sq (bits : Nat) :
    Canonical.PublicResourceBounds.qftEventBound bits ≤ 3 * bits ^ 2 := by
  by_cases zeroBits : bits = 0
  · subst bits
    rfl
  have positive : 1 ≤ bits := Nat.one_le_iff_ne_zero.mpr zeroBits
  have phaseHalf : bits * (bits - 1) / 2 ≤ bits * (bits - 1) :=
    Nat.div_le_self _ _
  have phaseFull : bits * (bits - 1) ≤ bits * bits :=
    Nat.mul_le_mul_left bits (Nat.sub_le bits 1)
  have swapHalf : bits / 2 ≤ bits := Nat.div_le_self _ _
  have linearLeSquare : bits ≤ bits * bits := by
    nlinarith
  unfold Canonical.PublicResourceBounds.qftEventBound
  simp only [pow_two]
  omega

private lemma coordinateWidth_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.coordinateWidth b ≤ 2 ^ 24 * b := by
  have ellLe := tradeoffWidth_le_self_of_effective effective
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  unfold Canonical.PublicResourceBounds.coordinateWidth
    Canonical.PublicResourceBounds.tradeoffWidth at ellLe ⊢
  norm_num only
  omega

private lemma clog_le_sixteenth {b n : Nat} (wide : 512 ≤ b)
    (bounded : n ≤ 2 * b + 1) : 16 * Nat.clog 2 n ≤ b := by
  have growth : ∀ k : Nat, 32 ≤ k → 32 * k + 31 ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num only
    | succ k hk ih =>
        rw [pow_succ]
        omega
  have capacity : n ≤ 2 ^ (b / 16) :=
    (show n ≤ 32 * (b / 16) + 31 by omega).trans (growth _ (by omega))
  have logarithm : Nat.clog 2 n ≤ b / 16 := Nat.clog_le_of_le_pow capacity
  omega

private lemma offsetEventBound_le_square {b width : Nat} (wide : 512 ≤ b)
    (bounded : width ≤ 2 * b + 1) :
    MAU.Addition.Gidney.constantOffsetEventBound width ≤ 9 * b ^ 2 := by
  have logarithm := clog_le_sixteenth wide bounded
  have factor : 39 * Nat.clog 2 width + 1 ≤ 3 * b := by omega
  unfold MAU.Addition.Gidney.constantOffsetEventBound
  calc
    _ ≤ (3 * b) * (3 * b) := Nat.mul_le_mul (by omega) factor
    _ = 9 * b ^ 2 := by ring

private lemma nativeQftBound_le_nine_sq (bits : Nat) :
    ShortDLP.CompiledMAU.qftPrimitiveBound bits ≤ 9 * bits ^ 2 := by
  by_cases zero : bits = 0
  · subst bits
    rfl
  have positive : 1 ≤ bits := Nat.one_le_iff_ne_zero.mpr zero
  have linear : bits ≤ bits ^ 2 := by nlinarith
  have pairs : bits.choose 2 ≤ bits ^ 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans
      (by simpa only [pow_two] using Nat.mul_le_mul_left bits (Nat.sub_le bits 1))
  have half := Nat.div_le_self bits 2
  unfold ShortDLP.CompiledMAU.qftPrimitiveBound
  omega

private lemma stageBound_le_square {b : Nat} (wide : 512 ≤ b) :
    MAU.Multiplication.Accumulate.Gidney.stageEventBound (2 * b) ≤ 2 ^ 11 * b ^ 2 := by
  have offset := offsetEventBound_le_square wide (show 2 * b ≤ 2 * b + 1 by omega)
  have extended := offsetEventBound_le_square wide (show 1 + 2 * b ≤ 2 * b + 1 by omega)
  have positive : 1 ≤ b := by omega
  have oneLeSquare : 1 ≤ b ^ 2 := one_le_pow_of_one_le' positive 2
  have linearLeSquare : b ≤ b ^ 2 := le_self_pow positive (by decide)
  unfold MAU.Multiplication.Accumulate.Gidney.stageEventBound
  rw [if_neg (by omega)]
  change 4 * (3 * (2 * (4 * (MAU.Addition.Gidney.constantOffsetEventBound (2 * b) +
    2 * b) + 2) + 2 * (MAU.Addition.Gidney.constantOffsetEventBound (1 + 2 * b) +
      MAU.Addition.Gidney.constantOffsetEventBound (2 * b) + 1))) ≤ _
  calc
    _ = 120 * MAU.Addition.Gidney.constantOffsetEventBound (2 * b) +
        24 * MAU.Addition.Gidney.constantOffsetEventBound (1 + 2 * b) + 192 * b + 72 := by
      ring
    _ ≤ 120 * (9 * b ^ 2) + 24 * (9 * b ^ 2) + 192 * b + 72 := by omega
    _ ≤ 2 ^ 11 * b ^ 2 := by norm_num only; omega

private lemma multiplicationBound_le_cube {b : Nat} (wide : 512 ≤ b) :
    MAU.Multiplication.Gidney.eventBound (2 * b) ≤ 2 ^ 14 * b ^ 3 := by
  have stageLe := stageBound_le_square wide
  have positive : 1 ≤ b := by omega
  have linearLeCube : b ≤ b ^ 3 := le_self_pow positive (by decide)
  unfold MAU.Multiplication.Gidney.eventBound
  calc
    _ = 4 * b * MAU.Multiplication.Accumulate.Gidney.stageEventBound (2 * b) +
        6 * b := by ring
    _ ≤ 4 * b * (2 ^ 11 * b ^ 2) + 6 * b :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ stageLe) _
    _ = 8192 * b ^ 3 + 6 * b := by norm_num only; ring
    _ ≤ 2 ^ 14 * b ^ 3 := by norm_num only; omega

private lemma exponentiationBound_le_cube {b : Nat} (wide : 512 ≤ b) (bits : Nat) :
    ShortDLP.CompiledMAU.exponentiationPrimitiveWidthBound bits (2 * b) ≤
      2 ^ 18 * bits * b ^ 3 := by
  have multiplicationLe := multiplicationBound_le_cube wide
  calc
    _ = (12 * bits) * MAU.Multiplication.Gidney.eventBound (2 * b) := by
      unfold ShortDLP.CompiledMAU.exponentiationPrimitiveWidthBound
        MAU.Exponentiation.Gidney.eventBound MAU.Exponentiation.Gidney.stageEventBound
      ring
    _ ≤ (12 * bits) * (2 ^ 14 * b ^ 3) := Nat.mul_le_mul_left _ multiplicationLe
    _ = (12 * 2 ^ 14) * (bits * b ^ 3) := by ring
    _ ≤ (2 ^ 18) * (bits * b ^ 3) := Nat.mul_le_mul_right _ (by norm_num only)
    _ = _ := by ring

private lemma groupActionBound_le_quartic {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    ShortDLP.CompiledMAU.groupActionPrimitiveWidthBound
      (b + 1) (Canonical.PublicResourceBounds.tradeoffWidth b) (2 * b) ≤
        2 ^ 20 * b ^ 4 := by
  have wide : 512 ≤ b := by
    simpa only [RSA.GeneratorOrder.effectiveCutoffBits] using effective
  have ellLe := tradeoffWidth_le_self_of_effective effective
  have combinedWidth : b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b ≤
      4 * b := by omega
  unfold ShortDLP.CompiledMAU.groupActionPrimitiveWidthBound
  calc
    _ ≤ 2 ^ 18 * (Canonical.PublicResourceBounds.tradeoffWidth b + (b + 1)) * b ^ 3 +
        2 ^ 18 * Canonical.PublicResourceBounds.tradeoffWidth b * b ^ 3 :=
      Nat.add_le_add (exponentiationBound_le_cube wide _) (exponentiationBound_le_cube wide _)
    _ = (2 ^ 18 * b ^ 3) *
        (b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b) := by ring
    _ ≤ (2 ^ 18 * b ^ 3) * (4 * b) := Nat.mul_le_mul_left _ combinedWidth
    _ = _ := by norm_num only; ring

private lemma memberEventBound_le_quartic_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.memberEventBound b ≤ 2 ^ 21 * b ^ 4 := by
  have wide : 512 ≤ b := by
    simpa only [RSA.GeneratorOrder.effectiveCutoffBits] using effective
  have positive : 1 ≤ b := by omega
  have oneLeSquare : 1 ≤ b ^ 2 := one_le_pow_of_one_le' positive 2
  have linearLeSquare : b ≤ b ^ 2 := le_self_pow positive (by decide)
  have squareLeQuartic : b ^ 2 ≤ b ^ 4 := by
    calc
      b ^ 2 = b ^ 2 * 1 := by simp
      _ ≤ b ^ 2 * b ^ 2 := Nat.mul_le_mul_left (b ^ 2) oneLeSquare
      _ = b ^ 4 := by ring
  have ellLe := tradeoffWidth_le_self_of_effective effective
  have firstWidth : b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b ≤ 3 * b := by
    omega
  have groupLe := groupActionBound_le_quartic effective
  have firstSquare : (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) ^ 2 ≤
      (3 * b) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul firstWidth firstWidth
  have firstQft : ShortDLP.CompiledMAU.qftPrimitiveBound
      (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) ≤ 81 * b ^ 2 := by
    calc
      _ ≤ 9 * (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) ^ 2 :=
        nativeQftBound_le_nine_sq _
      _ ≤ 9 * (3 * b) ^ 2 := Nat.mul_le_mul_left _ firstSquare
      _ = _ := by ring
  have secondSquare : Canonical.PublicResourceBounds.tradeoffWidth b ^ 2 ≤ b ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul ellLe ellLe
  have secondQft : ShortDLP.CompiledMAU.qftPrimitiveBound
      (Canonical.PublicResourceBounds.tradeoffWidth b) ≤ 9 * b ^ 2 :=
    (nativeQftBound_le_nine_sq _).trans (Nat.mul_le_mul_left _ secondSquare)
  have lowerLe : b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b +
      ShortDLP.CompiledMAU.qftPrimitiveBound
        (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) +
      ShortDLP.CompiledMAU.qftPrimitiveBound
        (Canonical.PublicResourceBounds.tradeoffWidth b) ≤ 2 ^ 7 * b ^ 2 := by
    norm_num only
    omega
  have lowerQuartic : 2 ^ 7 * b ^ 2 ≤ 2 ^ 20 * b ^ 4 :=
    (Nat.mul_le_mul_left (2 ^ 7) squareLeQuartic).trans
      (Nat.mul_le_mul_right (b ^ 4) (by norm_num only))
  unfold Canonical.PublicResourceBounds.memberEventBound
    ShortDLP.CompiledMAU.polynomialPrimitiveWidthBound
  have combined := Nat.add_le_add groupLe (lowerLe.trans lowerQuartic)
  calc
    _ = ShortDLP.CompiledMAU.groupActionPrimitiveWidthBound
        (b + 1) (Canonical.PublicResourceBounds.tradeoffWidth b) (2 * b) +
        (b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b +
          ShortDLP.CompiledMAU.qftPrimitiveBound
            (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) +
          ShortDLP.CompiledMAU.qftPrimitiveBound
            (Canonical.PublicResourceBounds.tradeoffWidth b)) := by
      simp only [Nat.add_comm (b + 1) (Canonical.PublicResourceBounds.tradeoffWidth b)]
      omega
    _ ≤ 2 ^ 20 * b ^ 4 + 2 ^ 20 * b ^ 4 := combined
    _ = _ := by norm_num only; ring

private lemma modularSetupEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.modularSetupEventBound b ≤
      2 ^ 6 * b ^ 2 := by
  have positive : 1 ≤ b := by
    unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
    omega
  unfold Canonical.PublicResourceBounds.modularSetupEventBound
  norm_num only
  nlinarith

private lemma nearestPlaneEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.nearestPlaneEventBound b ≤
      2 ^ 13 * b := by
  have ellLe := tradeoffWidth_le_self_of_effective effective
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  unfold Canonical.PublicResourceBounds.nearestPlaneEventBound
  norm_num only
  nlinarith

private lemma candidateScanEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.candidateScanEventBound b ≤
      2 ^ 48 * b ^ 2 := by
  have widthAtLeast : 512 ≤ b := by
    simpa only [RSA.GeneratorOrder.effectiveCutoffBits] using effective
  have coordinateLe := coordinateWidth_le_of_effective effective
  have factorLe : 8 * b + 11 ≤ 9 * b := by omega
  have productLe :
      Canonical.PublicResourceBounds.coordinateWidth b * (8 * b + 11) ≤
        9 * 2 ^ 24 * b ^ 2 := by
    calc
      _ ≤ (2 ^ 24 * b) * (9 * b) :=
        Nat.mul_le_mul coordinateLe factorLe
      _ = 9 * 2 ^ 24 * b ^ 2 := by ring
  have positive : 1 ≤ b := by omega
  have oneLeSquare : 1 ≤ b ^ 2 := one_le_pow_of_one_le' positive 2
  have innerLe :
      178 +
          Canonical.PublicResourceBounds.coordinateWidth b * (8 * b + 11) ≤
        2 ^ 28 * b ^ 2 := by
    norm_num only at productLe ⊢
    nlinarith
  have scaledLe := Nat.mul_le_mul_left 404685 innerLe
  unfold Canonical.PublicResourceBounds.candidateScanEventBound
  norm_num only at scaledLe ⊢
  nlinarith

private lemma quadraticEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.quadraticEventBound b ≤
      2 ^ 29 * b := by
  have positive : 1 ≤ b := by
    unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
    omega
  have coordinateLe := coordinateWidth_le_of_effective effective
  unfold Canonical.PublicResourceBounds.quadraticEventBound
  norm_num only at coordinateLe ⊢
  nlinarith

private lemma recoveryEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.recoveryEventBound b ≤
      2 ^ 57 * b ^ 2 := by
  have modularLe := modularSetupEventBound_le_of_effective effective
  have nearestLe := nearestPlaneEventBound_le_of_effective effective
  have candidateLe := candidateScanEventBound_le_of_effective effective
  have quadraticLe := quadraticEventBound_le_of_effective effective
  have positive : 1 ≤ b := by
    unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
    omega
  have oneLeSquare : 1 ≤ b ^ 2 := one_le_pow_of_one_le' positive 2
  have linearLeSquare : b ≤ b ^ 2 := le_self_pow positive (by decide)
  have bodyLe :
      13 +
          ((Canonical.PublicResourceBounds.nearestPlaneEventBound b + (b + 4) +
              Canonical.PublicResourceBounds.modularSetupEventBound b +
                Canonical.PublicResourceBounds.candidateScanEventBound b) +
            Canonical.PublicResourceBounds.quadraticEventBound b) ≤
        2 ^ 49 * b ^ 2 := by
    norm_num only at modularLe nearestLe candidateLe quadraticLe ⊢
    omega
  have scaledLe := Nat.mul_le_mul_left 120 bodyLe
  unfold Canonical.PublicResourceBounds.recoveryEventBound
  norm_num only at modularLe scaledLe ⊢
  omega

private lemma quadratic_bound_to_quartic {b events : Nat} (wide : 512 ≤ b)
    (bounded : events ≤ 2 ^ 57 * b ^ 2) : events ≤ 2 ^ 39 * b ^ 4 := by
  have widthSquareAtLeast : 2 ^ 18 ≤ b ^ 2 := by
    have square := Nat.mul_le_mul wide wide
    norm_num only at square ⊢
    simpa only [pow_two] using square
  calc
    _ ≤ 2 ^ 57 * b ^ 2 := bounded
    _ = (2 ^ 39 * b ^ 2) * 2 ^ 18 := by norm_num only; ring
    _ ≤ (2 ^ 39 * b ^ 2) * b ^ 2 :=
      Nat.mul_le_mul_left (2 ^ 39 * b ^ 2) widthSquareAtLeast
    _ = 2 ^ 39 * b ^ 4 := by ring

private lemma complete_batch_scalar_bound {b member recovery ell : Nat} (wide : 512 ≤ b)
    (memberLe : member ≤ 2 ^ 21 * b ^ 4) (recoveryLe : recovery ≤ 2 ^ 57 * b ^ 2)
    (ellLe : ell ≤ b) :
    88 * b + 180 + 16 * (member + b + 2 + 2 * ell) + recovery ≤ 2 ^ 54 * b ^ 4 := by
  have positive : 1 ≤ b := by omega
  have oneLeQuartic : 1 ≤ b ^ 4 := one_le_pow_of_one_le' positive 4
  have linearLeQuartic : b ≤ b ^ 4 := le_self_pow positive (by decide)
  have recoveryQuartic := quadratic_bound_to_quartic wide recoveryLe
  have headLe : 88 * b + 180 ≤ 2 ^ 10 * b ^ 4 := by norm_num only; omega
  have memberAndExtraLe : member + b + 2 + 2 * ell ≤ 2 ^ 22 * b ^ 4 := by
    norm_num only at memberLe ⊢
    omega
  have repetitionLe : 16 * (member + b + 2 + 2 * ell) ≤ 2 ^ 26 * b ^ 4 := by
    calc
      _ ≤ 16 * (2 ^ 22 * b ^ 4) := Nat.mul_le_mul_left 16 memberAndExtraLe
      _ = 2 ^ 26 * b ^ 4 := by norm_num only; ring
  calc
    _ ≤ (2 ^ 10 * b ^ 4 + 2 ^ 26 * b ^ 4) + 2 ^ 39 * b ^ 4 :=
      Nat.add_le_add (Nat.add_le_add headLe repetitionLe) recoveryQuartic
    _ ≤ 2 ^ 54 * b ^ 4 := by norm_num only; omega

/-- In the analytically effective same-bit range, the historical scalar batch
expression has a width-only quartic bound. -/
lemma batchEventBound_le_twoPow54_quartic {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.batchEventBound b ≤ 2 ^ 54 * b ^ 4 := by
  have wide : 512 ≤ b := by
    simpa only [RSA.GeneratorOrder.effectiveCutoffBits] using effective
  exact complete_batch_scalar_bound wide (memberEventBound_le_quartic_of_effective effective)
    (recoveryEventBound_le_of_effective effective) (tradeoffWidth_le_self_of_effective effective)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel
