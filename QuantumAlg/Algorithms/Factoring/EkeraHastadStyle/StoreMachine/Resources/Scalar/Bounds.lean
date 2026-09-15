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

private theorem tradeoffWidth_le_self_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.tradeoffWidth b ≤ b := by
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  unfold Canonical.PublicResourceBounds.tradeoffWidth
  omega

private theorem qftEventBound_le_three_mul_sq (bits : Nat) :
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

private theorem coordinateWidth_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.coordinateWidth b ≤ 2 ^ 24 * b := by
  have ellLe := tradeoffWidth_le_self_of_effective effective
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  unfold Canonical.PublicResourceBounds.coordinateWidth
    Canonical.PublicResourceBounds.tradeoffWidth at ellLe ⊢
  norm_num
  omega

private theorem clog_le_sixteenth {b n : Nat} (wide : 512 ≤ b)
    (bounded : n ≤ 2 * b + 1) : 16 * Nat.clog 2 n ≤ b := by
  have growth : ∀ k : Nat, 32 ≤ k → 32 * k + 31 ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
        rw [pow_succ]
        omega
  have capacity : n ≤ 2 ^ (b / 16) :=
    (show n ≤ 32 * (b / 16) + 31 by omega).trans (growth _ (by omega))
  have logarithm : Nat.clog 2 n ≤ b / 16 := Nat.clog_le_of_le_pow capacity
  omega

private theorem offsetEventBound_le_square {b width : Nat} (wide : 512 ≤ b)
    (bounded : width ≤ 2 * b + 1) :
    MAU.Addition.Gidney.constantOffsetEventBound width ≤ 9 * b ^ 2 := by
  have logarithm := clog_le_sixteenth wide bounded
  have factor : 39 * Nat.clog 2 width + 1 ≤ 3 * b := by omega
  calc
    _ ≤ (3 * b) * (3 * b) := Nat.mul_le_mul (by omega) factor
    _ = 9 * b ^ 2 := by ring

set_option maxHeartbeats 800000 in
-- Lean 4.33.1 needs this budget for the symbolic quartic event-bound normalization.
private theorem memberEventBound_le_quartic_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.memberEventBound b ≤ 2 ^ 15 * b ^ 4 := by
  have widthAtLeast : 512 ≤ b := by
    simpa only [RSA.GeneratorOrder.effectiveCutoffBits] using effective
  have positive : 1 ≤ b := by omega
  have oneLeSquare : 1 ≤ b ^ 2 := by nlinarith
  have linearLeSquare : b ≤ b ^ 2 := by nlinarith
  have squareLeQuartic : b ^ 2 ≤ b ^ 4 := by
    calc
      b ^ 2 = b ^ 2 * 1 := by simp
      _ ≤ b ^ 2 * b ^ 2 := Nat.mul_le_mul_left (b ^ 2) oneLeSquare
      _ = b ^ 4 := by ring
  have cubeLeQuartic : b ^ 3 ≤ b ^ 4 := by
    nlinarith
  have ellLe := tradeoffWidth_le_self_of_effective effective
  have memberWidthLe :
      b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b ≤
        4 * b := by
    omega
  have firstWidthLe :
      b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b ≤ 3 * b := by
    omega
  have stageLe : MAU.Multiplication.Accumulate.Gidney.stageEventBound (2 * b) ≤
      168 * b ^ 2 := by
    have offset := offsetEventBound_le_square widthAtLeast (show 2 * b ≤ 2 * b + 1 by omega)
    have extended := offsetEventBound_le_square widthAtLeast
      (show 1 + 2 * b ≤ 2 * b + 1 by omega)
    unfold MAU.Multiplication.Accumulate.Gidney.stageEventBound
    rw [if_neg (by omega)]
    unfold MAU.Addition.Gidney.modularOffsetEventBound MAU.Addition.Gidney.pivotEventBound
      MAU.Addition.Gidney.biFlipEventBound MAU.Addition.Gidney.comparisonEventBound
    nlinarith
  let primitive := 12 * (2 * b * MAU.Multiplication.Accumulate.Gidney.stageEventBound (2 * b)) +
    3 * (2 * b)
  have primitiveLe : primitive ≤ 2 ^ 12 * b ^ 3 := by
    have scaled := Nat.mul_le_mul_left (24 * b) stageLe
    dsimp [primitive]
    nlinarith
  have groupLe :
      (Canonical.PublicResourceBounds.tradeoffWidth b + (b + 1)) * primitive +
          Canonical.PublicResourceBounds.tradeoffWidth b * primitive ≤
        2 ^ 14 * b ^ 4 := by
    calc
      _ = (b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b) * primitive := by ring
      _ ≤ (4 * b) * (2 ^ 12 * b ^ 3) := Nat.mul_le_mul memberWidthLe primitiveLe
      _ = 2 ^ 14 * b ^ 4 := by norm_num; ring
  have firstSquareLe :
      (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) ^ 2 ≤
        (3 * b) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul firstWidthLe firstWidthLe
  have firstQftLe :
      Canonical.PublicResourceBounds.qftEventBound
          (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) ≤
        27 * b ^ 2 := by
    calc
      _ ≤ 3 *
          (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) ^ 2 :=
        qftEventBound_le_three_mul_sq _
      _ ≤ 3 * (3 * b) ^ 2 := Nat.mul_le_mul_left 3 firstSquareLe
      _ = 27 * b ^ 2 := by ring
  have ellSquareLe :
      (Canonical.PublicResourceBounds.tradeoffWidth b) ^ 2 ≤ b ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul ellLe ellLe
  have secondQftLe :
      Canonical.PublicResourceBounds.qftEventBound
          (Canonical.PublicResourceBounds.tradeoffWidth b) ≤
        3 * b ^ 2 := by
    exact (qftEventBound_le_three_mul_sq _).trans
      (Nat.mul_le_mul_left 3 ellSquareLe)
  have lowerLe :
      b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b +
          Canonical.PublicResourceBounds.qftEventBound
            (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) +
          Canonical.PublicResourceBounds.qftEventBound
            (Canonical.PublicResourceBounds.tradeoffWidth b) ≤
        2 ^ 6 * b ^ 2 := by
    norm_num at firstQftLe secondQftLe ⊢
    nlinarith
  have lowerQuartic : 2 ^ 6 * b ^ 2 ≤ 2 ^ 13 * b ^ 4 := by
    calc
      2 ^ 6 * b ^ 2 ≤ 2 ^ 6 * b ^ 4 :=
        Nat.mul_le_mul_left (2 ^ 6) squareLeQuartic
      _ ≤ 2 ^ 13 * b ^ 4 := by norm_num; omega
  unfold Canonical.PublicResourceBounds.memberEventBound
    ShortDLP.CompiledMAU.polynomialPrimitiveWidthBound
    ShortDLP.CompiledMAU.groupActionPrimitiveWidthBound
    ShortDLP.CompiledMAU.exponentiationPrimitiveWidthBound
  change
    (Canonical.PublicResourceBounds.tradeoffWidth b + (b + 1)) * primitive +
        Canonical.PublicResourceBounds.tradeoffWidth b * primitive +
        (b + 1 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b) +
        Canonical.PublicResourceBounds.qftEventBound
          (b + 1 + Canonical.PublicResourceBounds.tradeoffWidth b) +
        Canonical.PublicResourceBounds.qftEventBound
          (Canonical.PublicResourceBounds.tradeoffWidth b) ≤
      2 ^ 15 * b ^ 4
  have hcombined := Nat.add_le_add groupLe (lowerLe.trans lowerQuartic)
  norm_num at hcombined ⊢
  omega

private theorem modularSetupEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.modularSetupEventBound b ≤
      2 ^ 6 * b ^ 2 := by
  have positive : 1 ≤ b := by
    unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
    omega
  unfold Canonical.PublicResourceBounds.modularSetupEventBound
  norm_num
  nlinarith

private theorem nearestPlaneEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.nearestPlaneEventBound b ≤
      2 ^ 13 * b := by
  have ellLe := tradeoffWidth_le_self_of_effective effective
  unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
  unfold Canonical.PublicResourceBounds.nearestPlaneEventBound
  norm_num
  nlinarith

private theorem candidateScanEventBound_le_of_effective {b : Nat}
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
  have oneLeSquare : 1 ≤ b ^ 2 := by nlinarith
  have innerLe :
      178 +
          Canonical.PublicResourceBounds.coordinateWidth b * (8 * b + 11) ≤
        2 ^ 28 * b ^ 2 := by
    norm_num at productLe ⊢
    nlinarith
  have scaledLe := Nat.mul_le_mul_left 404685 innerLe
  unfold Canonical.PublicResourceBounds.candidateScanEventBound
  norm_num at scaledLe ⊢
  nlinarith

private theorem quadraticEventBound_le_of_effective {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.quadraticEventBound b ≤
      2 ^ 29 * b := by
  have positive : 1 ≤ b := by
    unfold RSA.GeneratorOrder.effectiveCutoffBits at effective
    omega
  have coordinateLe := coordinateWidth_le_of_effective effective
  unfold Canonical.PublicResourceBounds.quadraticEventBound
  norm_num at coordinateLe ⊢
  nlinarith

private theorem recoveryEventBound_le_of_effective {b : Nat}
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
  have oneLeSquare : 1 ≤ b ^ 2 := by nlinarith
  have linearLeSquare : b ≤ b ^ 2 := by nlinarith
  have bodyLe :
      13 +
          ((Canonical.PublicResourceBounds.nearestPlaneEventBound b + (b + 4) +
              Canonical.PublicResourceBounds.modularSetupEventBound b +
                Canonical.PublicResourceBounds.candidateScanEventBound b) +
            Canonical.PublicResourceBounds.quadraticEventBound b) ≤
        2 ^ 49 * b ^ 2 := by
    norm_num at modularLe nearestLe candidateLe quadraticLe ⊢
    omega
  have scaledLe := Nat.mul_le_mul_left 120 bodyLe
  unfold Canonical.PublicResourceBounds.recoveryEventBound
  norm_num at modularLe scaledLe ⊢
  omega

set_option maxHeartbeats 800000 in
-- The quartic comparison normalizes the complete scalar batch expression.
/-- In the analytically effective same-bit range, the historical scalar batch
expression has a width-only quartic bound. -/
theorem batchEventBound_le_twoPow54_quartic {b : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ b) :
    Canonical.PublicResourceBounds.batchEventBound b ≤ 2 ^ 54 * b ^ 4 := by
  have widthAtLeast : 512 ≤ b := by
    simpa only [RSA.GeneratorOrder.effectiveCutoffBits] using effective
  have memberLe := memberEventBound_le_quartic_of_effective effective
  have recoveryLe := recoveryEventBound_le_of_effective effective
  have ellLe := tradeoffWidth_le_self_of_effective effective
  have positive : 1 ≤ b := by omega
  have oneLeSquare : 1 ≤ b ^ 2 := by nlinarith
  have linearLeSquare : b ≤ b ^ 2 := by nlinarith
  have squareLeQuartic : b ^ 2 ≤ b ^ 4 := by
    calc
      b ^ 2 = b ^ 2 * 1 := by simp
      _ ≤ b ^ 2 * b ^ 2 := Nat.mul_le_mul_left (b ^ 2) oneLeSquare
      _ = b ^ 4 := by ring
  have oneLeQuartic : 1 ≤ b ^ 4 := oneLeSquare.trans squareLeQuartic
  have linearLeQuartic : b ≤ b ^ 4 := linearLeSquare.trans squareLeQuartic
  have widthSquareAtLeast : 2 ^ 18 ≤ b ^ 2 := by
    norm_num
    nlinarith
  have recoveryQuartic :
      Canonical.PublicResourceBounds.recoveryEventBound b ≤
        2 ^ 39 * b ^ 4 := by
    calc
      _ ≤ 2 ^ 57 * b ^ 2 := recoveryLe
      _ = (2 ^ 39 * b ^ 2) * 2 ^ 18 := by norm_num; ring
      _ ≤ (2 ^ 39 * b ^ 2) * b ^ 2 :=
        Nat.mul_le_mul_left (2 ^ 39 * b ^ 2) widthSquareAtLeast
      _ = 2 ^ 39 * b ^ 4 := by ring
  have headLe : 88 * b + 180 ≤ 2 ^ 10 * b ^ 4 := by
    norm_num
    omega
  have extraLe :
      b + 2 + 2 * Canonical.PublicResourceBounds.tradeoffWidth b ≤
        4 * b := by
    omega
  have memberAndExtraLe :
      Canonical.PublicResourceBounds.memberEventBound b + b + 2 +
          2 * Canonical.PublicResourceBounds.tradeoffWidth b ≤
        2 ^ 16 * b ^ 4 := by
    norm_num at memberLe ⊢
    omega
  have repetitionLe :
      16 *
          (Canonical.PublicResourceBounds.memberEventBound b + b + 2 +
            2 * Canonical.PublicResourceBounds.tradeoffWidth b) ≤
        2 ^ 20 * b ^ 4 := by
    calc
      _ ≤ 16 * (2 ^ 16 * b ^ 4) :=
        Nat.mul_le_mul_left 16 memberAndExtraLe
      _ = 2 ^ 20 * b ^ 4 := by norm_num; ring
  unfold Canonical.PublicResourceBounds.batchEventBound
  calc
    _ ≤ (2 ^ 10 * b ^ 4 + 2 ^ 20 * b ^ 4) + 2 ^ 39 * b ^ 4 :=
      Nat.add_le_add (Nat.add_le_add headLe repetitionLe) recoveryQuartic
    _ ≤ 2 ^ 54 * b ^ 4 := by
      norm_num
      omega

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel
