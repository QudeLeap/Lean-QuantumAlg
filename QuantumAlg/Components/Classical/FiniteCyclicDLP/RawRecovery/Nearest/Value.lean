/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Scale

/-!
# Exact finite-word nearest scaling

This is the value expression of the paid multiplication, denominator resize
and shift, addition, two divisions and final resize.  The no-overflow proof
applies to the rounded numerator before either division.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

/-- The finite-word value computed by nearest scaling's native instructions. -/
def scaleWordValue {width : Nat} (raw : CShape.Word width)
    (order denominator : CShape.Word (width + 1)) : CShape.Word width :=
  let product := CShape.mulFull width (width + 1) (.product raw order)
  let half := CShape.wordShiftRight (width + (width + 1))
    (CShape.wordResize (width + (width + 1)) denominator)
  let rounded := CShape.wordOfNat (width + (width + 1)) (product.toNat + half.toNat)
  let divided := CShape.divRem (width + (width + 1)) (width + 1)
    (.product rounded denominator)
  let reduced := CShape.divRem (width + (width + 1)) (width + 1)
    (.product divided.first order)
  CShape.wordResize width reduced.second

/-- The finite words compute exact nearest division followed by canonical
modular wrap; all intermediate truncations are proved inactive. -/
lemma scaleWordValue_toNat {width : Nat} (raw : CShape.Word width)
    (order denominator : CShape.Word (width + 1)) (orderPositive : 0 < order.toNat)
    (orderBound : order.toNat ≤ 2 ^ width) (powerValue : denominator.toNat = 2 ^ width) :
    (scaleWordValue raw order denominator).toNat =
      NearestResidue.quotient (raw.toNat * order.toNat) (2 ^ width) % order.toNat := by
  let totalWidth := width + (width + 1)
  have productBound : raw.toNat * order.toNat < 2 ^ totalWidth :=
    ClassicalOp.mulFull_product_lt width (width + 1) (.product raw order)
  have denominatorBound : denominator.toNat < 2 ^ totalWidth := by
    apply denominator.toNat_lt.trans_le
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have halfBound : denominator.toNat / 2 < 2 ^ totalWidth :=
    (Nat.div_le_self _ _).trans_lt denominatorBound
  have roundedBound : raw.toNat * order.toNat + denominator.toNat / 2 < 2 ^ totalWidth := by
    rw [powerValue]
    exact NearestResidue.rounded_numerator_lt width raw.toNat order.toNat raw.toNat_lt orderBound
  have quotientBound : (raw.toNat * order.toNat + denominator.toNat / 2) /
      denominator.toNat < 2 ^ totalWidth := (Nat.div_le_self _ _).trans_lt roundedBound
  have remainderBound : ((raw.toNat * order.toNat + denominator.toNat / 2) /
      denominator.toNat) % order.toNat < 2 ^ width :=
    (Nat.mod_lt _ orderPositive).trans_le orderBound
  have remainderWideBound : ((raw.toNat * order.toNat + denominator.toNat / 2) /
      denominator.toNat) % order.toNat < 2 ^ (width + 1) :=
    remainderBound.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  change (((raw.toNat * order.toNat % 2 ^ totalWidth +
    (denominator.toNat % 2 ^ totalWidth / 2) % 2 ^ totalWidth) % 2 ^ totalWidth /
      denominator.toNat) % 2 ^ totalWidth % order.toNat) % 2 ^ (width + 1) % 2 ^ width = _
  rw [Nat.mod_eq_of_lt productBound, Nat.mod_eq_of_lt denominatorBound,
    Nat.mod_eq_of_lt halfBound, Nat.mod_eq_of_lt roundedBound,
    Nat.mod_eq_of_lt quotientBound, Nat.mod_eq_of_lt remainderWideBound,
    Nat.mod_eq_of_lt remainderBound]
  rw [powerValue]
  rfl

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
