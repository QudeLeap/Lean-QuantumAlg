/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.NumberTheory.Extended
import all QuantumAlg.Util.RSA.ShortLog.Widths

/-!
# Uniform operand-width bridges for short-log lattice arithmetic

The sealed short-log arithmetic traces expose a common operand-magnitude
bound.  This module turns that scalar ledger into the two fixed-width facts
consumed by the literal signed and unsigned routines.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeOperandBounds

open ClassicalAlgorithms.NumberTheory

noncomputable section

/-- The public operand envelope lies strictly below the positive signed
capacity of the common coordinate word. -/
theorem operandWidthBound_lt_signedCapacity (N m ell : Nat) :
    RSA.ShortLogWidths.operandWidthBound N m ell <
      2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) := by
  let bound := RSA.ShortLogWidths.operandWidthBound N m ell
  have exponent : bound ≤ 2 * bound + 1 := by omega
  have powerMonotone : 2 ^ bound ≤ 2 ^ (2 * bound + 1) :=
    Nat.pow_le_pow_right (by norm_num) exponent
  have below : bound < 2 ^ (2 * bound + 1) :=
    bound.lt_two_pow_self.trans_le powerMonotone
  have widthSub : RSA.ShortLogWidths.coordinateWidth N m ell - 1 =
      2 * bound + 1 := by
    dsimp only [bound, RSA.ShortLogWidths.coordinateWidth]
    omega
  rw [widthSub]
  exact below

/-- Every integer below the shared operand-magnitude ledger has an exact
two's-complement representation in the common coordinate word. -/
theorem signedRepresentable_of_natAbs_le_operandWidthBound
    {N m ell : Nat} {value : Int}
    (valueBound : value.natAbs ≤ RSA.ShortLogWidths.operandWidthBound N m ell) :
    XGCD.signedRepresentable (RSA.ShortLogWidths.coordinateWidth N m ell) value := by
  have valueFits : value.natAbs <
      2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) :=
    valueBound.trans_lt (operandWidthBound_lt_signedCapacity N m ell)
  have upperNat :
      (value.natAbs : Int) <
        (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) :=
    Int.ofNat_lt.mpr valueFits
  have capacityCast :
      ((2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) : Int) =
        (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Int) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  unfold XGCD.signedRepresentable
  rw [← capacityCast]
  by_cases nonnegative : 0 ≤ value
  · have absEq : (value.natAbs : Int) = value :=
      Int.natAbs_of_nonneg nonnegative
    rw [absEq] at upperNat
    constructor
    · have capacityNonnegative :
          (0 : Int) ≤
            (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) := by
        positivity
      omega
    · exact upperNat
  · have nonpositive : value ≤ 0 := Int.le_of_not_le nonnegative
    have absEq : (value.natAbs : Int) = -value :=
      Int.ofNat_natAbs_of_nonpos nonpositive
    rw [absEq] at upperNat
    constructor
    · omega
    · have capacityPositive :
          (0 : Int) <
            (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) := by
        positivity
      omega

/-- Every natural below the shared operand-magnitude ledger fits in the
common unsigned coordinate word. -/
theorem nat_lt_wordModulus_of_le_operandWidthBound
    {N m ell value : Nat}
    (valueBound : value ≤ RSA.ShortLogWidths.operandWidthBound N m ell) :
    value < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) := by
  change value < 2 ^ RSA.ShortLogWidths.coordinateWidth N m ell
  have signedFits := operandWidthBound_lt_signedCapacity N m ell
  have exponent :
      RSA.ShortLogWidths.coordinateWidth N m ell - 1 ≤
        RSA.ShortLogWidths.coordinateWidth N m ell := Nat.sub_le _ _
  exact valueBound.trans_lt <|
    signedFits.trans_le (Nat.pow_le_pow_right (by norm_num) exponent)

/-- A signed operand whose binary width is below the shared ledger has an
exact two's-complement representation in the common coordinate word. -/
theorem signedRepresentable_of_size_le_operandWidthBound
    {N m ell : Nat} {value : Int}
    (valueWidth : Nat.size value.natAbs ≤
      RSA.ShortLogWidths.operandWidthBound N m ell) :
    XGCD.signedRepresentable (RSA.ShortLogWidths.coordinateWidth N m ell) value := by
  have valueBelowLedger : value.natAbs <
      2 ^ RSA.ShortLogWidths.operandWidthBound N m ell := Nat.size_le.mp valueWidth
  have exponent : RSA.ShortLogWidths.operandWidthBound N m ell ≤
      RSA.ShortLogWidths.coordinateWidth N m ell - 1 := by
    dsimp only [RSA.ShortLogWidths.coordinateWidth]
    omega
  have valueFits : value.natAbs <
      2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) :=
    valueBelowLedger.trans_le (Nat.pow_le_pow_right (by norm_num) exponent)
  have upperNat :
      (value.natAbs : Int) <
        (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) :=
    Int.ofNat_lt.mpr valueFits
  have capacityCast :
      ((2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) : Int) =
        (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Int) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  unfold XGCD.signedRepresentable
  rw [← capacityCast]
  by_cases nonnegative : 0 ≤ value
  · have absEq : (value.natAbs : Int) = value :=
      Int.natAbs_of_nonneg nonnegative
    rw [absEq] at upperNat
    constructor
    · have capacityNonnegative :
          (0 : Int) ≤
            (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) := by
        positivity
      omega
    · exact upperNat
  · have nonpositive : value ≤ 0 := Int.le_of_not_le nonnegative
    have absEq : (value.natAbs : Int) = -value :=
      Int.ofNat_natAbs_of_nonpos nonpositive
    rw [absEq] at upperNat
    constructor
    · omega
    · have capacityPositive :
          (0 : Int) <
            (2 ^ (RSA.ShortLogWidths.coordinateWidth N m ell - 1) : Nat) := by
        positivity
      omega

/-- An unsigned operand whose binary width is below the shared ledger fits
strictly in the common coordinate word. -/
theorem nat_lt_wordModulus_of_size_le_operandWidthBound
    {N m ell value : Nat}
    (valueWidth : Nat.size value ≤ RSA.ShortLogWidths.operandWidthBound N m ell) :
    value < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) := by
  change value < 2 ^ RSA.ShortLogWidths.coordinateWidth N m ell
  have valueBelowLedger : value <
      2 ^ RSA.ShortLogWidths.operandWidthBound N m ell := Nat.size_le.mp valueWidth
  have exponent : RSA.ShortLogWidths.operandWidthBound N m ell ≤
      RSA.ShortLogWidths.coordinateWidth N m ell := by
    dsimp only [RSA.ShortLogWidths.coordinateWidth]
    omega
  exact valueBelowLedger.trans_le
    (Nat.pow_le_pow_right (by norm_num) exponent)

end

end LatticeOperandBounds
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
