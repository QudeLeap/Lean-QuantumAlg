/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation.Montgomery

/-!
# Exact group equality represented by the retained Montgomery coordinate words

The actual coordinate pair uses the original Montgomery word encoding and
explicit equality of widths. Multiplication by the original radix unit is
injective. Consequently equality of the retained finite words is exactly
equality of the represented affine points in the original full curve group.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredPointAddition ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open GenericPointAddition.InPlace

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

/-- The actual two retained words are the original width-transported Montgomery coordinates. -/
def montgomeryCoordinates (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (point : AffinePoint E) :
    Fin (2 ^ p.size) × Fin (2 ^ p.size) :=
  (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
    (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits point.x),
   Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
    (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits point.y))

/-- The actual retained coordinate words denote exactly the two radix-scaled field values. -/
theorem montgomeryCoordinates_fieldWords (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (point : AffinePoint E) :
    montgomeryCoordinates fieldTail sameWidth fits point =
      (fieldWord ((2 : ZMod p) ^ fieldTail.succ * point.x),
        fieldWord ((2 : ZMod p) ^ fieldTail.succ * point.y)) :=
  Prod.ext (montgomeryWord_fieldWord fieldTail sameWidth fits point.x)
    (montgomeryWord_fieldWord fieldTail sameWidth fits point.y)

/-- The actual paired input contains precisely these two words beside its original exponents. -/
theorem pairedMontgomeryInput_coordinates (fieldTail exponentWidth : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (point : AffinePoint E) (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    pairedMontgomeryInput fieldTail exponentWidth sameWidth fits point branch =
      inputLabel p.size (2 * exponentWidth) (pairedExponentInput p exponentWidth branch)
        (montgomeryCoordinates fieldTail sameWidth fits point).1
        (montgomeryCoordinates fieldTail sameWidth fits point).2 := rfl

/-- Retained Montgomery word equality is exactly equality in the original curve group. -/
theorem montgomeryCoordinates_eq_iff_group (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (left right : AffinePoint E) :
    montgomeryCoordinates fieldTail sameWidth fits left =
        montgomeryCoordinates fieldTail sameWidth fits right ↔
      left.toGroupPoint = right.toGroupPoint := by
  constructor
  · intro same
    rw [montgomeryCoordinates_fieldWords, montgomeryCoordinates_fieldWords] at same
    have injective : Function.Injective
        (fun value : ZMod p => fieldWord ((2 : ZMod p) ^ fieldTail.succ * value)) := by
      intro first second equality
      have multiplied := congrArg (fun word : Fin (2 ^ p.size) => (word.val : ZMod p)) equality
      simp only [fieldWord_cast] at multiplied
      rw [← Semantics.radixUnit_coe p fieldTail.succ odd] at multiplied
      exact (Semantics.radixUnit p fieldTail.succ odd).mul_right_inj.mp multiplied
    exact congrArg AffinePoint.toGroupPoint (AffinePoint.ext_coordinates left right
      (injective (congrArg Prod.fst same)) (injective (congrArg Prod.snd same)))
  · intro same
    have underlying := congrArg GroupPoint.toMathlib same
    change left.toMathlib = right.toMathlib at underlying
    cases left with
    | mk leftX leftY leftNonsingular =>
        cases right with
        | mk rightX rightY rightNonsingular =>
            simp only [AffinePoint.toMathlib] at underlying
            cases underlying
            rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
