/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field.Correctness

/-!
# The six-query measured point schedule as an independent field calculation

The ordered table values are -Qx, -Qy, 3Qx, -exceptionalSlope, Qx+1, -Qy.
The first arithmetic call divides the first Y difference by the first X
difference. The square is subtracted before preparing the genuine normal
selector; only that selector enables the second arithmetic multiplication.
The exceptional fourth addition uses the original enable and the negated
normal selector. After clearing the normal selector on that unchanged X,
the enabled reflection is -1-X, followed by the last two table additions.

This is a pure field calculation for arbitrary prime p. It asserts no
circuit action, measurement coefficient, physical workspace restoration or
native ledger. Quantum seed preparation and its adjoint do not change these
two field coordinates and remain separately paid program instructions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

/-- The actual six-column order, with both arithmetic calls and the genuine normal predicate. -/
def fieldSchedule {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Bool) (x y : ZMod p) : ZMod p × ZMod p :=
  let firstX := x + if control then -Q.x else 0
  let firstY := y + if control then -Q.y else 0
  let quotient := if control then firstY / firstX else firstY
  let shiftedX := firstX + if control then 3 * Q.x else 0
  let secondX := if control then shiftedX - quotient ^ 2 else shiftedX
  let normal := normalControl control secondX
  let product := if normal then quotient * secondX else quotient
  let exceptionalY := product + if control && !normal then -exceptionalSlope E Q else 0
  let reflectedX := if control then -1 - secondX else secondX
  let finalX := reflectedX + if control then Q.x + 1 else 0
  let finalY := exceptionalY + if control then -Q.y else 0
  (finalX, finalY)

/-- The chronological schedule gives the same independent total field output. -/
lemma fieldSchedule_eq_fieldOutput {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (control : Bool) (x y : ZMod p) :
    fieldSchedule E Q control x y = fieldOutput E Q control x y := by
  cases control with
  | false => simp [fieldSchedule, fieldOutput, normalControl]
  | true =>
      have firstX : x + -Q.x = firstDifference x Q.x :=
        (sub_eq_add_neg x Q.x).symm
      have firstY : y + -Q.y = y - Q.y := (sub_eq_add_neg y Q.y).symm
      have quotient : (y - Q.y) / firstDifference x Q.x = slope x y Q.x Q.y := rfl
      have difference : firstDifference x Q.x + 3 * Q.x - slope x y Q.x Q.y ^ 2 =
          secondDifference x y Q.x Q.y := rfl
      simp only [fieldSchedule, fieldOutput, ↓reduceIte,
        firstX, firstY, quotient, difference]
      by_cases zero : secondDifference x y Q.x Q.y = 0 <;>
        apply Prod.ext <;> simp [normalControl, zero] <;> ring

/-- Disabled coordinates are arbitrary field values and require no denominator premise. -/
lemma fieldSchedule_false {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (x y : ZMod p) : fieldSchedule E Q false x y = (x, y) :=
  (fieldSchedule_eq_fieldOutput E Q false x y).trans (fieldOutput_false E Q x y)

/-- The original affine active domain suffices, including its reachable exceptional branch. -/
lemma fieldSchedule_true {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    fieldSchedule E Q true P.x P.y = (genericAddX E P Q, genericAddY E P Q) :=
  (fieldSchedule_eq_fieldOutput E Q true P.x P.y).trans (fieldOutput_true E P Q domain)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
