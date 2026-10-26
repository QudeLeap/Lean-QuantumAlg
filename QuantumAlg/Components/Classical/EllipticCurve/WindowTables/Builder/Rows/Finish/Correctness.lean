/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Domain.Exceptional
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Point

/-!
# Original five mathematical columns in the actual final row

The same fifteen-slot record returns canonical words for negative x,
negative y, three x, negative exceptional slope and x plus one. Its slope
uses the actual stored inverse of the preceding negative tangent batch.
The original point order proves the exceptional denominator is nonzero.
The identity row is handled by its separate actual five-zero program.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

/-- The original five nonidentity table values, independently of their construction program. -/
def fiveColumns {width : Nat} (curve : CurveSpec width)
    (x y : ZMod curve.field.modulus) : Fin 5 → ZMod curve.field.modulus :=
  ![-x, -y, 3 * x, -exceptionalSlope curve x y, x + 1]

namespace TableFrame

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Canonical words in the original physical five columns with their specified field values. -/
structure FinishedRowValue (curve : CurveSpec width) (frame : TableFrame ctx width length)
    (row : Fin length) (store : Store ctx) (x y : ZMod curve.field.modulus) : Prop where
  canonical : ∀ column : Fin 5,
    (store.read (rowRead (frame.finishColumns column) row)).toNat < curve.field.modulus
  fields : ∀ column : Fin 5,
    ((store.read (rowRead (frame.finishColumns column) row)).toNat : ZMod curve.field.modulus) =
      fiveColumns curve x y column

variable (frame : TableFrame ctx width length)

/-- The actual returned Store has all five original canonical mathematical values. -/
lemma finishStore_rowValue (curve : CurveSpec width) (row : Fin length) (store : Store ctx)
    (point : Point curve)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (zeroValue : (store.read frame.zero).toNat = 0)
    (oneValue : (store.read frame.one).toNat = 1)
    (curveValue : ((store.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (input : CoordinateValue curve (store.read (rowRead frame.arrays.x row))
      (store.read (rowRead frame.arrays.y row)) point)
    (large : 3 < addOrderOf point)
    (inverseValue : ((store.read (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) =
      (-((2 : ZMod curve.field.modulus) *
        (store.read (rowRead frame.arrays.y row)).toNat))⁻¹) :
    FinishedRowValue curve frame row (frame.finishStore curve.field row store)
      (store.read (rowRead frame.arrays.x row)).toNat
      (store.read (rowRead frame.arrays.y row)).toNat := by
  refine ⟨?_, ?_⟩
  · intro column
    rw [frame.finishStore_read_values curve.field row store loaded]
    exact finishWords_canonical curve.field _ _ _ _ _ _ input.xCanonical input.yCanonical column
  · intro column
    rw [frame.finishStore_read_values curve.field row store loaded]
    have finiteOrder : 3 < addOrderOf (.some
        ((store.read (rowRead frame.arrays.x row)).toNat : ZMod curve.field.modulus)
        ((store.read (rowRead frame.arrays.y row)).toNat : ZMod curve.field.modulus)
        input.finite : Point curve) := by
      rw [input.represents]
      exact large
    by_cases fourth : column = 3
    · subst column
      have domains := window_row_denominators_of_order curve _ _ input.finite finiteOrder
      have nonzeroY :
          ((store.read (rowRead frame.arrays.y row)).toNat : ZMod curve.field.modulus) ≠ 0 := by
        intro zeroY
        rw [zeroY, mul_zero, neg_zero] at domains
        exact domains.1 rfl
      have actual := finishWords_cast curve.field
        (store.read (rowRead frame.arrays.x row)) (store.read (rowRead frame.arrays.y row))
        (store.read frame.curveA) (store.read (rowRead frame.arrays.c row))
        (store.read frame.zero) (store.read frame.one) input.xCanonical input.yCanonical
        zeroValue oneValue 3
      change _ = (3 *
        ((store.read (rowRead frame.arrays.x row)).toNat : ZMod curve.field.modulus) ^ 2 +
        (store.read frame.curveA).toNat) *
        (store.read (rowRead frame.arrays.c row)).toNat at actual
      rw [curveValue, inverseValue] at actual
      refine actual.trans ?_
      change _ = -exceptionalSlope curve _ _
      rw [negative_exceptionalSlope_eq_tangent curve _ _ domains.2,
        ShortWeierstrass.doubleSlope_eq_formula curve _ _ (neg_ne_zero.mpr nonzeroY),
        ShortWeierstrass.doubleNumerator, ShortWeierstrass.doubleDenominator, div_eq_mul_inv]
      rw [mul_neg]
    · fin_cases column <;> first
        | exact False.elim (fourth rfl)
        | exact finishWords_cast curve.field _ _ _ _ _ _ input.xCanonical input.yCanonical
            zeroValue oneValue _

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The full actual path-bearing record returns precisely those same five original field values. -/
lemma finishRecord_rowValue (curve : CurveSpec width) (row : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) (point : Point curve)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (zeroValue : (before.1.read frame.zero).toNat = 0)
    (oneValue : (before.1.read frame.one).toNat = 1)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (input : CoordinateValue curve (before.1.read (rowRead frame.arrays.x row))
      (before.1.read (rowRead frame.arrays.y row)) point)
    (large : 3 < addOrderOf point)
    (inverseValue :
      ((before.1.read (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) =
      (-((2 : ZMod curve.field.modulus) *
        (before.1.read (rowRead frame.arrays.y row)).toNat))⁻¹) :
    FinishedRowValue curve frame row (frame.finishRecord curve.field row environment before).1.1
      (before.1.read (rowRead frame.arrays.x row)).toNat
      (before.1.read (rowRead frame.arrays.y row)).toNat := by
  rw [frame.finishRecord_store]
  exact frame.finishStore_rowValue curve row before.1 point loaded zeroValue oneValue curveValue
    input large inverseValue

end TableFrame

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
