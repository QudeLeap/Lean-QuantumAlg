/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Correctness

/-!
# Independent five-array field and word values for every group point

The identity has five zero words. A finite group point has the original
five mathematical columns, represented canonically in the existing field
word width. These are specification values, not inputs to the actual
construction circuit or an executable source of table entries.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

/-- Independent original five field columns, including five zeros at the group identity. -/
def pointFiveColumns {width : Nat} (curve : CurveSpec width) :
    Point curve → Fin 5 → ZMod curve.field.modulus
  | .zero => fun _ => 0
  | .some x y _ => fiveColumns curve x y

/-- The canonical actual word requested by each independent field-column specification. -/
def pointFiveWords {width : Nat} (curve : CurveSpec width) (point : Point curve)
    (column : Fin 5) : CShape.Word width :=
  CShape.wordOfNat width (pointFiveColumns curve point column).val

/-- Every specified finite field value fits the original physical word without truncation. -/
lemma pointFiveWords_toNat {width : Nat} (curve : CurveSpec width) (point : Point curve)
    (column : Fin 5) :
    (pointFiveWords curve point column).toNat = (pointFiveColumns curve point column).val := by
  let _ : NeZero curve.field.modulus := ⟨Nat.ne_of_gt (modulusSpec_modulus_pos curve.field)⟩
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt _) curve.field.le_capacity)

/-- Original canonical coordinate words identify exactly the independent point columns. -/
lemma CoordinateValue.pointFiveColumns_eq {width : Nat} (curve : CurveSpec width)
    (x y : CShape.Word width) (point : Point curve) (value : CoordinateValue curve x y point) :
    pointFiveColumns curve point = fiveColumns curve x.toNat y.toNat := by
  rw [← value.represents]
  rfl

namespace TableFrame

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

private lemma unsignedWord_toNat_injective :
    Function.Injective (fun value : CShape.Word width => value.toNat) := by
  intro first second same
  cases first with
  | unsignedWord first =>
      cases second with
      | unsignedWord second =>
          exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- Each actual row and physical column contains the canonical requested group-table word. -/
def TableValue (curve : CurveSpec width) (frame : TableFrame ctx width length)
    (point : Point curve) (store : Store ctx) : Prop :=
  ∀ row : Fin length, ∀ column : Fin 5,
    store.read (rowRead (frame.finishColumns column) row) =
      pointFiveWords curve (row.val • point) column

/-- Canonical actual final-row field values determine exactly the requested physical words. -/
lemma FinishedRowValue.words (curve : CurveSpec width) (frame : TableFrame ctx width length)
    (row : Fin length) (store : Store ctx) (x y : CShape.Word width) (point : Point curve)
    (input : CoordinateValue curve x y point)
    (finished : FinishedRowValue curve frame row store x.toNat y.toNat) (column : Fin 5) :
    store.read (rowRead (frame.finishColumns column) row) = pointFiveWords curve point column := by
  have numbers : (store.read (rowRead (frame.finishColumns column) row)).toNat =
      (pointFiveWords curve point column).toNat := by
    rw [pointFiveWords_toNat, input.pointFiveColumns_eq]
    have actual := congrArg (fun value : ZMod curve.field.modulus => value.val)
      (finished.fields column)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (finished.canonical column)] at actual
    exact actual
  exact unsignedWord_toNat_injective numbers

end TableFrame

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
