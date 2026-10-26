/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Canonical
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Input
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Preservation

/-!
# The actual paid subtraction writes the signed coordinate

This width-parametric proof interprets the actual
`subIntoWordStep` Store update and does not evaluate a 256-bit circuit.
The surrounding unpack and table preparation have separate Store obligations.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution
open QuantumAlg.ClassicalAlgorithms.Modular
open QuantumAlg.ClassicalAlgorithms.EllipticCurve
open QuantumAlg.ClassicalRoutines.EllipticCurve

noncomputable section

private lemma word_eq_of_toNat_eq {width : Nat}
    (left right : CShape.Word width) (same : left.toNat = right.toNat) :
    left = right := by
  cases left with
  | unsignedWord left =>
    cases right with
    | unsignedWord right =>
      exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- The actual native subtraction step writes exactly the negative coordinate's number. -/
lemma subIntoWord_signedCoordinate_toNat
    {model : ExecutionModel} [BitWord.Selected model]
    {environment : model.Environment} {ctx : RuntimeCtx model.kind} {width : Nat}
    (curve : CurveSpec width)
    (zeroInput targetY : CInputRef ctx (.unsignedWord width))
    (signedY : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (y : ZMod curve.field.modulus)
    (zeroRead : (store.read zeroInput).toNat = 0)
    (targetRead : (store.read targetY).toNat = (coordinateWord curve y).val) :
    ((Field.Native.subIntoWordStep (model := model) (environment := environment)
      curve.field zeroInput targetY signedY store).1.read
        (QuantumAlg.ClassicalRoutines.Modular.Reduce.Native.reductionRead signedY)).toNat =
      (coordinateWord curve (-y)).val := by
  have canonical : (store.read targetY).toNat < curve.field.modulus := by
    rw [targetRead, coordinateWord_val]
    exact ZMod.val_lt y
  calc
    _ = ((store.read zeroInput).toNat + curve.field.modulus -
        (store.read targetY).toNat) % curve.field.modulus :=
      Field.Native.subIntoWord_toNat (model := model) (environment := environment)
        curve.field zeroInput targetY signedY store canonical
    _ = (coordinateWord curve (-y)).val := by
      simpa only [zeroRead, targetRead] using coordinateWord_neg_value curve y

/-- The complete written word is the canonical negative-Y word, not just congruent modulo p. -/
lemma subIntoWord_signedCoordinate_word
    {model : ExecutionModel} [BitWord.Selected model]
    {environment : model.Environment} {ctx : RuntimeCtx model.kind} {width : Nat}
    (curve : CurveSpec width)
    (zeroInput targetY : CInputRef ctx (.unsignedWord width))
    (signedY : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (y : ZMod curve.field.modulus)
    (zeroRead : (store.read zeroInput).toNat = 0)
    (targetRead : (store.read targetY).toNat = (coordinateWord curve y).val) :
    (Field.Native.subIntoWordStep (model := model) (environment := environment)
      curve.field zeroInput targetY signedY store).1.read
        (QuantumAlg.ClassicalRoutines.Modular.Reduce.Native.reductionRead signedY) =
      .unsignedWord (coordinateWord curve (-y)) := by
  apply word_eq_of_toNat_eq
  simpa only [CShape.Value.toNat] using
    subIntoWord_signedCoordinate_toNat (model := model) (environment := environment)
      curve zeroInput targetY signedY store y zeroRead targetRead

open QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
open QuantumAlg.ClassicalRoutines.Modular.NativePower

variable {model : ExecutionModel} [BitWord.Selected model]
  {environment : model.Environment} {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The paid negative-Y word feeds both unchanged point-base families. -/
lemma pairedBases_after_paid_signed_y
    (frame : WindowTables.Outer.Frame ctx width) (curve : CurveSpec width)
    (firstX firstY secondX targetY zeroInput : CInputRef ctx (.unsignedWord width))
    (signedY : CWriteRef ctx (.unsignedWord width))
    (before : Store ctx × model.HiddenState)
    (first target : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (targetOrder : addOrderOf target.toMathlib = order)
    (loaded : before.1.read (wordRead frame.coordinates.modulus) =
      .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.coordinates.curveA).toNat :
      ZMod curve.field.modulus) = curve.curve.a)
    (zeroRead : (before.1.read zeroInput).toNat = 0)
    (firstYFree : frame.coordinates.x.key ∉ firstY.storageKeys)
    (secondXFree : WindowTables.Outer.Preparation.OutputFree frame.coordinates secondX)
    (signedYFree : WindowTables.Outer.Preparation.OutputFree frame.coordinates
      (.storage signedY.toCStorageRef))
    (outputModulusFree : signedY.key ∉
      (wordRead frame.coordinates.modulus).storageKeys)
    (outputCurveFree : signedY.key ∉ frame.coordinates.curveA.storageKeys)
    (outputFirstXFree : signedY.key ∉ firstX.storageKeys)
    (outputFirstYFree : signedY.key ∉ firstY.storageKeys)
    (outputSecondXFree : signedY.key ∉ secondX.storageKeys)
    (firstXValue : before.1.read firstX =
      .unsignedWord (coordinateWord curve first.x))
    (firstYValue : before.1.read firstY =
      .unsignedWord (coordinateWord curve first.y))
    (secondXValue : before.1.read secondX =
      .unsignedWord (coordinateWord curve target.x))
    (targetYValue : before.1.read targetY =
      .unsignedWord (coordinateWord curve target.y)) :
    let after := (Field.Native.subIntoWordStep (model := model)
      (environment := environment) curve.field zeroInput targetY signedY before.1).1
    let returned := (frame.pairedBasesRecord curve.field firstX firstY secondX
      (.storage signedY.toCStorageRef) environment (after, before.2)).1.1
    (∀ index : Fin 17, CoordinateValue curve
      (returned.read (rowRead frame.coordinates.x (firstBaseRows index)))
      (returned.read (rowRead frame.coordinates.y (firstBaseRows index)))
      ((2 ^ (16 * index.val)) • first.toMathlib)) ∧
    (∀ index : Fin 17, CoordinateValue curve
      (returned.read (rowRead frame.coordinates.x (secondBaseRows index)))
      (returned.read (rowRead frame.coordinates.y (secondBaseRows index)))
      ((2 ^ (16 * index.val)) • (-target.toMathlib))) := by
  let after := (Field.Native.subIntoWordStep (model := model)
    (environment := environment) curve.field zeroInput targetY signedY before.1).1
  have modulusRead : after.read (wordRead frame.coordinates.modulus) =
      before.1.read (wordRead frame.coordinates.modulus) :=
    Field.Native.subIntoWordStep_read_other (environment := environment)
      curve.field zeroInput targetY signedY
      before.1 _ outputModulusFree
  have curveRead : after.read frame.coordinates.curveA =
      before.1.read frame.coordinates.curveA :=
    Field.Native.subIntoWordStep_read_other (environment := environment)
      curve.field zeroInput targetY signedY
      before.1 _ outputCurveFree
  have firstXRead : after.read firstX = before.1.read firstX :=
    Field.Native.subIntoWordStep_read_other (environment := environment)
      curve.field zeroInput targetY signedY
      before.1 _ outputFirstXFree
  have firstYRead : after.read firstY = before.1.read firstY :=
    Field.Native.subIntoWordStep_read_other (environment := environment)
      curve.field zeroInput targetY signedY
      before.1 _ outputFirstYFree
  have secondXRead : after.read secondX = before.1.read secondX :=
    Field.Native.subIntoWordStep_read_other (environment := environment)
      curve.field zeroInput targetY signedY
      before.1 _ outputSecondXFree
  have targetNat : (before.1.read targetY).toNat =
      (coordinateWord curve target.y).val := by
    rw [targetYValue]
    rfl
  have signedRead : after.read (.storage signedY.toCStorageRef) =
      .unsignedWord (coordinateWord curve (-target.y)) := by
    simpa only [QuantumAlg.ClassicalRoutines.Modular.Reduce.Native.reductionRead] using
      subIntoWord_signedCoordinate_word (model := model) (environment := environment)
        curve zeroInput targetY signedY before.1 target.y zeroRead targetNat
  have rowValues := frame.pairedBasesRecord_signed_values curve firstX firstY secondX
    (.storage signedY.toCStorageRef) environment (after, before.2) first target
    order prime large firstOrder targetOrder (modulusRead.trans loaded)
    (by rw [curveRead]; exact curveValue) firstYFree secondXFree signedYFree
    (firstXRead.trans firstXValue) (firstYRead.trans firstYValue)
    (secondXRead.trans secondXValue) signedRead
  exact rowValues.2.2

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
