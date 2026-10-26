/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Parameters
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Input
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Rows

/-!
# Original input predicates for the actual retained sampler

These declarations specify the same two borrowed points, four constants and
thirty-four signed rows. They depend only on the actual input record and
Store reads; retry contraction and sampling probabilities are separate proofs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Conditional

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve
open ClassicalRoutines.EllipticCurve.WindowTables ClassicalRoutines.Modular.NativePower

private def signedRows {width : Nat} (curve : CurveSpec width)
    (basePoint targetPoint : Pure.Point curve)
    (xs ys : CShape.Value (.fixedVector 34 (.unsignedWord width))) : Prop :=
  (∀ index : Fin 17, CoordinateValue curve
    (xs.get (@firstBaseRows 16 index)) (ys.get (@firstBaseRows 16 index))
    ((2 ^ (16 * index.val)) • basePoint)) ∧
  (∀ index : Fin 17, CoordinateValue curve
    (xs.get (@secondBaseRows 16 index)) (ys.get (@secondBaseRows 16 index))
    ((2 ^ (16 * index.val)) • (-targetPoint)))

private lemma actual_row_read {outer inner : RuntimeCtx .quantum} {width length : Nat}
    (lift : Transport outer inner) (array : CWriteRef outer (.fixedVector length
      (.unsignedWord width))) (store : Store inner) (index : Fin length) :
    store.read (lift.liftInput (rowRead array index)) =
      (store.read (lift.liftInput (.storage array.toCStorageRef))).get index := rfl

private def actualArraysRead {ctx : RuntimeCtx .quantum} (original : Inputs ctx)
    (read : {shape : CShape} → CInputRef ctx shape → CShape.Value shape) :
    CShape.Value (.fixedVector 34 (.unsignedWord 256)) ×
      CShape.Value (.fixedVector 34 (.unsignedWord 256)) :=
  (@read (.fixedVector 34 (.unsignedWord 256)) (.storage original.frame.x.toCStorageRef),
    @read (.fixedVector 34 (.unsignedWord 256)) (.storage original.frame.y.toCStorageRef))

private def rowReadConditions {ctx : RuntimeCtx .quantum} (original : Inputs ctx)
    (basePoint targetPoint : Pure.Point original.curve)
    (read : {shape : CShape} → CInputRef ctx shape → CShape.Value shape) : Prop :=
  let arrays := actualArraysRead original read
  signedRows (width := 256) original.curve basePoint targetPoint arrays.1 arrays.2

private def readConditions {ctx : RuntimeCtx .quantum} (original : Inputs ctx)
    (basePoint targetPoint : Pure.Point original.curve)
    (read : {shape : CShape} → CInputRef ctx shape → CShape.Value shape) : Prop :=
  (PointRepresents original.curve (read original.base) basePoint ∧
    PointRepresents original.curve (read original.target) targetPoint) ∧
  read (wordRead original.frame.modulus) = .unsignedWord original.curve.field.extendedWord ∧
  (read (.storage original.frame.zero.toCStorageRef)).toNat = 0 ∧
  (read (.storage original.frame.one.toCStorageRef)).toNat = 1 ∧
  ((read (.storage original.frame.curveA.toCStorageRef)).toNat :
    ZMod original.curve.field.modulus) = original.curve.curve.a ∧
  rowReadConditions original basePoint targetPoint read

private lemma readConditions_congr {ctx : RuntimeCtx .quantum} (original : Inputs ctx)
    (basePoint targetPoint : Pure.Point original.curve)
    (first second : {shape : CShape} → CInputRef ctx shape → CShape.Value shape)
    (same : ∀ {shape : CShape} (input : CInputRef ctx shape), first input = second input) :
    readConditions original basePoint targetPoint first =
      readConditions original basePoint targetPoint second := by
  have readers : @first = @second := by
    funext shape input
    exact same input
  exact congrArg (readConditions original basePoint targetPoint) readers

private def inputsSupported {outer inner : RuntimeCtx .quantum} {Reference : Register}
    {Label : Type} [Fintype Label] (original : Inputs outer) (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve) (state : State inner Reference Label) :
    Prop :=
  ∀ entry, 0 < (state.block entry).mass →
    readConditions original basePoint targetPoint (fun input => entry.1.read (lift.liftInput input))

end

end Storage.Conditional

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
