/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Input
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Selection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Seed
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Prepare
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field.Columns.Transport

/-!
# Inputs and affine boundary of the actual constructed-table point driver

The contracts name the original caller reads, feedback references and complete
physical point coordinates. They are independent of an instrument certificate
or a proof of the driver's action.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve.WindowTables
open QuantumAlg.ClassicalRoutines.Modular.NativePower
open Sampling

variable {ctx : RuntimeCtx .quantum}

attribute [local irreducible] modulus

def driverScratchReferences (parameters : Driver.Parameters ctx)
    {parityCount : Nat} (scratch : Storage.Frame ctx 256 parityCount)
    (position : Fin (2 ^ parameters.lowWidth) → Fin parityCount) : Prop :=
  parameters.output = scratch.output ∧
  parameters.mask = scratch.mask ∧
  parameters.parity = (fun index => scratch.parity (position index)) ∧
  parameters.temporary = scratch.temporary

def tableInputValues {wordWidth window : Nat}
    (table : TableFrame ctx wordWidth (2 ^ window))
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec wordWidth)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (store : Store ctx) : Prop :=
  store.read (ClassicalRoutines.Modular.NativePower.wordRead table.modulus) =
    .unsignedWord curve.field.extendedWord ∧
  (store.read table.zero).toNat = 0 ∧
  (store.read table.one).toNat = 1 ∧
  ((store.read table.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a ∧
  CoordinateValue curve (store.read table.baseX) (store.read table.baseY) point

def driverReadValues {wordWidth : Nat}
    (frame : Outer.Frame ctx wordWidth) (curve : CurveSpec wordWidth)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)
    (read : (shape : CShape) → CInputRef ctx shape → CShape.Value shape) : Prop :=
  read _ (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord ∧
  (read _ (.storage frame.zero.toCStorageRef)).toNat = 0 ∧
  (read _ (.storage frame.one.toCStorageRef)).toNat = 1 ∧
  ((read _ (.storage frame.curveA.toCStorageRef)).toNat :
    ZMod curve.field.modulus) = curve.curve.a ∧
  CoordinateValue curve (read _ (rowRead frame.x row))
    (read _ (rowRead frame.y row)) point

def driverInputValues {wordWidth : Nat}
    (frame : Outer.Frame ctx wordWidth) (curve : CurveSpec wordWidth)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)
    (before : Store ctx) : Prop :=
  driverReadValues frame curve point row (fun _ input => before.read input)

private lemma driverTransportReads_eq {inner : RuntimeCtx .quantum}
    (lift : Transport ctx inner) (before : Store ctx) (current : Store inner)
    (reads : lift.ReadsAs before current) :
    (fun (shape : CShape) (input : CInputRef ctx shape) =>
      current.read (lift.liftInput input)) =
    (fun (shape : CShape) (input : CInputRef ctx shape) => before.read input) := by
  funext shape input
  exact reads input

/-- The actual table's six input projections are the transported original reads. -/
private lemma tableInputValues_tableFrame_read {wordWidth window : Nat}
    (frame : Outer.Frame ctx wordWidth) (curve : CurveSpec wordWidth)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)
    {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
    (cells : Cells inner (Outer.tableShapes wordWidth (2 ^ window)))
    (distinct : cells.Distinct) (separated : cells.TransportSeparated lift)
    (current : Store inner) :
    tableInputValues (wordWidth := wordWidth) (window := window)
      (frame.tableFrame (width := wordWidth) (length := 2 ^ window)
        lift cells distinct separated row) curve point current =
      driverReadValues frame curve point row
        (fun _ input => current.read (lift.liftInput input)) := by
  unfold tableInputValues driverReadValues
  rfl

attribute [local irreducible] driverReadValues

/-- Retained reads transport the same six conditions together, at arbitrary widths. -/
private lemma driverInputValues_transport {wordWidth window : Nat}
    (frame : Outer.Frame ctx wordWidth) (curve : CurveSpec wordWidth)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)
    (before : Store ctx) (values : driverInputValues frame curve point row before)
    {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
    (cells : Cells inner (Outer.tableShapes wordWidth (2 ^ window)))
    (distinct : cells.Distinct) (separated : cells.TransportSeparated lift)
    (table : TableFrame inner wordWidth (2 ^ window))
    (same : table = frame.tableFrame (width := wordWidth) (length := 2 ^ window)
      lift cells distinct separated row)
    (current : Store inner) (reads : lift.ReadsAs before current) :
    tableInputValues (wordWidth := wordWidth) (window := window) table curve point current := by
  cases same
  unfold driverInputValues at values
  have readers := driverTransportReads_eq lift before current reads
  have pulled := Eq.mpr (congrArg (driverReadValues frame curve point row) readers) values
  exact Eq.mpr (tableInputValues_tableFrame_read (wordWidth := wordWidth) (window := window)
    frame curve point row lift cells distinct separated current) pulled

def affineRowGeometry {Group : Type} [AddGroup Group]
    (enabled : Bool) (first result selected : Group) : Prop :=
  (enabled = true → first ≠ selected ∧ first ≠ -selected) ∧
    result = first + selected

def driverAffineBlank (curve : CurveSpec 256)
    (sameModulus : curve.field.modulus = modulus)
    (point : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  let transported := MeasuredPointAddition.affineAtModulus curve sameModulus point
  Window.sourceBlank (Residue.input transported.x) (Residue.input transported.y) flags address

def driverAffineInitialized (curve : CurveSpec 256)
    (sameModulus : curve.field.modulus = modulus)
    (point : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  let transported := MeasuredPointAddition.affineAtModulus curve sameModulus point
  Chain.Arithmetic.Call.clearedInitial
    (Residue.input transported.x) (Residue.input transported.y) flags address

def driverAffineEnabled (parameters : Driver.Parameters ctx)
    (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
    (point : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) : Bool :=
  let transported := MeasuredPointAddition.affineAtModulus curve sameModulus point
  Chain.Arithmetic.Call.Endpoint.divisionEnabled parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input transported.x) (Residue.input transported.y) flags address

def driverSelectedRow (parameters : Driver.Parameters ctx)
    (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
    (point : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) :
    Fin (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)) :=
  Window.Tables.selectedRow parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (driverAffineInitialized curve sameModulus point flags address)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver
