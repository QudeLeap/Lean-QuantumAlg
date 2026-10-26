/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Frame
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Input
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Rows
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Read

/-! # Store predicates established by paid signed-row preparation -/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
open QuantumAlg.Execution QuantumAlg.ClassicalAlgorithms.EllipticCurve
open QuantumAlg.ClassicalRoutines.Modular.NativePower
open QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

variable {kind : ProblemKind} {width : Nat}

/-- The borrowed input is separate from the actual ten retained table cells. -/
def InputFree {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (frame : Frame ctx width) {shape : CShape} (input : CInputRef ctx shape) : Prop :=
  ∀ index : Fin 10, frame.keyAt index ∉ input.storageKeys

/-- The four actual retained constants used by every row of the same table. -/
structure Constants {ctx : RuntimeCtx kind} (frame : WindowTables.Outer.Frame ctx width)
    (curve : CurveSpec width) (store : Store ctx) : Prop where
  modulus : store.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord
  zero : (store.read (.storage frame.zero.toCStorageRef)).toNat = 0
  one : (store.read (.storage frame.one.toCStorageRef)).toNat = 1
  curveA : ((store.read (.storage frame.curveA.toCStorageRef)).toNat :
    ZMod curve.field.modulus) = curve.curve.a

/-- Actual transported reads transfer the four constants to the caller Store. -/
lemma constants_of_readsAs {outer inner : RuntimeCtx kind}
    (frame : WindowTables.Outer.Frame outer width) (curve : CurveSpec width)
    (lift : ClassicalWorkspace.Transport outer inner)
    (source : Store outer) (returned : Store inner) (reads : lift.ReadsAs source returned)
    (constants : Constants (frame.transport lift) curve returned) :
    Constants frame curve source := by
  constructor
  · exact (reads (wordRead frame.modulus)).symm.trans constants.modulus
  · exact (congrArg CShape.Value.toNat
      (reads (.storage frame.zero.toCStorageRef))).symm.trans constants.zero
  · exact (congrArg CShape.Value.toNat
      (reads (.storage frame.one.toCStorageRef))).symm.trans constants.one
  · rw [← reads (.storage frame.curveA.toCStorageRef)]
    exact constants.curveA

/-- Exactly the two seventeen-row value families in one returned Store. -/
def pairedRows {inner : RuntimeCtx kind}
    (curve : CurveSpec width) (frame : WindowTables.Outer.Frame inner width)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (returned : Store inner) : Prop :=
  (∀ index : Fin 17, CoordinateValue curve
    (returned.read (rowRead frame.coordinates.x (firstBaseRows index)))
    (returned.read (rowRead frame.coordinates.y (firstBaseRows index)))
    ((2 ^ (16 * index.val)) • first.toMathlib)) ∧
  (∀ index : Fin 17, CoordinateValue curve
    (returned.read (rowRead frame.coordinates.x (secondBaseRows index)))
    (returned.read (rowRead frame.coordinates.y (secondBaseRows index)))
    ((2 ^ (16 * index.val)) • (-second.toMathlib)))

/-- The named predicate is exactly the two coordinate-value families. -/
lemma pairedRows_iff {inner : RuntimeCtx kind}
    (curve : CurveSpec width) (frame : WindowTables.Outer.Frame inner width)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (returned : Store inner) :
    pairedRows curve frame first second returned ↔
      (∀ index : Fin 17, CoordinateValue curve
        (returned.read (rowRead frame.coordinates.x (firstBaseRows index)))
        (returned.read (rowRead frame.coordinates.y (firstBaseRows index)))
        ((2 ^ (16 * index.val)) • first.toMathlib)) ∧
      (∀ index : Fin 17, CoordinateValue curve
        (returned.read (rowRead frame.coordinates.x (secondBaseRows index)))
        (returned.read (rowRead frame.coordinates.y (secondBaseRows index)))
        ((2 ^ (16 * index.val)) • (-second.toMathlib))) := by
  rfl

/-- The same actual transported row reads transfer both full row families. -/
lemma pairedRows_of_readsAs {outer inner : RuntimeCtx kind}
    (frame : WindowTables.Outer.Frame outer width) (curve : CurveSpec width)
    (lift : ClassicalWorkspace.Transport outer inner)
    (source : Store outer) (returned : Store inner) (reads : lift.ReadsAs source returned)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (rows : pairedRows curve (frame.transport lift) first second returned) :
    pairedRows curve frame first second source := by
  constructor
  · intro index
    rw [← reads (rowRead frame.coordinates.x (firstBaseRows index)),
      ← reads (rowRead frame.coordinates.y (firstBaseRows index))]
    exact rows.1 index
  · intro index
    rw [← reads (rowRead frame.coordinates.x (secondBaseRows index)),
      ← reads (rowRead frame.coordinates.y (secondBaseRows index))]
    exact rows.2 index


end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
