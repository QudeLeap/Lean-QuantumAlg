/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Specification
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Unpack.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Canonical
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Read

/-!
# Actual returned-Store row values of paid signed preparation

The three Store-value premises describe the actual post-initialization source
Store. A subsequent prefix proof must discharge them from paid initialization and
retained allocation. This module proves the callback row values in its exact
returned Store without changing the circuit or resource contract.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.ClassicalAlgorithms.EllipticCurve
open QuantumAlg.ClassicalAlgorithms.Modular
open QuantumAlg.ClassicalRoutines.Modular.NativePower
open QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {width : Nat}

/-- A typed Store boundary for the exact unchanged callback projection. -/
def callbackStore {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width) (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment)
    (before : Store inner × model.HiddenState) : Store inner :=
  (callbackRecord (model := model) frame spec base target cells distinct lift
    separated environment before).1.1

/-- The typed boundary is precisely the Store returned by the actual callback. -/
lemma callbackStore_eq_callbackRecord {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width) (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment)
    (before : Store inner × model.HiddenState) :
    callbackStore (model := model) frame spec base target cells distinct lift
      separated environment before =
      (callbackRecord (model := model) frame spec base target cells distinct lift
        separated environment before).1.1 := by
  rfl

omit [BitWord.Selected model] in
private lemma scratch_key_separation {inner : RuntimeCtx model.kind}
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct) :
    let scratch := scratchOfCells cells
    scratch.rawBase.key ≠ scratch.rawTarget.key ∧
      scratch.signedY.key ≠ scratch.rawBase.key ∧
      scratch.signedY.key ≠ scratch.rawTarget.key := by
  cases cells with
  | cons rawBase remaining =>
    cases remaining with
    | cons rawTarget remaining =>
      cases remaining with
      | cons signedY remaining =>
        cases remaining
        exact ⟨Ne.symm distinct.1.1, distinct.1.2.1, distinct.2.1.1⟩

omit [BitWord.Selected model] in
private lemma transported_write_avoids_scratch
    {outer inner : RuntimeCtx model.kind} {writtenShape scratchShape : CShape}
    (lift : Transport outer inner) (written : CWriteRef outer writtenShape)
    (scratch : CWriteRef inner scratchShape)
    (avoids : scratch.key ∉
      (lift.liftInput (.storage written.toCStorageRef)).storageKeys) :
    (lift.liftWrite written).key ∉
      (CInputRef.storage scratch.toCStorageRef).storageKeys := by
  rw [lift.liftWrite_input] at avoids
  change scratch.key ∉ [(lift.liftWrite written).key] at avoids
  have opposite : scratch.key ≠ (lift.liftWrite written).key := by
    simpa only [List.mem_singleton] using avoids
  change (lift.liftWrite written).key ∉ [scratch.key]
  simpa only [List.mem_singleton] using opposite.symm

omit [BitWord.Selected model] in
private lemma each_transported_write_avoids_scratch
    {outer inner : RuntimeCtx model.kind} {writtenShape : CShape}
    (cells : Cells inner (scratchShapes width))
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (written : CWriteRef outer writtenShape) :
    let scratch := scratchOfCells cells
    (lift.liftWrite written).key ∉
        (CInputRef.storage scratch.rawBase.toCStorageRef).storageKeys ∧
      (lift.liftWrite written).key ∉
        (CInputRef.storage scratch.rawTarget.toCStorageRef).storageKeys ∧
      (lift.liftWrite written).key ∉
        (CInputRef.storage scratch.signedY.toCStorageRef).storageKeys := by
  have avoids := scratch_avoids_original lift cells separated
    (.storage written.toCStorageRef)
  exact ⟨transported_write_avoids_scratch lift written _ avoids.1,
    transported_write_avoids_scratch lift written _ avoids.2.1,
    transported_write_avoids_scratch lift written _ avoids.2.2⟩

omit [BitWord.Selected model] in
/-- All six table-output keys avoid any input backed by one of the real scratch cells. -/
private lemma outputFree_scratch {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width) (lift : Transport outer inner)
    {scratchShape observedShape : CShape}
    (scratch : CWriteRef inner scratchShape) (observed : CInputRef inner observedShape)
    (sameKeys : observed.storageKeys =
      (CInputRef.storage scratch.toCStorageRef).storageKeys)
    (free : ∀ {shape : CShape} (written : CWriteRef outer shape),
      (lift.liftWrite written).key ∉
        (CInputRef.storage scratch.toCStorageRef).storageKeys) :
    WindowTables.Outer.Preparation.OutputFree (frame.transport lift).coordinates observed := by
  intro key member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sameKeys]
    exact free frame.x
  · rw [sameKeys]
    exact free frame.y
  · rw [sameKeys]
    exact free frame.product
  · rw [sameKeys]
    exact free frame.inverse
  · rw [sameKeys]
    exact free frame.temporary
  · rw [sameKeys]
    exact free frame.slope

omit [BitWord.Selected model] in
/-- The four actual raw Store reads use the same two represented nominal values. -/
private lemma twoUnpackStore_canonical_coordinates
    {outer inner : RuntimeCtx model.kind}
    (curve : CurveSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (source : Store outer) (before : Store inner)
    (reads : lift.ReadsAs source before)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (baseRep : PointRepresents curve (source.read base) first.toMathlib)
    (targetRep : PointRepresents curve (source.read target) second.toMathlib) :
    let scratch := scratchOfCells cells
    let after := WindowTables.Outer.Preparation.twoUnpackStore
      (lift.liftInput base) (lift.liftInput target)
      scratch.rawBase scratch.rawTarget before
    after.read (rawX scratch.rawBase) =
        .unsignedWord (coordinateWord curve first.x) ∧
      after.read (rawY scratch.rawBase) =
        .unsignedWord (coordinateWord curve first.y) ∧
      after.read (rawX scratch.rawTarget) =
        .unsignedWord (coordinateWord curve second.x) ∧
      after.read (rawY scratch.rawTarget) =
        .unsignedWord (coordinateWord curve second.y) := by
  let scratch := scratchOfCells cells
  have rawDistinct := (scratch_key_separation cells distinct).1
  have targetFree := (scratch_avoids_original lift cells separated target).1
  have firstRep : PointRepresents curve
      (before.read (lift.liftInput base)) first.toMathlib := by
    rw [reads base]
    exact baseRep
  have secondRep : PointRepresents curve
      (before.read (lift.liftInput target)) second.toMathlib := by
    rw [reads target]
    exact targetRep
  have firstWords := representedAffine_coordinate_words curve
    (before.read (lift.liftInput base)) first firstRep
  have secondWords := representedAffine_coordinate_words curve
    (before.read (lift.liftInput target)) second secondRep
  have firstReads := WindowTables.Outer.Preparation.twoUnpackStore_base_coordinates
    (lift.liftInput base) (lift.liftInput target)
    scratch.rawBase scratch.rawTarget before rawDistinct
  have secondReads := WindowTables.Outer.Preparation.twoUnpackStore_target_coordinates
    (lift.liftInput base) (lift.liftInput target)
    scratch.rawBase scratch.rawTarget before targetFree
  dsimp only at firstReads secondReads ⊢
  rw [firstWords.1, firstWords.2] at firstReads
  rw [secondWords.1, secondWords.2] at secondReads
  exact ⟨firstReads.1, firstReads.2, secondReads.1, secondReads.2⟩

/-- The exact Store returned by paid native subtraction and paired-base preparation. -/
private def paidPairedStore {inner : RuntimeCtx model.kind}
    (environment : model.Environment)
    (frame : WindowTables.Outer.Frame inner width) (spec : ModulusSpec width)
    (firstX firstY secondX targetY zeroInput : CInputRef inner (.unsignedWord width))
    (signedY : CWriteRef inner (.unsignedWord width))
    (before : Store inner × model.HiddenState) : Store inner :=
  let after := (Field.Native.subIntoWordStep
    (model := model)
    (environment := environment) spec zeroInput targetY signedY before.1).1
  (frame.pairedBasesRecord spec firstX firstY secondX
    (.storage signedY.toCStorageRef) environment (after, before.2)).1.1

/-- The named Store is exactly the actual paid record's Store projection. -/
private lemma paidPairedStore_eq {inner : RuntimeCtx model.kind}
    (environment : model.Environment)
    (frame : WindowTables.Outer.Frame inner width) (spec : ModulusSpec width)
    (firstX firstY secondX targetY zeroInput : CInputRef inner (.unsignedWord width))
    (signedY : CWriteRef inner (.unsignedWord width))
    (before : Store inner × model.HiddenState) :
    paidPairedStore environment frame spec firstX firstY secondX targetY zeroInput
      signedY before =
      let after := (Field.Native.subIntoWordStep
        (model := model)
        (environment := environment) spec zeroInput targetY signedY before.1).1
      (frame.pairedBasesRecord spec firstX firstY secondX
        (.storage signedY.toCStorageRef) environment (after, before.2)).1.1 := by
  rfl

/-- The accepted paid signed-Y theorem as one named same-Store row predicate. -/
private lemma pairedRows_after_paid_signed_y
    {inner : RuntimeCtx model.kind}
    (environment : model.Environment)
    (frame : WindowTables.Outer.Frame inner width) (curve : CurveSpec width)
    (firstX firstY secondX targetY zeroInput : CInputRef inner (.unsignedWord width))
    (signedY : CWriteRef inner (.unsignedWord width))
    (before : Store inner × model.HiddenState)
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
    pairedRows curve frame first target
      (paidPairedStore environment frame curve.field firstX firstY secondX
        targetY zeroInput signedY before) := by
  rw [paidPairedStore_eq]
  exact (pairedRows_iff curve frame first target _).2
    (pairedBases_after_paid_signed_y
      (model := model) (environment := environment)
      frame curve firstX firstY secondX targetY zeroInput signedY before first target
      order prime large firstOrder targetOrder loaded curveValue zeroRead
      firstYFree secondXFree signedYFree outputModulusFree outputCurveFree
      outputFirstXFree outputFirstYFree outputSecondXFree
      firstXValue firstYValue secondXValue targetYValue)

/-- The callback's returned Store is the paid tail on its actual unpacked Store. -/
private lemma callbackStore_eq_paidPairedStore {outer inner : RuntimeCtx model.kind}
    (frame : Frame outer width) (spec : ModulusSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment) (before : Store inner × model.HiddenState) :
    callbackStore frame spec base target cells distinct lift separated environment before =
      paidPairedStore environment (frame.transport lift) spec
        (rawX (scratchOfCells cells).rawBase) (rawY (scratchOfCells cells).rawBase)
        (rawX (scratchOfCells cells).rawTarget) (rawY (scratchOfCells cells).rawTarget)
        (.storage (frame.transport lift).zero.toCStorageRef) (scratchOfCells cells).signedY
        (twoUnpackStore (lift.liftInput base) (lift.liftInput target)
          (scratchOfCells cells).rawBase (scratchOfCells cells).rawTarget before.1, before.2) := by
  rw [callbackStore_eq_callbackRecord, callbackRecord_store, paidPairedStore_eq]

attribute [local irreducible] paidPairedStore callbackStore callbackRecord

omit [BitWord.Selected model] in
private lemma scratch_free {outer inner : RuntimeCtx model.kind}
    (frame : Frame outer width) (cells : Cells inner (scratchShapes width))
    (distinct : cells.Distinct) (lift : Transport outer inner)
    (separated : cells.TransportSeparated lift) :
    let scratch := scratchOfCells cells
    let localFrame := frame.transport lift
    localFrame.coordinates.x.key ∉ (rawY scratch.rawBase).storageKeys ∧
      OutputFree localFrame.coordinates (rawX scratch.rawTarget) ∧
      OutputFree localFrame.coordinates (.storage scratch.signedY.toCStorageRef) ∧
      scratch.signedY.key ∉ (wordRead localFrame.coordinates.modulus).storageKeys ∧
      scratch.signedY.key ∉ localFrame.coordinates.curveA.storageKeys ∧
      scratch.signedY.key ∉ (rawX scratch.rawBase).storageKeys ∧
      scratch.signedY.key ∉ (rawY scratch.rawBase).storageKeys ∧
      scratch.signedY.key ∉ (rawX scratch.rawTarget).storageKeys := by
  let scratch := scratchOfCells cells
  let localFrame := frame.transport lift
  have rawDistinct := scratch_key_separation cells distinct
  have firstYFree : localFrame.coordinates.x.key ∉
      (rawY scratch.rawBase).storageKeys := by
    change (lift.liftWrite frame.x).key ∉
      (CInputRef.storage scratch.rawBase.toCStorageRef).storageKeys
    exact (each_transported_write_avoids_scratch cells lift separated frame.x).1
  have secondXFree : WindowTables.Outer.Preparation.OutputFree localFrame.coordinates
      (rawX scratch.rawTarget) :=
    outputFree_scratch frame lift scratch.rawTarget (rawX scratch.rawTarget) rfl
      (fun written => (each_transported_write_avoids_scratch
        cells lift separated written).2.1)
  have signedYFree : WindowTables.Outer.Preparation.OutputFree localFrame.coordinates
      (.storage scratch.signedY.toCStorageRef) :=
    outputFree_scratch frame lift scratch.signedY
      (.storage scratch.signedY.toCStorageRef) rfl
      (fun written => (each_transported_write_avoids_scratch
        cells lift separated written).2.2)
  have outputModulusFree : scratch.signedY.key ∉
      (wordRead localFrame.coordinates.modulus).storageKeys := by
    change scratch.signedY.key ∉
      (lift.liftInput (wordRead frame.modulus)).storageKeys
    exact (scratch_avoids_original lift cells separated (wordRead frame.modulus)).2.2
  have outputCurveFree : scratch.signedY.key ∉
      localFrame.coordinates.curveA.storageKeys := by
    change scratch.signedY.key ∉
      (lift.liftInput (.storage frame.curveA.toCStorageRef)).storageKeys
    exact (scratch_avoids_original lift cells separated
      (.storage frame.curveA.toCStorageRef)).2.2
  have outputFirstXFree : scratch.signedY.key ∉
      (rawX scratch.rawBase).storageKeys := by
    simpa only [rawX, CInputRef.storageKeys, List.mem_singleton] using rawDistinct.2.1
  have outputFirstYFree : scratch.signedY.key ∉
      (rawY scratch.rawBase).storageKeys := by
    simpa only [rawY, CInputRef.storageKeys, List.mem_singleton] using rawDistinct.2.1
  have outputSecondXFree : scratch.signedY.key ∉
      (rawX scratch.rawTarget).storageKeys := by
    simpa only [rawX, CInputRef.storageKeys, List.mem_singleton] using rawDistinct.2.2
  exact ⟨firstYFree, secondXFree, signedYFree, outputModulusFree, outputCurveFree,
    outputFirstXFree, outputFirstYFree, outputSecondXFree⟩

/-- Both paid row families are in the Store returned by this exact callback. -/
lemma callback_rows_of_post_init_source {outer inner : RuntimeCtx model.kind}
    (frame : WindowTables.Outer.Frame outer width) (curve : CurveSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment)
    (source : Store outer)
    (before : Store inner × model.HiddenState)
    (reads : lift.ReadsAs source before.1)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (targetOrder : addOrderOf second.toMathlib = order)
    (baseRep : PointRepresents curve (source.read base) first.toMathlib)
    (targetRep : PointRepresents curve (source.read target) second.toMathlib)
    (loaded : source.read (wordRead frame.modulus) =
      .unsignedWord curve.field.extendedWord)
    (curveValue : ((source.read (.storage frame.curveA.toCStorageRef)).toNat :
      ZMod curve.field.modulus) = curve.curve.a)
    (zeroRead : (source.read (.storage frame.zero.toCStorageRef)).toNat = 0) :
    let localFrame := frame.transport lift
    let returned : Store inner := callbackStore (model := model) frame curve.field base target
      cells distinct lift separated environment before
    pairedRows curve localFrame first second returned := by
  let scratch := scratchOfCells cells
  let localFrame := frame.transport lift
  let unpacked := WindowTables.Outer.Preparation.twoUnpackStore
    (lift.liftInput base) (lift.liftInput target)
    scratch.rawBase scratch.rawTarget before.1
  have canonical := twoUnpackStore_canonical_coordinates curve base target cells distinct
    lift separated source before.1 reads first second baseRep targetRep
  have preserved {shape : CShape} (observed : CInputRef outer shape) :
      unpacked.read (lift.liftInput observed) = source.read observed := by
    have avoid := scratch_avoids_original lift cells separated observed
    exact (WindowTables.Outer.Preparation.twoUnpackStore_read_other
      (lift.liftInput base) (lift.liftInput target)
      scratch.rawBase scratch.rawTarget before.1 (lift.liftInput observed)
      avoid.1 avoid.2.1).trans (reads observed)
  have loadedHere : unpacked.read (wordRead localFrame.coordinates.modulus) =
      .unsignedWord curve.field.extendedWord := by
    change unpacked.read (lift.liftInput (wordRead frame.modulus)) = _
    exact (preserved (wordRead frame.modulus)).trans loaded
  have curveHere : ((unpacked.read localFrame.coordinates.curveA).toNat :
      ZMod curve.field.modulus) = curve.curve.a := by
    change ((unpacked.read (lift.liftInput
      (.storage frame.curveA.toCStorageRef))).toNat :
      ZMod curve.field.modulus) = curve.curve.a
    rw [preserved (.storage frame.curveA.toCStorageRef)]
    exact curveValue
  have zeroHere : (unpacked.read
      (.storage localFrame.zero.toCStorageRef)).toNat = 0 := by
    change (unpacked.read (lift.liftInput
      (.storage frame.zero.toCStorageRef))).toNat = 0
    rw [preserved (.storage frame.zero.toCStorageRef)]
    exact zeroRead
  obtain ⟨firstYFree, secondXFree, signedYFree, outputModulusFree, outputCurveFree,
    outputFirstXFree, outputFirstYFree, outputSecondXFree⟩ :=
    scratch_free frame cells distinct lift separated
  change unpacked.read (rawX scratch.rawBase) = .unsignedWord (coordinateWord curve first.x) ∧
    unpacked.read (rawY scratch.rawBase) = .unsignedWord (coordinateWord curve first.y) ∧
    unpacked.read (rawX scratch.rawTarget) = .unsignedWord (coordinateWord curve second.x) ∧
    unpacked.read (rawY scratch.rawTarget) =
      .unsignedWord (coordinateWord curve second.y) at canonical
  generalize unpackedEq : unpacked = abstractStore at canonical loadedHere curveHere zeroHere
  have rows := pairedRows_after_paid_signed_y (model := model)
    (environment := environment)
    localFrame curve (rawX scratch.rawBase) (rawY scratch.rawBase)
    (rawX scratch.rawTarget) (rawY scratch.rawTarget)
    (.storage localFrame.zero.toCStorageRef) scratch.signedY
    (abstractStore, before.2) first second order prime large firstOrder targetOrder
    loadedHere curveHere zeroHere firstYFree secondXFree signedYFree
    outputModulusFree outputCurveFree outputFirstXFree outputFirstYFree
    outputSecondXFree canonical.1 canonical.2.1 canonical.2.2.1 canonical.2.2.2
  change pairedRows curve localFrame first second
    (callbackStore frame curve.field base target cells distinct lift separated environment before)
  rw [callbackStore_eq_paidPairedStore]
  change pairedRows curve localFrame first second
    (paidPairedStore environment localFrame curve.field (rawX scratch.rawBase)
      (rawY scratch.rawBase) (rawX scratch.rawTarget) (rawY scratch.rawTarget)
      (.storage localFrame.zero.toCStorageRef) scratch.signedY (unpacked, before.2))
  rw [unpackedEq]
  exact rows

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
