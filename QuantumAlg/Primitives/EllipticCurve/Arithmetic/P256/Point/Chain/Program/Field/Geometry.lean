/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Field.Schedule
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Tables.Field

/-!
# The original selected-row group target of the field calculation

The total chronological calculation gives the original conditional affine
sum under its original two active exclusions. The actual complete table
row supplies its own affine addend only in the selected sector. Row zero
keeps the accumulator without inventing finite coordinates for identity.
All curve and point transport uses the same original modulus equality.
This is a mathematical label law, not an instrument or Born theorem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Arithmetic.Call Arithmetic.Call.Endpoint
open ClassicalAlgorithms.EllipticCurve

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

attribute [local irreducible] modulus

private lemma fieldSchedule_affine {p : Nat} (curve : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (control : Bool) (first second : AffinePoint curve)
    (allowed : MeasuredPointAddition.affineAllowed control first second) :
    MeasuredPointAddition.fieldSchedule curve second control first.x first.y =
      if control then (genericAddX curve first second, genericAddY curve first second)
      else (first.x, first.y) := by
  cases control with
  | false =>
      exact MeasuredPointAddition.fieldSchedule_false curve second first.x first.y
  | true =>
      obtain ⟨different, inverseDifferent⟩ := allowed rfl
      exact MeasuredPointAddition.fieldSchedule_true curve first second
        (genericAddDomain_of_ne_of_ne_negate curve first second different inverseDifferent)

attribute [local irreducible] nativeEnableValue fieldProgramOutput

/-- The original active exclusions give the conditional affine coordinates and original flags. -/
lemma fieldProgramOutput_affine (curve : PrimeFieldShortWeierstrass modulus)
    (first second : AffinePoint curve) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false)
    (allowed : MeasuredPointAddition.affineAllowed
      (parameters.nativeEnableValue first.x first.y flags address) first second) :
    letI : Fact modulus.Prime := ⟨curve.prime⟩
    parameters.fieldProgramOutput
        ![-second.x, -second.y, 3 * second.x,
          -MeasuredPointAddition.exceptionalSlope curve second, second.x + 1]
        first.x first.y flags address =
      ((if parameters.nativeEnableValue first.x first.y flags address then
        (genericAddX curve first second, genericAddY curve first second)
      else (first.x, first.y)), flags) := by
  let : Fact modulus.Prime := ⟨curve.prime⟩
  exact (parameters.fieldProgramOutput_fieldSchedule curve second first.x first.y
    flags address normalZero).trans
      (congrArg (fun coordinates : ZMod modulus × ZMod modulus => (coordinates, flags))
        (fieldSchedule_affine curve
          (parameters.nativeEnableValue first.x first.y flags address) first second allowed))

private lemma affineAllowed_transport {width : Nat} (spec : CurveSpec width)
    (target : Nat) (sameModulus : spec.field.modulus = target)
    (control : Bool) (first second : AffinePoint spec.curve)
    (allowed : MeasuredPointAddition.affineAllowed control first second) :
    MeasuredPointAddition.affineAllowed control
      (MeasuredPointAddition.affineAtModulus spec sameModulus first)
      (MeasuredPointAddition.affineAtModulus spec sameModulus second) := by
  subst target
  exact allowed

private lemma genericAdd_result_transport {width : Nat} (spec : CurveSpec width)
    (target : Nat) (sameModulus : spec.field.modulus = target)
    (first second : AffinePoint spec.curve) (domain : GenericAddDomain first second) :
    let curve := MeasuredPointAddition.curveAtModulus spec sameModulus
    let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
    let secondTarget := MeasuredPointAddition.affineAtModulus spec sameModulus second
    let result := genericAddPoint spec.curve first second domain
    let resultTarget := MeasuredPointAddition.affineAtModulus spec sameModulus result
    letI : Fact target.Prime := ⟨curve.prime⟩
    (genericAddX curve firstTarget secondTarget, genericAddY curve firstTarget secondTarget) =
      (resultTarget.x, resultTarget.y) := by
  subst target
  rfl

private def selectedSumTarget {width : Nat} (spec : CurveSpec width)
    (first : AffinePoint spec.curve) (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (row : Nat) : ClassicalAlgorithms.EllipticCurve.Point spec :=
  first.toMathlib + row • base

private def affineFieldTarget {width target : Nat} {Flags : Type}
    (spec : CurveSpec width) (sameModulus : spec.field.modulus = target)
    (first : AffinePoint spec.curve) (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (row : Nat) (flags : Flags) (output : (ZMod target × ZMod target) × Flags) : Prop :=
  ∃ result : AffinePoint spec.curve,
    result.toMathlib = selectedSumTarget spec first base row ∧
      let resultTarget : AffinePoint
          (MeasuredPointAddition.curveAtModulus (target := target) spec sameModulus) :=
        MeasuredPointAddition.affineAtModulus (target := target) spec sameModulus result
      output = ((resultTarget.x, resultTarget.y), flags)

private def SelectedPointFacts (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Window.Raw) : Prop :=
  ∃ selected : AffinePoint spec.curve,
    selected.toMathlib = (Window.Tables.selectedRow stream width bounded state).val • base ∧
      let targetCurve := MeasuredPointAddition.curveAtModulus spec sameModulus
      let targetPoint := MeasuredPointAddition.affineAtModulus spec sameModulus selected
      letI : Fact modulus.Prime := ⟨targetCurve.prime⟩
      ∀ column : Fin 5,
        Window.Tables.selectedFieldColumn spec base stream width bounded state column =
          ![-targetPoint.x, -targetPoint.y, 3 * targetPoint.x,
            -MeasuredPointAddition.exceptionalSlope targetCurve targetPoint,
            targetPoint.x + 1] column

private def TargetColumns {width target : Nat} (spec : CurveSpec width)
    (sameModulus : spec.field.modulus = target) (point : AffinePoint spec.curve)
    (columns : Fin 5 → ZMod target) : Prop :=
  let curve := MeasuredPointAddition.curveAtModulus (target := target) spec sameModulus
  let targetPoint := MeasuredPointAddition.affineAtModulus (target := target)
    spec sameModulus point
  letI : Fact target.Prime := ⟨curve.prime⟩
  ∀ column : Fin 5, columns column =
    ![-targetPoint.x, -targetPoint.y, 3 * targetPoint.x,
      -MeasuredPointAddition.exceptionalSlope curve targetPoint, targetPoint.x + 1] column

attribute [local irreducible] SelectedPointFacts

private lemma selected_point_facts (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Window.Raw) (order : Nat)
    (original : addOrderOf base = order) (tableFits : 2 ^ (width + 1) < order)
    (active : Window.QueryInsertion.querySelected stream width bounded false state = true) :
    SelectedPointFacts spec base sameModulus stream width bounded state := by
  unfold SelectedPointFacts
  exact Tables.selectedAffinePoint_fieldColumns spec base sameModulus stream width bounded
    state order original tableFits active

private lemma affineAllowed_from_row {width : Nat} (spec : CurveSpec width)
    (first second : AffinePoint spec.curve)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec) (row : Nat)
    (represents : second.toMathlib = row • base)
    (exclusions : first.toMathlib ≠ row • base ∧ first.toMathlib ≠ -(row • base)) :
    MeasuredPointAddition.affineAllowed true first second := by
  intro _
  constructor
  · intro same
    exact exclusions.1 ((congrArg AffinePoint.toMathlib same).trans represents)
  · intro same
    apply exclusions.2
    exact (congrArg AffinePoint.toMathlib same).trans
      ((AffinePoint.negate_toMathlib second).trans (congrArg Neg.neg represents))

private lemma affineFieldTarget_addition {width target : Nat} {Flags : Type}
    (spec : CurveSpec width) (sameModulus : spec.field.modulus = target)
    (first second : AffinePoint spec.curve)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec) (row : Nat) (flags : Flags)
    (represents : second.toMathlib = row • base)
    (allowed : MeasuredPointAddition.affineAllowed true first second) :
    let curve := MeasuredPointAddition.curveAtModulus (target := target) spec sameModulus
    let firstTarget := MeasuredPointAddition.affineAtModulus (target := target)
      spec sameModulus first
    let secondTarget := MeasuredPointAddition.affineAtModulus (target := target)
      spec sameModulus second
    letI : Fact target.Prime := ⟨curve.prime⟩
    affineFieldTarget spec sameModulus first base row flags
      ((genericAddX curve firstTarget secondTarget, genericAddY curve firstTarget secondTarget),
        flags) := by
  obtain ⟨different, inverseDifferent⟩ := allowed rfl
  have domain := genericAddDomain_of_ne_of_ne_negate spec.curve first second
    different inverseDifferent
  unfold affineFieldTarget
  refine ⟨genericAddPoint spec.curve first second domain, ?_, ?_⟩
  · dsimp only [selectedSumTarget]
    exact (genericAdd_group_law_mathlib spec.curve first second domain).symm.trans
      (congrArg (fun point => first.toMathlib + point) represents)
  · exact congrArg (fun coordinates => (coordinates, flags))
      (genericAdd_result_transport spec target sameModulus first second domain)

private lemma affineFieldTarget_self {width target : Nat} {Flags : Type}
    (spec : CurveSpec width) (sameModulus : spec.field.modulus = target)
    (first : AffinePoint spec.curve) (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (row : Nat) (flags : Flags) (rowZero : row = 0) :
    let firstTarget := MeasuredPointAddition.affineAtModulus (target := target)
      spec sameModulus first
    affineFieldTarget spec sameModulus first base row flags
      ((firstTarget.x, firstTarget.y), flags) := by
  unfold affineFieldTarget
  refine ⟨first, ?_, rfl⟩
  simp only [selectedSumTarget, rowZero, zero_nsmul, add_zero]

attribute [local irreducible] affineFieldTarget clearedInitial Residue.input
  Window.Tables.selectedRow Window.Tables.selectedFieldColumn
  MeasuredPointAddition.affineAtModulus

attribute [local irreducible] TargetColumns

private lemma property_of_output_eq {Value : Type} (property : Value → Prop)
    (left right : Value) (same : left = right) (holds : property right) : property left := by
  cases same
  exact holds

private lemma pair_if_true {Value Flags : Type} (control : Bool)
    (active inactive : Value) (flags : Flags) (selected : control = true) :
    ((if control then active else inactive), flags) = (active, flags) := by
  cases control with
  | false => cases selected
  | true => rfl

private lemma fieldProgramOutput_active (curve : PrimeFieldShortWeierstrass modulus)
    (first second : AffinePoint curve) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false)
    (allowed : MeasuredPointAddition.affineAllowed true first second)
    (active : parameters.nativeEnableValue first.x first.y flags address = true) :
    letI : Fact modulus.Prime := ⟨curve.prime⟩
    ∀ columns : Fin 5 → ZMod modulus,
      columns = ![-second.x, -second.y, 3 * second.x,
        -MeasuredPointAddition.exceptionalSlope curve second, second.x + 1] →
      parameters.fieldProgramOutput columns first.x first.y flags address =
        ((genericAddX curve first second, genericAddY curve first second), flags) := by
  let : Fact modulus.Prime := ⟨curve.prime⟩
  intro columns sameColumns
  have actual := parameters.fieldProgramOutput_affine curve first second flags address
    normalZero (by intro _; exact allowed rfl)
  have selectedOutput := pair_if_true
    (parameters.nativeEnableValue first.x first.y flags address)
    (genericAddX curve first second, genericAddY curve first second)
    (first.x, first.y) flags active
  exact (congrArg (fun entry => parameters.fieldProgramOutput entry first.x first.y
    flags address) sameColumns).trans (actual.trans selectedOutput)

private lemma row_zero_of_disabled (row : Nat) (selector enabled : Bool)
    (agrees : selector = enabled) (disabled : enabled = false)
    (selected : selector = true ↔ row ≠ 0) : row = 0 := by
  by_contra nonzero
  have yes := selected.mpr nonzero
  have impossible : false = true := disabled.symm.trans (agrees.symm.trans yes)
  cases impossible

private lemma affineFieldTarget_of_coordinates {width target : Nat} {Flags : Type}
    (spec : CurveSpec width) (sameModulus : spec.field.modulus = target)
    (first second : AffinePoint spec.curve)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec) (row : Nat) (flags : Flags)
    (output : (ZMod target × ZMod target) × Flags)
    (represents : second.toMathlib = row • base)
    (allowed : MeasuredPointAddition.affineAllowed true first second)
    (actual :
      let curve := MeasuredPointAddition.curveAtModulus spec sameModulus
      let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
      let secondTarget := MeasuredPointAddition.affineAtModulus spec sameModulus second
      letI : Fact target.Prime := ⟨curve.prime⟩
      output = ((genericAddX curve firstTarget secondTarget,
        genericAddY curve firstTarget secondTarget), flags)) :
    affineFieldTarget spec sameModulus first base row flags output := by
  subst target
  exact property_of_output_eq
    (affineFieldTarget spec rfl first base row flags) _ _ actual
    (affineFieldTarget_addition spec rfl first second base row flags represents allowed)

private lemma affineFieldTarget_of_identity {width target : Nat} {Flags : Type}
    (spec : CurveSpec width) (sameModulus : spec.field.modulus = target)
    (first : AffinePoint spec.curve) (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (row : Nat) (flags : Flags) (output : (ZMod target × ZMod target) × Flags)
    (rowZero : row = 0)
    (actual :
      let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
      output = ((firstTarget.x, firstTarget.y), flags)) :
    affineFieldTarget spec sameModulus first base row flags output := by
  subst target
  exact property_of_output_eq
    (affineFieldTarget spec rfl first base row flags) _ _ actual
    (affineFieldTarget_self spec rfl first base row flags rowZero)

private lemma target_columns_function {width target : Nat} (spec : CurveSpec width)
    (sameModulus : spec.field.modulus = target) (second : AffinePoint spec.curve)
    (columns : Fin 5 → ZMod target) (values : TargetColumns spec sameModulus second columns) :
    let curve := MeasuredPointAddition.curveAtModulus spec sameModulus
    let secondTarget := MeasuredPointAddition.affineAtModulus spec sameModulus second
    letI : Fact target.Prime := ⟨curve.prime⟩
    columns = ![-secondTarget.x, -secondTarget.y, 3 * secondTarget.x,
      -MeasuredPointAddition.exceptionalSlope curve secondTarget, secondTarget.x + 1] := by
  unfold TargetColumns at values
  exact funext values

private lemma transported_field_output (spec : CurveSpec 256)
    (sameModulus : spec.field.modulus = modulus) (first second : AffinePoint spec.curve)
    (columns : Fin 5 → ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false)
    (allowed : MeasuredPointAddition.affineAllowed true first second)
    (active : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address = true)
    (values : TargetColumns spec sameModulus second columns) :
    let curve := MeasuredPointAddition.curveAtModulus spec sameModulus
    let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
    let secondTarget := MeasuredPointAddition.affineAtModulus spec sameModulus second
    letI : Fact modulus.Prime := ⟨curve.prime⟩
    parameters.fieldProgramOutput columns firstTarget.x firstTarget.y flags address =
      ((genericAddX curve firstTarget secondTarget, genericAddY curve firstTarget secondTarget),
        flags) := by
  exact parameters.fieldProgramOutput_active
    (MeasuredPointAddition.curveAtModulus spec sameModulus)
    (MeasuredPointAddition.affineAtModulus spec sameModulus first)
    (MeasuredPointAddition.affineAtModulus spec sameModulus second) flags address normalZero
    (affineAllowed_transport spec modulus sameModulus true first second allowed)
    active columns (target_columns_function spec sameModulus second columns values)

private lemma input_querySelected (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    Window.QueryInsertion.querySelected parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound false
        (clearedInitial (Residue.input x) (Residue.input y) flags address) =
      parameters.nativeEnableValue x y flags address := by
  simpa only [nativeEnableValue, Bool.false_eq_true, if_false] using
    querySelected_clearedInitial parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound false
      (Residue.input x) (Residue.input y) flags address

private lemma input_row_zero_of_disabled (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address)
    (disabled : parameters.nativeEnableValue x y flags address = false) :
    (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (clearedInitial (Residue.input x) (Residue.input y) flags address)).val = 0 := by
  exact row_zero_of_disabled _ _ _
    (parameters.input_querySelected x y flags address) disabled
    (Window.Tables.querySelected_ordinary_iff parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (clearedInitial (Residue.input x) (Residue.input y) flags address))

private lemma active_field_target (spec : CurveSpec 256)
    (sameModulus : spec.field.modulus = modulus) (first second : AffinePoint spec.curve)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec) (row : Nat)
    (columns : Fin 5 → ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false) (represents : second.toMathlib = row • base)
    (allowed : MeasuredPointAddition.affineAllowed true first second)
    (active : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address = true)
    (values : TargetColumns spec sameModulus second columns) :
    let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
    affineFieldTarget spec sameModulus first base row flags
      (parameters.fieldProgramOutput columns firstTarget.x firstTarget.y flags address) := by
  exact affineFieldTarget_of_coordinates spec sameModulus first second base row flags
    (parameters.fieldProgramOutput columns
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address)
    represents allowed
    (parameters.transported_field_output spec sameModulus first second columns flags address
      normalZero allowed active values)

private def GeometryAtRow (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (first : AffinePoint spec.curve)
    (flags : Frame.Controls) (address : Window.Address) (row : Nat)
    (columns : Fin 5 → ZMod modulus) : Prop :=
    let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
    (parameters.nativeEnableValue firstTarget.x firstTarget.y flags address = true →
      first.toMathlib ≠ row • base ∧ first.toMathlib ≠ -(row • base)) →
      affineFieldTarget spec sameModulus first base row flags
        (parameters.fieldProgramOutput columns firstTarget.x firstTarget.y flags address)

attribute [local irreducible] GeometryAtRow

/-- The original two active exclusions imply the same selected-row group target and coordinates. -/
def SelectedFieldGeometry (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (first : AffinePoint spec.curve)
    (flags : Frame.Controls) (address : Window.Address) : Prop :=
    parameters.GeometryAtRow spec base sameModulus first flags address
      (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (clearedInitial
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).x)
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).y)
        flags address)).val
      (Window.Tables.selectedFieldColumn spec base parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (clearedInitial
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).x)
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).y)
        flags address))

attribute [local irreducible] SelectedFieldGeometry selectedSumTarget

private lemma unselected_field_output (spec : CurveSpec 256)
    (sameModulus : spec.field.modulus = modulus) (first : AffinePoint spec.curve)
    (columns : Fin 5 → ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false)
    (inactive : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address ≠ true) :
    let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
    parameters.fieldProgramOutput columns firstTarget.x firstTarget.y flags address =
      ((firstTarget.x, firstTarget.y), flags) := by
  exact parameters.fieldProgramOutput_false columns
    (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
    (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address normalZero
    (Bool.eq_false_iff.mpr inactive)

private lemma unselected_field_target (spec : CurveSpec 256)
    (sameModulus : spec.field.modulus = modulus) (first : AffinePoint spec.curve)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec) (row : Nat)
    (columns : Fin 5 → ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false) (rowZero : row = 0)
    (inactive : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address ≠ true) :
    let firstTarget := MeasuredPointAddition.affineAtModulus spec sameModulus first
    affineFieldTarget spec sameModulus first base row flags
      (parameters.fieldProgramOutput columns firstTarget.x firstTarget.y flags address) := by
  exact affineFieldTarget_of_identity spec sameModulus first base row flags
    (parameters.fieldProgramOutput columns
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address)
    rowZero
    (parameters.unselected_field_output spec sameModulus first columns flags address
      normalZero inactive)

private lemma geometryAtRow_unselected (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (first : AffinePoint spec.curve)
    (flags : Frame.Controls) (address : Window.Address) (row : Nat)
    (columns : Fin 5 → ZMod modulus) (normalZero : flags.2.1 = false) (rowZero : row = 0)
    (inactive : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address ≠ true) :
    parameters.GeometryAtRow spec base sameModulus first flags address row columns := by
  unfold GeometryAtRow
  intro firstTarget _
  exact parameters.unselected_field_target spec sameModulus first base row columns
    flags address normalZero rowZero inactive

private lemma implication_chain (a b c : Prop) (ha : a)
    (ab : a → b) (bc : b → c) : c :=
  bc (ab ha)

private lemma geometryAtRow_selected (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (first second : AffinePoint spec.curve)
    (flags : Frame.Controls) (address : Window.Address) (row : Nat)
    (columns : Fin 5 → ZMod modulus) (normalZero : flags.2.1 = false)
    (represents : second.toMathlib = row • base)
    (values : TargetColumns spec sameModulus second columns)
    (active : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address = true) :
    parameters.GeometryAtRow spec base sameModulus first flags address row columns := by
  unfold GeometryAtRow
  dsimp only
  intro allowed
  exact implication_chain
    (first.toMathlib ≠ row • base ∧ first.toMathlib ≠ -(row • base))
    (MeasuredPointAddition.affineAllowed true first second)
    (affineFieldTarget spec sameModulus first base row flags
      (parameters.fieldProgramOutput columns
        (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
        (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address))
    (allowed active)
    (affineAllowed_from_row spec first second base row represents)
    (fun originalAllowed => parameters.active_field_target spec sameModulus first second
      base row columns flags address normalZero represents originalAllowed active values)

private lemma fieldProgramOutput_unselected (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (first : AffinePoint spec.curve)
    (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false)
    (inactive : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address ≠ true) :
    parameters.SelectedFieldGeometry spec base sameModulus first flags address := by
  unfold SelectedFieldGeometry
  exact parameters.geometryAtRow_unselected spec base sameModulus first flags address
    (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (clearedInitial
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).x)
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).y)
        flags address)).val
    (Window.Tables.selectedFieldColumn spec base parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (clearedInitial
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).x)
        (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).y)
        flags address)) normalZero
    (parameters.input_row_zero_of_disabled
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address
      (Bool.eq_false_iff.mpr inactive)) inactive

private lemma selected_state_field_target (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (order : Nat)
    (original : addOrderOf base = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (first : AffinePoint spec.curve) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false) (state : Window.Raw)
    (selected : Window.QueryInsertion.querySelected parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound false state = true)
    (active : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address = true) :
    parameters.GeometryAtRow spec base sameModulus first flags address
      (Window.Tables.selectedRow parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound state).val
      (Window.Tables.selectedFieldColumn spec base parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound state) := by
  have selectedBase := selected_point_facts spec base sameModulus
  have selectedStream := selectedBase parameters.stream
  have selectedWidth := selectedStream
    (Nat.add (@Program.Parameters.highRemaining ctx parameters)
      (@Program.Parameters.lowWidth ctx parameters))
  have selectedBound := selectedWidth parameters.addressBound
  have selectedState := selectedBound state
  have found := selectedState order original tableFits selected
  unfold SelectedPointFacts at found
  obtain ⟨second, represents, columnValues⟩ := found
  let columns : Fin 5 → ZMod modulus :=
    Window.Tables.selectedFieldColumn spec base parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound state
  have values : TargetColumns spec sameModulus second columns := by
    unfold TargetColumns
    exact columnValues
  have baseLaw := geometryAtRow_selected (ctx := ctx) parameters spec base sameModulus
    first second flags address
  have rowLaw := baseLaw
    (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound state).val
  have columnLaw := rowLaw columns
  have normalLaw := columnLaw normalZero
  have representedLaw := normalLaw represents
  have valuesLaw := representedLaw values
  have actual := valuesLaw active
  exact actual

private lemma selected_active_field_target (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (order : Nat)
    (original : addOrderOf base = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (first : AffinePoint spec.curve) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false)
    (active : parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address = true) :
    parameters.SelectedFieldGeometry spec base sameModulus first flags address := by
  unfold SelectedFieldGeometry
  exact parameters.selected_state_field_target spec base sameModulus order original tableFits
    first flags address normalZero
    (clearedInitial
      (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).x)
      (Residue.input (MeasuredPointAddition.affineAtModulus spec sameModulus first).y)
      flags address)
    ((parameters.input_querySelected
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address).trans active)
    active

private lemma bool_split (control : Bool) (goal : Prop)
    (enabled : control = true → goal) (disabled : control ≠ true → goal) : goal := by
  cases control with
  | false => exact disabled (by intro impossible; cases impossible)
  | true => exact enabled rfl

/-- The same original selected row yields its exact group sum and complete numerical output. -/
lemma fieldProgramOutput_selected (spec : CurveSpec 256)
    (base : ClassicalAlgorithms.EllipticCurve.Point spec)
    (sameModulus : spec.field.modulus = modulus) (order : Nat)
    (original : addOrderOf base = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (first : AffinePoint spec.curve) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false) :
    parameters.SelectedFieldGeometry spec base sameModulus first flags address := by
  exact bool_split
    (parameters.nativeEnableValue
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).x
      (MeasuredPointAddition.affineAtModulus spec sameModulus first).y flags address)
    (parameters.SelectedFieldGeometry spec base sameModulus first flags address)
    (parameters.selected_active_field_target spec base sameModulus order original tableFits
      first flags address normalZero)
    (parameters.fieldProgramOutput_unselected spec base sameModulus first flags address
      normalZero)

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
