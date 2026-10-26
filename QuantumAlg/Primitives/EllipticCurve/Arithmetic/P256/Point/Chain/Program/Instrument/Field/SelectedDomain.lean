/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Field.Geometry
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Domain

/-!
# The original first-call domain from its same selected table row

The selected affine point, its first column and the original two exclusions
are derived together.
The conclusion is exactly the conditional first-call domain required by
the existing complete point trace. No condition is imposed on its numerator.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Arithmetic.Call.Endpoint
open ClassicalAlgorithms.EllipticCurve

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Residue.input Arithmetic.Call.clearedInitial
  Window.Tables.selectedFieldColumn nativeEnableValue firstFieldState
  PointFieldState.initialized Window.Tables.selectedRow
  MeasuredPointAddition.affineAtModulus SelectedPointFacts

private def pointFieldState_of_affine (inputs : PointFieldTableInputs parameters)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls) : PointFieldState :=
  let target := MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus first
  ⟨target.x, target.y, flags⟩

attribute [local irreducible] pointFieldState_of_affine

private def SelectedAffineExclusions (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (first : AffinePoint inputs.curve.curve)
    (address : Window.Address) : Prop :=
  parameters.nativeEnableValue state.x state.y state.flags address = true →
    first.toMathlib ≠ (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address)).val • inputs.point ∧
    first.toMathlib ≠ -((Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address)).val • inputs.point)

private def FirstFieldDomain (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : Prop :=
  divisionEnabled parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input (parameters.firstFieldState inputs state address).x)
    (Residue.input (parameters.firstFieldState inputs state address).y)
    (parameters.firstFieldState inputs state address).flags address = true →
      ActiveDomain (Residue.input (parameters.firstFieldState inputs state address).x)
        (Residue.input (parameters.firstFieldState inputs state address).y)

attribute [local irreducible] SelectedAffineExclusions FirstFieldDomain

private lemma selectedFacts_of_active
    (inputs : PointFieldTableInputs parameters) (state : PointFieldState)
    (address : Window.Address) (order : Nat)
    (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (active : parameters.nativeEnableValue state.x state.y state.flags address = true) :
    SelectedPointFacts inputs.curve inputs.point inputs.sameModulus
      parameters.stream (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address) := by
  have selected : Window.QueryInsertion.querySelected parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound false
      (state.initialized address) = true := by
    simpa only [PointFieldState.initialized] using
      (parameters.input_querySelected state.x state.y state.flags address).trans active
  exact selected_point_facts inputs.curve inputs.point inputs.sameModulus
    parameters.stream (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (state.initialized address) order original tableFits selected

private def SelectedFirstColumn (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : Prop :=
  ∃ second : AffinePoint inputs.curve.curve,
    second.toMathlib = (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address)).val • inputs.point ∧
    Window.Tables.selectedFieldColumn inputs.curve inputs.point parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address) 0 =
        -(MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus second).x

attribute [local irreducible] SelectedFirstColumn

private lemma selectedFirstColumn_of_active
    (inputs : PointFieldTableInputs parameters) (state : PointFieldState)
    (address : Window.Address) (order : Nat)
    (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (active : parameters.nativeEnableValue state.x state.y state.flags address = true) :
    parameters.SelectedFirstColumn inputs state address := by
  have facts := parameters.selectedFacts_of_active inputs state address order
    original tableFits active
  unfold SelectedPointFacts at facts
  obtain ⟨second, represents, columnValues⟩ := facts
  unfold SelectedFirstColumn
  exact ⟨second, represents, columnValues (0 : Fin 5)⟩

private lemma firstFieldState_domain_of_selected_point
    (inputs : PointFieldTableInputs parameters) (state : PointFieldState)
    (first second : AffinePoint inputs.curve.curve)
    (sameX : state.x =
      (MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus first).x)
    (address : Window.Address)
    (represents : second.toMathlib = (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address)).val • inputs.point)
    (columnZero : Window.Tables.selectedFieldColumn inputs.curve inputs.point parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address) 0 =
        -(MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus second).x)
    (allowed : parameters.SelectedAffineExclusions inputs state first address)
    (active : parameters.nativeEnableValue state.x state.y state.flags address = true) :
    ActiveDomain (Residue.input (parameters.firstFieldState inputs state address).x)
      (Residue.input (parameters.firstFieldState inputs state address).y) := by
  unfold SelectedAffineExclusions at allowed
  have originalAllowed := affineAllowed_from_row inputs.curve first second inputs.point
    (Window.Tables.selectedRow parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address)).val represents (allowed active)
  have targetAllowed := affineAllowed_transport inputs.curve modulus inputs.sameModulus
    true first second originalAllowed
  exact parameters.firstFieldState_activeDomain_of_affine inputs state address
    (MeasuredPointAddition.curveAtModulus inputs.curve inputs.sameModulus)
    (MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus first)
    (MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus second)
    sameX columnZero targetAllowed active

private lemma firstFieldState_domain_of_original_row
    (inputs : PointFieldTableInputs parameters) (state : PointFieldState)
    (first : AffinePoint inputs.curve.curve)
    (sameX : state.x =
      (MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus first).x)
    (address : Window.Address) (order : Nat)
    (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (allowed : parameters.SelectedAffineExclusions inputs state first address)
    (active : parameters.nativeEnableValue state.x state.y state.flags address = true) :
    ActiveDomain (Residue.input (parameters.firstFieldState inputs state address).x)
      (Residue.input (parameters.firstFieldState inputs state address).y) := by
  have facts := parameters.selectedFirstColumn_of_active inputs state address order
    original tableFits active
  unfold SelectedFirstColumn at facts
  obtain ⟨second, represents, columnZero⟩ := facts
  exact parameters.firstFieldState_domain_of_selected_point inputs state first second sameX
    address represents columnZero allowed active

private lemma transport_true_domain (first second : Bool) (domain : Prop)
    (same : first = second) (proved : second = true → domain) : first = true → domain :=
  fun active => proved (same.symm.trans active)

private lemma firstFieldState_domain_from_active
    (inputs : PointFieldTableInputs parameters) (state : PointFieldState)
    (address : Window.Address)
    (proved : parameters.nativeEnableValue state.x state.y state.flags address = true →
      ActiveDomain (Residue.input (parameters.firstFieldState inputs state address).x)
        (Residue.input (parameters.firstFieldState inputs state address).y)) :
    parameters.FirstFieldDomain inputs state address := by
  unfold FirstFieldDomain
  simpa only [nativeEnableValue] using transport_true_domain
    (parameters.nativeEnableValue
      (parameters.firstFieldState inputs state address).x
      (parameters.firstFieldState inputs state address).y
      (parameters.firstFieldState inputs state address).flags address)
    (parameters.nativeEnableValue state.x state.y state.flags address)
    (ActiveDomain (Residue.input (parameters.firstFieldState inputs state address).x)
      (Residue.input (parameters.firstFieldState inputs state address).y))
    (parameters.firstFieldState_enable inputs state address) proved


private lemma firstFieldState_conditionalDomain_of_original_row
    (inputs : PointFieldTableInputs parameters) (state : PointFieldState)
    (first : AffinePoint inputs.curve.curve)
    (sameX : state.x =
      (MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus first).x)
    (address : Window.Address) (order : Nat)
    (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (allowed : parameters.SelectedAffineExclusions inputs state first address) :
    parameters.FirstFieldDomain inputs state address :=
  parameters.firstFieldState_domain_from_active inputs state address
    (parameters.firstFieldState_domain_of_original_row inputs state first sameX address
      order original tableFits allowed)

private lemma pointFieldState_mk_x (x y : ZMod modulus) (flags : Frame.Controls) :
    (PointFieldState.mk x y flags).x = x := rfl

private lemma pointFieldState_of_affine_x (inputs : PointFieldTableInputs parameters)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls) :
    (parameters.pointFieldState_of_affine inputs first flags).x =
      (MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus first).x := by
  unfold pointFieldState_of_affine
  exact pointFieldState_mk_x _ _ flags

private lemma firstFieldState_activeDomain_of_selected_row
    (inputs : PointFieldTableInputs parameters)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (order : Nat)
    (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (allowed : parameters.SelectedAffineExclusions inputs
      (parameters.pointFieldState_of_affine inputs first flags) first address) :
    parameters.FirstFieldDomain inputs
      (parameters.pointFieldState_of_affine inputs first flags) address := by
  exact parameters.firstFieldState_conditionalDomain_of_original_row inputs
    (parameters.pointFieldState_of_affine inputs first flags) first
    (parameters.pointFieldState_of_affine_x inputs first flags)
    address order original tableFits allowed

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
