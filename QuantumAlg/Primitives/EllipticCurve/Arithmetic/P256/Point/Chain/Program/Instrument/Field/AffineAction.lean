/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.SelectedDomain
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Schedule
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Coverage
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Field.Geometry

/-!
# The actual measured point action at the original selected affine row

The retained table supplies the same affine addend used by the field
schedule. Its original two active exclusions discharge the first division
internally. The five actual phase actions then give the same group sum,
restore the original flags and blank arithmetic workspace, and retain each
arbitrary measured path and external reference. No whole-point action or
success-probability certificate is an assumption.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
namespace Program.Parameters
noncomputable section
open Execution Window.Sampling

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Residue.input Arithmetic.Call.clearedInitial
  Window.sourceBlank PointFieldState.blank PointFieldState.initialized
  pointFieldState_of_affine firstFieldState completeFieldState fieldProgramOutput nativeEnableValue
  InstrumentBranchAction CompletePointFieldAction PointFieldPaths.complete
  pointProgramInstrument QueryOutcome SelectedAffineExclusions FirstFieldDomain
  Window.Tables.selectedRow Window.Tables.selectedFieldColumn
  MeasuredPointAddition.affineAtModulus selectedSumTarget

private def PointFieldResultAction
    (store : Store ctx) (paths : PointFieldPaths parameters services)
    (initial final : PointFieldState) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  parameters.InstrumentBranchAction (Reference := Reference) environment
    (parameters.pointProgramInstrument environment) store (paths.complete parameters)
    (NormalizedVector.invSqrt2 ^ 2048) (initial.blank address) (final.blank address) reference

attribute [local irreducible] PointFieldResultAction

private lemma pointFieldState_mk_y (x y : ZMod modulus) (flags : Frame.Controls) :
    (PointFieldState.mk x y flags).y = y := rfl

private lemma pointFieldState_mk_flags (x y : ZMod modulus) (flags : Frame.Controls) :
    (PointFieldState.mk x y flags).flags = flags := rfl

private lemma pointFieldState_of_affine_y (inputs : PointFieldTableInputs parameters)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls) :
    (parameters.pointFieldState_of_affine inputs first flags).y =
      (MeasuredPointAddition.affineAtModulus inputs.curve inputs.sameModulus first).y := by
  unfold pointFieldState_of_affine
  exact pointFieldState_mk_y _ _ flags

private lemma pointFieldState_of_affine_flags (inputs : PointFieldTableInputs parameters)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls) :
    (parameters.pointFieldState_of_affine inputs first flags).flags = flags := by
  unfold pointFieldState_of_affine
  exact pointFieldState_mk_flags _ _ flags

private lemma pointFieldState_blank_of_labels
    (first second : PointFieldState) (address : Window.Address)
    (same : ((first.x, first.y), first.flags) = ((second.x, second.y), second.flags)) :
    first.blank address = second.blank address := by
  have mapped := congrArg
    (fun output : (ZMod modulus × ZMod modulus) × Frame.Controls =>
      Window.sourceBlank (Residue.input output.1.1) (Residue.input output.1.2)
        output.2 address) same
  simpa only [PointFieldState.blank] using mapped

private lemma completeFieldState_selected_affine
    (inputs : PointFieldTableInputs parameters)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)
    (order : Nat) (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (allowed : parameters.SelectedAffineExclusions inputs
      (parameters.pointFieldState_of_affine inputs first flags) first address) :
    ∃ result : AffinePoint inputs.curve.curve,
      result.toMathlib = selectedSumTarget inputs.curve first inputs.point
        (Window.Tables.selectedRow parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          ((parameters.pointFieldState_of_affine inputs first flags).initialized address)).val ∧
      (parameters.completeFieldState inputs
        (parameters.pointFieldState_of_affine inputs first flags) address).blank address =
          (parameters.pointFieldState_of_affine inputs result flags).blank address := by
  let state : PointFieldState := parameters.pointFieldState_of_affine inputs first flags
  let columns : Fin 5 → ZMod modulus := Window.Tables.selectedFieldColumn
    inputs.curve inputs.point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (state.initialized address)
  have geometry := parameters.fieldProgramOutput_selected inputs.curve inputs.point
    inputs.sameModulus order original tableFits first flags address normalZero
  unfold SelectedFieldGeometry GeometryAtRow at geometry
  dsimp only at geometry
  have originalAllowed := allowed
  unfold SelectedAffineExclusions at originalAllowed
  simp only [PointFieldState.initialized, pointFieldState_of_affine_x,
    pointFieldState_of_affine_y, pointFieldState_of_affine_flags] at originalAllowed
  have target := geometry originalAllowed
  unfold affineFieldTarget at target
  obtain ⟨result, group, coordinates⟩ := target
  have sameOutput : parameters.fieldProgramOutput columns state.x state.y state.flags address =
      (((parameters.pointFieldState_of_affine inputs result flags).x,
        (parameters.pointFieldState_of_affine inputs result flags).y),
        (parameters.pointFieldState_of_affine inputs result flags).flags) := by
    simpa only [columns, state, PointFieldState.initialized, pointFieldState_of_affine_x,
      pointFieldState_of_affine_y, pointFieldState_of_affine_flags] using coordinates
  have labels := (parameters.completeFieldState_schedule inputs state address).trans sameOutput
  have final := pointFieldState_blank_of_labels
    (parameters.completeFieldState inputs state address)
    (parameters.pointFieldState_of_affine inputs result flags) address labels
  refine ⟨result, ?_, final⟩
  simpa only [PointFieldState.initialized, pointFieldState_of_affine_x,
    pointFieldState_of_affine_y, pointFieldState_of_affine_flags] using group

/-- The original two affine exclusions suffice for the same actual measured point action. -/
lemma pointProgramInstrument_table_affine_action (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : ClassicalRoutines.EllipticCurve.WindowTables.TableFrame.TableValue
      inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)
    (order : Nat) (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (allowed : parameters.SelectedAffineExclusions inputs
      (parameters.pointFieldState_of_affine inputs first flags) first address)
    {Reference : Register} (reference : Reference.Index) :
    ∃ result : AffinePoint inputs.curve.curve,
      result.toMathlib = selectedSumTarget inputs.curve first inputs.point
        (Window.Tables.selectedRow parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          ((parameters.pointFieldState_of_affine inputs first flags).initialized address)).val ∧
      parameters.PointFieldResultAction (Reference := Reference) environment store paths
        (parameters.pointFieldState_of_affine inputs first flags)
        (parameters.pointFieldState_of_affine inputs result flags) address reference := by
  let state : PointFieldState := parameters.pointFieldState_of_affine inputs first flags
  have admitted := parameters.firstFieldState_activeDomain_of_selected_row
    inputs first flags address order original tableFits allowed
  unfold FirstFieldDomain at admitted
  have zero : state.flags.2.1 = false := by
    simpa only [state, pointFieldState_of_affine_flags] using normalZero
  have action := parameters.pointProgramInstrument_table_fieldTrace (Reference := Reference)
    environment inputs store values paths state address zero admitted reference
  obtain ⟨result, group, final⟩ := parameters.completeFieldState_selected_affine
    inputs first flags address normalZero order original tableFits allowed
  unfold CompletePointFieldAction at action
  rw [final] at action
  refine ⟨result, group, ?_⟩
  unfold PointFieldResultAction
  exact action

end
end Program.Parameters
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
