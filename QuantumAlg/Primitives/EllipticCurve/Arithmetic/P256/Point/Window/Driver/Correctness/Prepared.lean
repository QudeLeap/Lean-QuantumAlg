/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Instrument
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Specified
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Final.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification

/-!
# The actual paid table record supplies the same measured affine point action

The five-table builder derives its complete table value from the original
loaded inputs. The point operator then reads that actual returned Store.
Every outcome has the same specified affine target and branch coefficient;
the retained certificate keeps both real Paths and the returned hidden state.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point

namespace Window.Driver

noncomputable section

open QuantumAlg.Execution.Instrument

open Sampling

open Execution ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma tablePrefixInstrument_operator {wordWidth window : Nat}
    (table : TableFrame ctx wordWidth (2 ^ window)) (spec : ModulusSpec wordWidth)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true}
    {Outcome : Type} [Fintype Outcome] (actual : Instrument body Outcome environment)
    (before : Store ctx × services.HiddenState) (outcome : Outcome) :
    (tablePrefixInstrument table spec environment actual).operator before outcome =
      actual.operator (table.circuitRecord
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        spec environment before).1.1 outcome := rfl

end

end Window.Driver

namespace Chain.Program.Parameters

noncomputable section

open Execution Window.Sampling
open QuantumAlg.Execution.Instrument
open ClassicalRoutines.EllipticCurve.WindowTables
open QuantumAlg.ClassicalRoutines.Modular.NativePower

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Residue.input Arithmetic.Call.clearedInitial
  Window.sourceBlank PointFieldState.blank PointFieldState.initialized
  pointFieldState_of_affine pointProgramInstrument InstrumentBranchAction
  PointFieldAllResultsAction SelectedAffineExclusions selectedSumTarget
  Window.Tables.selectedRow referenceKet

private def PreparedPointAllResultsAction (inputs : PointFieldTableInputs parameters)
    (before : Store ctx × services.HiddenState) (initial final : PointFieldState)
    (address : Window.Address) {Reference : Register} (reference : Reference.Index) : Prop :=
  ∀ outcome, (referenceLift (Local := ctx.register) Reference
      ((Window.Driver.tablePrefixInstrument inputs.frame inputs.curve.field environment
        (parameters.pointProgramInstrument environment).embedIdentity).operator before outcome)
      ).applyVec (parameters.referenceKet (initial.blank address) reference) =
    (NormalizedVector.invSqrt2 ^ 2048) •
      parameters.referenceKet (final.blank address) reference

attribute [local irreducible] PreparedPointAllResultsAction Window.Driver.tableInputValues

/-- The same point action passes through its actual paid classical prefix. -/
private lemma preparedPointAllResultsAction_of_point (inputs : PointFieldTableInputs parameters)
    (before : Store ctx × services.HiddenState) (initial final : PointFieldState)
    (address : Window.Address) {Reference : Register} (reference : Reference.Index)
    (action : parameters.PointFieldAllResultsAction (Reference := Reference) environment
      (inputs.frame.circuitRecord
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        inputs.curve.field environment before).1.1 initial final address reference) :
    parameters.PreparedPointAllResultsAction (Reference := Reference) environment inputs before
      initial final address reference := by
  unfold PointFieldAllResultsAction InstrumentBranchAction at action
  unfold PreparedPointAllResultsAction
  intro outcome
  rw [Window.Driver.tablePrefixInstrument_operator]
  exact action outcome

/-- The same returned table supplies the specified point action. -/
private lemma preparedPointInstrument_affine_action_of_table
    (inputs : PointFieldTableInputs parameters)
    (before : Store ctx × services.HiddenState)
    (first result : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)
    (order : Nat)
    (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point
      (inputs.frame.circuitRecord
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        inputs.curve.field environment before).1.1)
    (allowed : parameters.SelectedAffineExclusions inputs
      (parameters.pointFieldState_of_affine inputs first flags) first address)
    (target : result.toMathlib = selectedSumTarget inputs.curve first inputs.point
      (Window.Tables.selectedRow parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        ((parameters.pointFieldState_of_affine inputs first flags).initialized address)).val)
    {Reference : Register} (reference : Reference.Index) :
    parameters.PreparedPointAllResultsAction (Reference := Reference) environment inputs before
      (parameters.pointFieldState_of_affine inputs first flags)
      (parameters.pointFieldState_of_affine inputs result flags) address reference := by
  have action := parameters.pointProgramInstrument_table_affine_action_specified
    (ctx := ctx) (services := services) (Reference := Reference)
    environment inputs _ values first flags address normalZero
    order original tableFits allowed result target reference
  have retained := parameters.preparedPointAllResultsAction_of_point
    (ctx := ctx) (services := services) (Reference := Reference) environment inputs before
    (parameters.pointFieldState_of_affine inputs first flags)
    (parameters.pointFieldState_of_affine inputs result flags) address reference action
  exact retained

/-- Paid original table construction supplies all values used by every actual point outcome. -/
lemma preparedPointInstrument_affine_action (inputs : PointFieldTableInputs parameters)
    (before : Store ctx × services.HiddenState)
    (first result : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (values : Window.Driver.tableInputValues inputs.frame inputs.curve inputs.point before.1)
    (allowed : parameters.SelectedAffineExclusions inputs
      (parameters.pointFieldState_of_affine inputs first flags) first address)
    (target : result.toMathlib = selectedSumTarget inputs.curve first inputs.point
      (Window.Tables.selectedRow parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        ((parameters.pointFieldState_of_affine inputs first flags).initialized address)).val)
    {Reference : Register} (reference : Reference.Index) :
    parameters.PreparedPointAllResultsAction (Reference := Reference) environment inputs before
      (parameters.pointFieldState_of_affine inputs first flags)
      (parameters.pointFieldState_of_affine inputs result flags) address reference := by
  unfold Window.Driver.tableInputValues at values
  obtain ⟨loaded, zero, one, curveValue, baseValue⟩ := values
  have built := inputs.frame.circuitRecord_tableValue inputs.curve environment before
    inputs.point order prime large original tableFits loaded zero one curveValue baseValue
  exact parameters.preparedPointInstrument_affine_action_of_table
    (ctx := ctx) (services := services) (Reference := Reference)
    environment inputs before first result flags address normalZero order original tableFits
    built.2 allowed target reference

end

end Chain.Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point
