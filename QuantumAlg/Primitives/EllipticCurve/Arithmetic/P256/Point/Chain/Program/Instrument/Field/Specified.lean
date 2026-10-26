/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.AffineAction
import all QuantumAlg.Util.EllipticCurve.Order

/-!
# Every actual point outcome has the same specified affine group target

The target point is determined by its original group value, independently
of the measured path, through injectivity of its affine embedding. Structural
outcome coverage retains every actual reset and query outcome.
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
  pointFieldState_of_affine InstrumentBranchAction PointFieldResultAction
  SelectedAffineExclusions selectedSumTarget PointFieldPaths.complete pointProgramInstrument
  Window.Tables.selectedRow

private def PointFieldAllResultsAction
    (store : Store ctx) (initial final : PointFieldState) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  ∀ outcome, parameters.InstrumentBranchAction (Reference := Reference) environment
    (parameters.pointProgramInstrument environment) store outcome
    (NormalizedVector.invSqrt2 ^ 2048) (initial.blank address) (final.blank address) reference

attribute [local irreducible] PointFieldAllResultsAction

private lemma pointFieldAllResultsAction_of_paths
    (store : Store ctx) (initial final : PointFieldState) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index)
    (action : ∀ paths, parameters.PointFieldResultAction (Reference := Reference) environment
      store paths initial final address reference) :
    parameters.PointFieldAllResultsAction (Reference := Reference) environment
      store initial final address reference := by
  unfold PointFieldAllResultsAction
  intro outcome
  obtain ⟨paths, rfl⟩ := parameters.pointFieldPaths_complete_surjective
    (services := services) outcome
  have actual := action paths
  unfold PointFieldResultAction at actual
  exact actual

/-- Every actual outcome reaches the same specified affine representative of the original sum. -/
lemma pointProgramInstrument_table_affine_action_specified
    (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : ClassicalRoutines.EllipticCurve.WindowTables.TableFrame.TableValue
      inputs.curve inputs.frame inputs.point store)
    (first : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)
    (order : Nat) (original : addOrderOf inputs.point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
    (allowed : parameters.SelectedAffineExclusions inputs
      (parameters.pointFieldState_of_affine inputs first flags) first address)
    (result : AffinePoint inputs.curve.curve)
    (target : result.toMathlib = selectedSumTarget inputs.curve first inputs.point
      (Window.Tables.selectedRow parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        ((parameters.pointFieldState_of_affine inputs first flags).initialized address)).val)
    {Reference : Register} (reference : Reference.Index) :
    parameters.PointFieldAllResultsAction (Reference := Reference) environment
      store (parameters.pointFieldState_of_affine inputs first flags)
      (parameters.pointFieldState_of_affine inputs result flags) address reference := by
  apply parameters.pointFieldAllResultsAction_of_paths environment store
    (parameters.pointFieldState_of_affine inputs first flags)
    (parameters.pointFieldState_of_affine inputs result flags) address reference
  intro paths
  obtain ⟨actual, sameGroup, action⟩ :=
    parameters.pointProgramInstrument_table_affine_action (Reference := Reference)
      environment inputs store values paths first flags address normalZero order original
      tableFits allowed reference
  have samePoint : actual = result :=
    AffinePoint.toMathlib_injective inputs.curve.curve (sameGroup.trans target.symm)
  subst actual
  exact action

end
end Program.Parameters
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
