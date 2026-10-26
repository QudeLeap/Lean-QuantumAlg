/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Differences

/-!
# The actual final two queries and the original quantum-seed adjoint

Both real query outcomes and their literal intermediate Store are retained.
The same paid table supplies both columns. The last native operation clears
its complete initializer at the updated coordinates, including the original
pool, controls and address, with the arbitrary reference unchanged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Arithmetic.Call.clearedInitial Residue.input
  InstrumentBranchAction queryFieldNext referenceKet Window.sourceBlank nativeOperator
  Circuit.measurementSequence EncodedBit.WindowLookup.resultReadouts finishInstrument finish

private def finishFirstCoordinates
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    ZMod modulus × ZMod modulus :=
  let initial := Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address
  let column := Window.Tables.selectedFieldColumn curve point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound initial
    (Window.QueryColumns.column 4)
  parameters.queryFieldNext 4 x y column flags address

private def finishFieldMiddle
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let first := parameters.finishFirstCoordinates curve point x y flags address
  Arithmetic.Call.clearedInitial (Residue.input first.1) (Residue.input first.2) flags address

private def finishLastCoordinates
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    ZMod modulus × ZMod modulus :=
  let initial := Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address
  let column := Window.Tables.selectedFieldColumn curve point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound initial
    (Window.QueryColumns.column 5)
  let first := parameters.finishFirstCoordinates curve point x y flags address
  parameters.queryFieldNext 5 first.1 first.2 column flags address

private def finishFieldInitialized
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let final := parameters.finishLastCoordinates curve point x y flags address
  Arithmetic.Call.clearedInitial (Residue.input final.1) (Residue.input final.2) flags address

private def finishFieldBlank
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let final := parameters.finishLastCoordinates curve point x y flags address
  Window.sourceBlank (Residue.input final.1) (Residue.input final.2) flags address

attribute [local irreducible] finishFirstCoordinates finishFieldMiddle finishLastCoordinates
  finishFieldInitialized finishFieldBlank

private lemma finishQueries_operator (store : Store ctx)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5) (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      (((parameters.queryFragmentInstrument environment 4).seq
        (parameters.queryFragmentInstrument environment 5)).operator store (path4, path5)) =
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.queryFragmentInstrument environment 5).operator
          ((parameters.queryFragmentInstrument environment 4).record store path4).1 path5) *
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.queryFragmentInstrument environment 4).operator store path4) :=
  seq_reference_operator (parameters.queryFragmentInstrument environment 4)
    (parameters.queryFragmentInstrument environment 5) store path4 path5 Reference

private lemma finishInstrument_operator (store : Store ctx)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5) (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      ((parameters.finishInstrument environment).operator store (path4, (path5, ()))) =
      parameters.nativeOperator
        (Window.suffixProgram
          (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))
        environment.quantum Reference *
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        (((parameters.queryFragmentInstrument environment 4).seq
          (parameters.queryFragmentInstrument environment 5)).operator store (path4, path5)) := by
  unfold finishInstrument
  rw [seq_reference_operator, seq_reference_operator, nativeFragmentInstrument_operator,
    Matrix.mul_assoc, ← parameters.finishQueries_operator environment store path4 path5 Reference]

private lemma finishQueries_branchAction
    (store : Store ctx)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5)
    (initial middle final : Window.Raw) {Reference : Register} (reference : Reference.Index)
    (firstAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 4) store path4
      (NormalizedVector.invSqrt2 ^ 256) initial middle reference)
    (secondAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 5)
      ((parameters.queryFragmentInstrument environment 4).record store path4).1 path5
      (NormalizedVector.invSqrt2 ^ 256) middle final reference) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      ((parameters.queryFragmentInstrument environment 4).seq
        (parameters.queryFragmentInstrument environment 5))
      store (path4, path5) (NormalizedVector.invSqrt2 ^ 512) initial final reference := by
  unfold InstrumentBranchAction at firstAction secondAction ⊢
  rw [parameters.finishQueries_operator environment store path4 path5 Reference]
  exact twoFactors_power (R := ctx.register.prod Reference) _ _
    (parameters.referenceKet initial reference) (parameters.referenceKet middle reference)
    (parameters.referenceKet final reference) 256 256 firstAction secondAction

private lemma finishQueriesThenSeed_branchAction
    (store : Store ctx)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5)
    (initial middle final : Window.Raw) {Reference : Register} (reference : Reference.Index)
    (headAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      ((parameters.queryFragmentInstrument environment 4).seq
        (parameters.queryFragmentInstrument environment 5))
      store (path4, path5) (NormalizedVector.invSqrt2 ^ 512) initial middle reference)
    (tailAction : (parameters.nativeOperator
      (Window.suffixProgram
        (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))
      environment.quantum Reference).applyVec (parameters.referenceKet middle reference) =
        parameters.referenceKet final reference) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.finishInstrument environment) store (path4, (path5, ()))
      (NormalizedVector.invSqrt2 ^ 512) initial final reference := by
  unfold InstrumentBranchAction at headAction ⊢
  rw [parameters.finishInstrument_operator environment store path4 path5 Reference,
    HilbertOperator.mul_applyVec, headAction, HilbertOperator.applyVec_smul, tailAction]

private lemma finishDagger_field (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator
      (Window.suffixProgram
        (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))
      environment.quantum Reference).applyVec
        (parameters.referenceKet (Arithmetic.Call.clearedInitial input numerator flags address)
          reference) =
      parameters.referenceKet (Window.sourceBlank input numerator flags address) reference :=
  parameters.nativeOperator_original _ environment.quantum _ _
    (Window.sourceSeedProgram_dagger environment.quantum input numerator flags address) reference

private lemma finishFirstQuery_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation : parameters.QueryFieldSeparation 4)
    (path : parameters.QueryOutcome (services := services) 4)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 4) store path
      (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.finishFieldMiddle curve point x y flags address) reference := by
  unfold finishFieldMiddle finishFirstCoordinates
  exact parameters.queryInstrument_table_anchor (Reference := Reference)
    environment curve frame point sameModulus arrays store values 4 separation
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address) path
    x y x y flags address reference

private lemma finishSecondQuery_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation : parameters.QueryFieldSeparation 5)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 5)
      ((parameters.queryFragmentInstrument environment 4).record store path4).1 path5
      (NormalizedVector.invSqrt2 ^ 256)
      (parameters.finishFieldMiddle curve point x y flags address)
      (parameters.finishFieldInitialized curve point x y flags address) reference := by
  have nextValues := parameters.queryFragmentInstrument_tableValue environment 4
    curve frame point store values outputFree maskFree parityFree temporaryFree path4
  unfold finishFieldMiddle finishFieldInitialized finishLastCoordinates
  exact parameters.queryInstrument_table_anchor (Reference := Reference)
    environment curve frame point sameModulus arrays _ nextValues 5 separation
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address) path5
    (parameters.finishFirstCoordinates curve point x y flags address).1
    (parameters.finishFirstCoordinates curve point x y flags address).2
    x y flags address reference

private lemma finishQueries_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation4 : parameters.QueryFieldSeparation 4)
    (separation5 : parameters.QueryFieldSeparation 5)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      ((parameters.queryFragmentInstrument environment 4).seq
        (parameters.queryFragmentInstrument environment 5))
      store (path4, path5) (NormalizedVector.invSqrt2 ^ 512)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.finishFieldInitialized curve point x y flags address) reference := by
  have firstAction := parameters.finishFirstQuery_table_residue (Reference := Reference)
    environment curve frame point sameModulus arrays store values separation4 path4
    x y flags address reference
  have secondAction := parameters.finishSecondQuery_table_residue (Reference := Reference)
    environment curve frame point sameModulus arrays store values separation5
    outputFree maskFree parityFree temporaryFree path4 path5 x y flags address reference
  exact parameters.finishQueries_branchAction (Reference := Reference)
    environment store path4 path5 _ _ _ reference firstAction secondAction

private def FinishFieldAction
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (store : Store ctx)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  parameters.InstrumentBranchAction (Reference := Reference) environment
    (parameters.finishInstrument environment) store (path4, (path5, ()))
    (NormalizedVector.invSqrt2 ^ 512)
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    (parameters.finishFieldBlank curve point x y flags address) reference

attribute [local irreducible] FinishFieldAction

/-- Both actual queries and the original adjoint restore the entire updated source blank. -/
lemma finishInstrument_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation4 : parameters.QueryFieldSeparation 4)
    (separation5 : parameters.QueryFieldSeparation 5)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path4 : parameters.QueryOutcome (services := services) 4)
    (path5 : parameters.QueryOutcome (services := services) 5)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.FinishFieldAction (Reference := Reference) environment
      curve point store path4 path5 x y flags address reference := by
  unfold FinishFieldAction
  refine parameters.finishQueriesThenSeed_branchAction (Reference := Reference)
    environment store path4 path5
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    (parameters.finishFieldInitialized curve point x y flags address)
    (parameters.finishFieldBlank curve point x y flags address) reference ?_ ?_
  · exact parameters.finishQueries_table_residue (Reference := Reference)
      environment curve frame point sameModulus arrays store values separation4 separation5
      outputFree maskFree parityFree temporaryFree path4 path5 x y flags address reference
  · unfold finishFieldInitialized finishFieldBlank
    exact parameters.finishDagger_field (Reference := Reference) environment
      (Residue.input (parameters.finishLastCoordinates curve point x y flags address).1)
      (Residue.input (parameters.finishLastCoordinates curve point x y flags address).2)
      flags address reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
