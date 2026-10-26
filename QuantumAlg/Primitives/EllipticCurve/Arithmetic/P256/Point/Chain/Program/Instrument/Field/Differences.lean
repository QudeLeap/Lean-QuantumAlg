/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Seed
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Queries.Tables
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store.Tables

/-!
# The actual first-difference phase at both literal query records

The original source seed is followed by the actual first two queries.
Their source columns come from the same retained paid table, including
its complete original row. Each second fragment receives the first
fragment's actual Store, and both measured paths remain explicit.
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
  InstrumentBranchAction queryFieldNext referenceKet Window.sourceBlank
  Circuit.measurementSequence EncodedBit.WindowLookup.resultReadouts
  differencesInstrument differences

private lemma queryInstrument_table_anchor
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (occurrence : Fin 6) (separation : parameters.QueryFieldSeparation occurrence)
    (seed : Window.Raw) (path : parameters.QueryOutcome (services := services) occurrence)
    (x y anchorX anchorY : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    let column := Window.Tables.selectedFieldColumn curve point parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Arithmetic.Call.clearedInitial (Residue.input anchorX) (Residue.input anchorY) flags address)
      (Window.QueryColumns.column occurrence)
    parameters.InstrumentBranchAction environment
      (parameters.queryFragmentInstrument environment occurrence) store path
      (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (Arithmetic.Call.clearedInitial
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).1)
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).2)
        flags address) reference := by
  dsimp only
  have source := parameters.queryInitializedSource_of_tableValue curve frame point
    sameModulus arrays store values occurrence x y flags address
  rw [Window.Tables.selectedFieldColumn_clearedInitial_values
    _ _ _ _ _ (Residue.input x) (Residue.input y)
    (Residue.input anchorX) (Residue.input anchorY)] at source
  exact parameters.queryInstrument_initialized_residue (Reference := Reference)
    environment occurrence store
    separation seed path x y _ flags address source reference

private def differencesFirstCoordinates
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    ZMod modulus × ZMod modulus :=
  let initial := Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address
  let column0 := Window.Tables.selectedFieldColumn curve point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound initial
    (Window.QueryColumns.column 0)
  parameters.queryFieldNext 0 x y column0 flags address

private def differencesFieldMiddle
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let first := parameters.differencesFirstCoordinates curve point x y flags address
  Arithmetic.Call.clearedInitial (Residue.input first.1) (Residue.input first.2) flags address

private def differencesFieldFinal
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let initial := Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address
  let column1 := Window.Tables.selectedFieldColumn curve point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound initial
    (Window.QueryColumns.column 1)
  let first := parameters.differencesFirstCoordinates curve point x y flags address
  let final := parameters.queryFieldNext 1 first.1 first.2 column1 flags address
  Arithmetic.Call.clearedInitial (Residue.input final.1) (Residue.input final.2) flags address

attribute [local irreducible] differencesFirstCoordinates differencesFieldMiddle
  differencesFieldFinal

private lemma twoFactors_power {R : Register}
    (first second : HilbertOperator R)
    (initial middle final : HilbertVector R) (firstPower secondPower : Nat)
    (firstAction : first.applyVec initial =
      NormalizedVector.invSqrt2 ^ firstPower • middle)
    (secondAction : second.applyVec middle =
      NormalizedVector.invSqrt2 ^ secondPower • final) :
    HilbertOperator.applyVec (second * first) initial =
      NormalizedVector.invSqrt2 ^ (firstPower + secondPower) • final := by
  rw [HilbertOperator.mul_applyVec, firstAction,
    HilbertOperator.applyVec_smul, secondAction, smul_smul, ← pow_add]

private lemma firstQueries_operator (store : Store ctx)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      (((parameters.queryFragmentInstrument environment 0).seq
        (parameters.queryFragmentInstrument environment 1)).operator store (path0, path1)) =
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.queryFragmentInstrument environment 1).operator
          ((parameters.queryFragmentInstrument environment 0).record store path0).1 path1) *
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.queryFragmentInstrument environment 0).operator store path0) :=
  seq_reference_operator (parameters.queryFragmentInstrument environment 0)
    (parameters.queryFragmentInstrument environment 1) store path0 path1 Reference

private lemma seedThenQueries_operator (store : Store ctx)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      ((parameters.differencesInstrument environment).operator store ((), (path0, path1))) =
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        (((parameters.queryFragmentInstrument environment 0).seq
          (parameters.queryFragmentInstrument environment 1)).operator store (path0, path1)) *
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.nativeFragmentInstrument environment
          (Window.suffixProgram Inversion.Seed.program)).operator store ()) := by
  unfold differencesInstrument
  rw [seq_reference_operator, nativeFragmentInstrument_store]

private lemma firstQueries_branchAction
    (store : Store ctx)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (initial middle final : Window.Raw) {Reference : Register} (reference : Reference.Index)
    (firstAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 0) store path0
      (NormalizedVector.invSqrt2 ^ 256) initial middle reference)
    (secondAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 1)
      ((parameters.queryFragmentInstrument environment 0).record store path0).1 path1
      (NormalizedVector.invSqrt2 ^ 256) middle final reference) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      ((parameters.queryFragmentInstrument environment 0).seq
        (parameters.queryFragmentInstrument environment 1))
      store (path0, path1) (NormalizedVector.invSqrt2 ^ 512) initial final reference := by
  unfold InstrumentBranchAction at firstAction secondAction ⊢
  rw [parameters.firstQueries_operator environment store path0 path1 Reference]
  exact twoFactors_power _ _
    (parameters.referenceKet initial reference)
    (parameters.referenceKet middle reference)
    (parameters.referenceKet final reference)
    256 256 firstAction secondAction

private lemma seedThenQueries_branchAction
    (store : Store ctx)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (initial middle final : Window.Raw) {Reference : Register} (reference : Reference.Index)
    (seedAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.nativeFragmentInstrument environment
        (Window.suffixProgram Inversion.Seed.program)) store () 1 initial middle reference)
    (queryAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      ((parameters.queryFragmentInstrument environment 0).seq
        (parameters.queryFragmentInstrument environment 1))
      store (path0, path1) (NormalizedVector.invSqrt2 ^ 512) middle final reference) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.differencesInstrument environment)
      store ((), (path0, path1)) (NormalizedVector.invSqrt2 ^ 512) initial final reference := by
  unfold InstrumentBranchAction at seedAction queryAction ⊢
  rw [parameters.seedThenQueries_operator environment store path0 path1 Reference,
    HilbertOperator.mul_applyVec, seedAction, one_smul]
  exact queryAction

private lemma firstDifference_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation : parameters.QueryFieldSeparation 0)
    (path : parameters.QueryOutcome (services := services) 0)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 0) store path
      (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.differencesFieldMiddle curve point x y flags address) reference := by
  unfold differencesFieldMiddle differencesFirstCoordinates
  exact parameters.queryInstrument_table_anchor (Reference := Reference)
    environment curve frame point sameModulus arrays store values 0 separation
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address) path
    x y x y flags address reference

private lemma secondDifference_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation : parameters.QueryFieldSeparation 1)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 1)
      ((parameters.queryFragmentInstrument environment 0).record store path0).1 path1
      (NormalizedVector.invSqrt2 ^ 256)
      (parameters.differencesFieldMiddle curve point x y flags address)
      (parameters.differencesFieldFinal curve point x y flags address) reference := by
  have nextValues := parameters.queryFragmentInstrument_tableValue environment 0
    curve frame point store values outputFree maskFree parityFree temporaryFree path0
  unfold differencesFieldMiddle differencesFieldFinal
  exact parameters.queryInstrument_table_anchor (Reference := Reference)
    environment curve frame point sameModulus arrays _ nextValues 1 separation
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address) path1
    (parameters.differencesFirstCoordinates curve point x y flags address).1
    (parameters.differencesFirstCoordinates curve point x y flags address).2
    x y flags address reference

private lemma differencesQueries_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation0 : parameters.QueryFieldSeparation 0)
    (separation1 : parameters.QueryFieldSeparation 1)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      ((parameters.queryFragmentInstrument environment 0).seq
        (parameters.queryFragmentInstrument environment 1))
      store (path0, path1) (NormalizedVector.invSqrt2 ^ 512)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.differencesFieldFinal curve point x y flags address) reference := by
  have firstAction := parameters.firstDifference_table_residue (Reference := Reference)
    environment curve frame point sameModulus arrays store values separation0 path0
    x y flags address reference
  have secondAction := parameters.secondDifference_table_residue (Reference := Reference)
    environment curve frame point sameModulus arrays store values separation1
    outputFree maskFree parityFree temporaryFree path0 path1 x y flags address reference
  exact parameters.firstQueries_branchAction (Reference := Reference)
    environment store path0 path1 _ _ _ reference firstAction secondAction

private def sourceFieldBlank (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  Window.sourceBlank (Residue.input x) (Residue.input y) flags address

attribute [local irreducible] sourceFieldBlank

private lemma differencesSeed_field (store : Store ctx)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.nativeFragmentInstrument environment
        (Window.suffixProgram Inversion.Seed.program)) store () 1
      (sourceFieldBlank x y flags address)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      reference := by
  unfold sourceFieldBlank
  exact parameters.sourceSeedInstrument_blank (Reference := Reference)
    environment store (Residue.input x) (Residue.input y) flags address reference

/-- The same literal first-phase proposition, with its actual typed instrument named once. -/
private def DifferencesFieldAction
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (store : Store ctx)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  parameters.InstrumentBranchAction (Reference := Reference) environment
    (parameters.differencesInstrument environment)
    store ((), (path0, path1)) (NormalizedVector.invSqrt2 ^ 512)
    (sourceFieldBlank x y flags address)
    (parameters.differencesFieldFinal curve point x y flags address) reference

attribute [local irreducible] DifferencesFieldAction

/-- The original seed and two real query paths give the whole next initializer with common mass. -/
lemma differencesInstrument_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation0 : parameters.QueryFieldSeparation 0)
    (separation1 : parameters.QueryFieldSeparation 1)
    (outputFree : ∀ index column, (parameters.output index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (maskFree : ∀ column, parameters.mask.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (parityFree : ∀ index column, (parameters.parity index).key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (temporaryFree : ∀ column, parameters.temporary.key ∉
      (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys)
    (path0 : parameters.QueryOutcome (services := services) 0)
    (path1 : parameters.QueryOutcome (services := services) 1)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.DifferencesFieldAction (Reference := Reference) environment
      curve point store path0 path1 x y flags address reference := by
  unfold DifferencesFieldAction
  refine parameters.seedThenQueries_branchAction (Reference := Reference)
    environment store path0 path1 (sourceFieldBlank x y flags address)
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    (parameters.differencesFieldFinal curve point x y flags address)
    reference ?_ ?_
  · exact parameters.differencesSeed_field (Reference := Reference)
      environment store x y flags address reference
  · exact parameters.differencesQueries_table_residue (Reference := Reference)
      environment curve frame point sameModulus arrays store values separation0 separation1
      outputFree maskFree parityFree temporaryFree path0 path1 x y flags address reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
