/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Operator
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Columns.Coherent.Single
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Field

/-!
# Original complete-label action of every actual point-program query

The operator reads the actual allocated column and retains its actual
measurement path. Its source and native body are the same ones in the
real point circuit. The single-label law is a specialization of the
already coherent law, with the original arbitrary reference and the
common coefficient. Active canonicality remains conditional.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup Window Window.QueryInsertion

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

/-- The original caller-selected table column, including its complete physical row width. -/
def querySource (occurrence : Fin 6) :=
  (parameters.arrays.column (QueryColumns.column occurrence)).toCStorageRef

/-- The original load/body/unlookup parameters on the same existing bank. -/
def queryParameters (occurrence : Fin 6) :=
  let placement := queryPlacement parameters.stream (QueryColumns.assignment occurrence).source
    parameters.highRemaining parameters.lowWidth parameters.addressBound parameters.lowBound
    parameters.sameWires parameters.output parameters.mask parameters.parity parameters.temporary
  placement.parameters (.storage (parameters.querySource occurrence))

/-- The literal unlookup measurement sequence retains every original outcome. -/
def QueryOutcome (occurrence : Fin 6) : Type :=
  (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts (QubitLayout.canonical Window.encoding.width) parameters.sameWires
      (resultWord (QueryColumns.assignment occurrence).source) parameters.output)).Path

/-- The exact real source, selected native body and paid feedback operator. -/
def queryBranchOperator (occurrence : Fin 6) (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (ctx.register.prod Reference) :=
  (parameters.queryParameters occurrence).insertedBranchOperator (services := services)
    (unitaryOfEqualWires _ _ parameters.sameWires
      (QueryColumns.body parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound occurrence))
    store path environment Reference

/-- These same parameters and body are the literal query in the actual point program. -/
lemma query_eq_inserted (occurrence : Fin 6) :
    parameters.query (services := services) occurrence =
      QueryInsertion.circuit (services := services) (parameters.queryParameters occurrence)
        (unitaryOfEqualWires _ _ parameters.sameWires
          (QueryColumns.body parameters.stream
            (parameters.highRemaining + parameters.lowWidth)
            parameters.addressBound occurrence)) := by
  unfold query queryParameters querySource
  rw [QueryColumns.assignment_source]
  rfl

/-- The exact original retained branch maps two complete labels beside the same reference. -/
def QueryBranchAction (occurrence : Fin 6) (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (environment : OracleModel.empty.Interpretation) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  (parameters.queryBranchOperator (services := services)
    occurrence store path environment Reference).applyVec
      (parameters.referenceKet initial reference) =
    NormalizedVector.invSqrt2 ^ 256 • parameters.referenceKet final reference

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus referenceKet queryBranchOperator
  Circuit.measurementSequence resultReadouts

/-- One actual retained record has the same coefficient and the exact original target setter. -/
lemma queryBranchOperator_original
    (occurrence : Fin 6) (store : Store ctx)
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (protection : RuntimeRow.Protection (.storage parameters.mask.toCStorageRef)
      parameters.parity parameters.temporary
      (fun topHigh : Bool × Fin (2 ^ parameters.highRemaining) =>
        RuntimeTable.splitInputs (.storage (parameters.querySource occurrence))
          topHigh.1 topHigh.2))
    (outputFree : ∀ index top high low,
      (parameters.output index).key ∉
        (RuntimeTable.splitInputs (.storage (parameters.querySource occurrence))
          top high low).storageKeys)
    (maskFree : ∀ top high low, parameters.mask.key ∉
      (RuntimeTable.splitInputs (.storage (parameters.querySource occurrence))
        top high low).storageKeys)
    (environment : OracleModel.empty.Interpretation) (seed initial : Window.Raw)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (clean : Frame.CleanPool initial.1)
    (zero : ∀ bit,
      ((resultWord (QueryColumns.assignment occurrence).source).bit bit).get initial = false)
    (admitted : querySelected parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (decide (occurrence.val = 3)) initial = true →
        Canonical (selectedWord parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          (RuntimeTable.tableValue (store.read (.storage (parameters.querySource occurrence))))
          initial) ∧ Canonical ((QueryColumns.assignment occurrence).target.value initial.1))
    {Reference : Register} (reference : Reference.Index) :
    parameters.QueryBranchAction (services := services)
      occurrence store path environment initial
      (resultSetConstant (resultWord (QueryColumns.assignment occurrence).target)
        (queryValue parameters.stream (parameters.highRemaining + parameters.lowWidth)
          parameters.addressBound (QueryColumns.assignment occurrence)
          (decide (occurrence.val = 3))
          (RuntimeTable.tableValue (store.read (.storage (parameters.querySource occurrence))))
          initial) initial) reference := by
  have actual := QueryColumns.columnBranchOperator_value_single_path
    (ctx := ctx) (services := services) (Reference := Reference) parameters.stream
    parameters.highRemaining parameters.lowWidth parameters.addressBound parameters.lowBound
    occurrence parameters.sameWires (parameters.querySource occurrence) parameters.output
    parameters.mask parameters.parity parameters.temporary store distinct protection outputFree
    maskFree environment seed initial path clean zero admitted reference
  simpa only [QueryBranchAction, queryBranchOperator, queryParameters, referenceKet] using actual

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
