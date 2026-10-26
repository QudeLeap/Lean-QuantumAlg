/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Residue

/-!
# Ordinary field action of the actual retained query operator

The actual stored source and original target words determine the field
sum. The only value hypotheses are their mathematical coordinate reads;
no action callback or alternate table is supplied. The original full
label law remains available for arbitrary inactive binary words.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup Window Window.QueryInsertion

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx) (occurrence : Fin 6) (store : Store ctx)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus referenceKet queryBranchOperator QueryBranchAction
  Circuit.measurementSequence resultReadouts

/-- The two original word reads, without an operator-action or arithmetic-domain assertion. -/
structure QueryFieldValues (initial : Window.Raw) (column target : ZMod modulus) : Prop where
  sourceValue : selectedWord parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (RuntimeTable.tableValue (store.read (.storage (parameters.querySource occurrence))))
    initial = Residue.word column
  targetValue : (QueryColumns.assignment occurrence).target.value initial.1 =
    Residue.word target

/-- The original four storage-layout facts, with no quantum input or action premise. -/
structure QueryFieldSeparation : Prop where
  distinct : Function.Injective fun index => (parameters.output index).key
  protection : RuntimeRow.Protection (.storage parameters.mask.toCStorageRef)
    parameters.parity parameters.temporary
    (fun topHigh : Bool × Fin (2 ^ parameters.highRemaining) =>
      RuntimeTable.splitInputs (.storage (parameters.querySource occurrence))
        topHigh.1 topHigh.2)
  outputFree : ∀ index top high low,
    (parameters.output index).key ∉
      (RuntimeTable.splitInputs (.storage (parameters.querySource occurrence))
        top high low).storageKeys
  maskFree : ∀ top high low, parameters.mask.key ∉
    (RuntimeTable.splitInputs (.storage (parameters.querySource occurrence))
      top high low).storageKeys

variable (separation : parameters.QueryFieldSeparation occurrence)

include separation

/-- The same real query record returns its ordinary selected field sum in the original target. -/
lemma queryBranchOperator_residue (environment : OracleModel.empty.Interpretation)
    (seed initial : Window.Raw)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (clean : Frame.CleanPool initial.1)
    (zero : ∀ bit,
      ((resultWord (QueryColumns.assignment occurrence).source).bit bit).get initial = false)
    (column target : ZMod modulus)
    (values : parameters.QueryFieldValues occurrence store initial column target)
    {Reference : Register} (reference : Reference.Index) :
    parameters.QueryBranchAction (services := services)
      occurrence store path environment initial
      (resultSetConstant (resultWord (QueryColumns.assignment occurrence).target)
        (Residue.word (target +
          if querySelected parameters.stream (parameters.highRemaining + parameters.lowWidth)
            parameters.addressBound (decide (occurrence.val = 3)) initial then column else 0))
        initial) reference := by
  have actual := parameters.queryBranchOperator_original (ctx := ctx) (services := services)
    (Reference := Reference) occurrence store separation.distinct separation.protection
    separation.outputFree separation.maskFree environment seed initial path clean zero (by
      intro _
      exact ⟨values.sourceValue.symm ▸ Residue.word_canonical column,
        values.targetValue.symm ▸ Residue.word_canonical target⟩) reference
  have updated := queryValue_word parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (QueryColumns.assignment occurrence) (decide (occurrence.val = 3))
    (RuntimeTable.tableValue (store.read (.storage (parameters.querySource occurrence))))
    initial column target values.sourceValue values.targetValue
  unfold QueryBranchAction at actual ⊢
  exact actual.trans (congrArg (fun value : Word =>
    NormalizedVector.invSqrt2 ^ 256 • parameters.referenceKet
      (resultSetConstant (resultWord (QueryColumns.assignment occurrence).target) value initial)
      reference) updated)

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
