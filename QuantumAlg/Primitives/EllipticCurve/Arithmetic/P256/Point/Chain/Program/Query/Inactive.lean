/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Inactive

/-!
# Actual query records preserve every disabled original binary label

Every real retained outcome has the same coefficient as the active
query. The original target may be any binary word, including words
outside the field's canonical range. Its complete source, workspace,
controls, address and arbitrary original reference are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup Window Window.QueryInsertion

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx) (occurrence : Fin 6) (store : Store ctx)
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

include distinct protection outputFree maskFree

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus referenceKet queryBranchOperator QueryBranchAction
  Circuit.measurementSequence resultReadouts

/-- The actually disabled sector is the exact original label beside its unchanged reference. -/
lemma queryBranchOperator_disabled (environment : OracleModel.empty.Interpretation)
    (seed initial : Window.Raw)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (clean : Frame.CleanPool initial.1)
    (zero : ∀ bit,
      ((resultWord (QueryColumns.assignment occurrence).source).bit bit).get initial = false)
    (disabled : querySelected parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound (decide (occurrence.val = 3)) initial = false)
    {Reference : Register} (reference : Reference.Index) :
    parameters.QueryBranchAction (services := services)
      occurrence store path environment initial initial reference := by
  have actual := parameters.queryBranchOperator_original (ctx := ctx) (services := services)
    (Reference := Reference) occurrence store distinct protection outputFree maskFree
    environment seed initial path clean zero (by
      intro selected
      exact False.elim (Bool.false_ne_true (disabled.symm.trans selected))) reference
  have unchanged := queryValue_disabled_label parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (QueryColumns.assignment occurrence) (decide (occurrence.val = 3))
    (RuntimeTable.tableValue (store.read (.storage (parameters.querySource occurrence))))
    initial disabled
  unfold QueryBranchAction at actual ⊢
  exact actual.trans (congrArg (fun state : Window.Raw =>
    NormalizedVector.invSqrt2 ^ 256 • parameters.referenceKet state reference) unchanged)

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
