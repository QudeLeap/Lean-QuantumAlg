/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Arithmetic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Initialized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Inactive

/-!
# Complete-label actions of the same actual query instruments

The instrument matrix is exactly the already proved query branch matrix.
The field specialization returns the complete next initializer. The
separate disabled law accepts arbitrary original binary numerical words,
with no replacement by their field residues or added canonicality.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup Window Window.QueryInsertion
open Arithmetic.Call Arithmetic.Call.Endpoint

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus referenceKet queryBranchOperator QueryBranchAction
  InstrumentBranchAction clearedInitial Residue.input Residue.word queryFieldNext
  Circuit.measurementSequence resultReadouts

/-- The actual instrument and original branch assertion are the very same vector equation. -/
lemma queryInstrument_branchAction_iff (occurrence : Fin 6) (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (initial final : Window.Raw) {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment
        (parameters.queryFragmentInstrument environment occurrence) store path
        (NormalizedVector.invSqrt2 ^ 256) initial final reference ↔
      parameters.QueryBranchAction (services := services) (Reference := Reference)
        occurrence store path environment.quantum initial final reference := by
  unfold InstrumentBranchAction QueryBranchAction
  rw [queryFragmentInstrument_operator]

/-- The actual stored column gives the whole next initializer on every retained query path. -/
lemma queryInstrument_initialized_residue (occurrence : Fin 6) (store : Store ctx)
    (separation : parameters.QueryFieldSeparation occurrence) (seed : Window.Raw)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (x y column : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (values : parameters.QueryInitializedSource occurrence store x y column flags address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment
      (parameters.queryFragmentInstrument environment occurrence) store path
      (NormalizedVector.invSqrt2 ^ 256)
      (clearedInitial (Residue.input x) (Residue.input y) flags address)
      (clearedInitial
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).1)
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).2)
        flags address) reference := by
  apply (parameters.queryInstrument_branchAction_iff environment occurrence store path _ _
    (Reference := Reference) reference).mpr
  exact parameters.queryBranchOperator_initialized_residue (services := services)
    (Reference := Reference) occurrence store separation environment.quantum seed path
    x y column flags address values reference

/-- Disabled actual query records retain the original binary label without a field promise. -/
lemma queryInstrument_disabled (occurrence : Fin 6) (store : Store ctx)
    (separation : parameters.QueryFieldSeparation occurrence) (seed initial : Window.Raw)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (clean : Frame.CleanPool initial.1)
    (zero : ∀ bit,
      ((resultWord (QueryColumns.assignment occurrence).source).bit bit).get initial = false)
    (disabled : querySelected parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound (decide (occurrence.val = 3)) initial = false)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment
      (parameters.queryFragmentInstrument environment occurrence) store path
      (NormalizedVector.invSqrt2 ^ 256) initial initial reference := by
  apply (parameters.queryInstrument_branchAction_iff environment occurrence store path _ _
    (Reference := Reference) reference).mpr
  exact parameters.queryBranchOperator_disabled (services := services) (Reference := Reference)
    occurrence store separation.distinct separation.protection separation.outputFree
    separation.maskFree environment.quantum seed initial path clean zero disabled reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
