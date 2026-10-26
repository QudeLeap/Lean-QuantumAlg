/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Query
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Call

/-!
# Named instruments of the original point-program fragments

Each value retains the same actual native, query or measured arithmetic
code. Equality transport changes only the presentation of the original
query syntax; its operator and all actual records are retained. These
values support chronological composition at each literal returned Store.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution
open EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def instrumentAlong {Outcome : Type} [Fintype Outcome]
    {first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment}
    (same : first = second)
    (actual : Execution.Instrument first Outcome environment) :
    Execution.Instrument second Outcome environment where
  record store outcome :=
    let original := actual.record store outcome
    (original.1, same ▸ original.2)
  operator := actual.operator
  blocks := by
    cases same
    exact actual.blocks

private lemma instrumentAlong_operator {Outcome : Type} [Fintype Outcome]
    {first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment}
    (same : first = second)
    (actual : Execution.Instrument first Outcome environment)
    (store : Store ctx) (outcome : Outcome) :
    (instrumentAlong same actual).operator store outcome = actual.operator store outcome := by
  cases same
  rfl

variable (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local irreducible] Circuit.measurementSequence resultReadouts


private lemma queryInstrument_reference_operator {lowWidth highRemaining : Nat}
    (q : RuntimeTable.CycleParameters Window.encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts q.physical q.sameWires q.frame.result q.output)).Path)
    (Reference : Register) :
    Execution.Instrument.referenceLift
        (Local := ctx.register) Reference
        ((Window.Sampling.Locality.queryInstrument (services := services)
          q body environment).operator store path) =
      q.insertedBranchOperator (services := services) body store path
        environment.quantum Reference := by
  change Execution.Instrument.referenceLift
    (Local := ctx.register) Reference
    (Window.Sampling.Locality.queryLocalOperator q body store path environment.quantum) = _
  exact ((Window.Sampling.Locality.query_branch_tensor_reference
    q body store path environment.quantum Reference).trans
      (Window.Sampling.Locality.kronecker_referenceLift
        (Local := ctx.register) (Reference := Reference) _)).symm

private lemma queryInstrumentAlong_reference_operator {lowWidth highRemaining : Nat}
    (q : RuntimeTable.CycleParameters Window.encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    {target : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false}
    (same : Window.QueryInsertion.circuit (services := services) q body = target)
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts q.physical q.sameWires q.frame.result q.output)).Path)
    (Reference : Register) :
    Execution.Instrument.referenceLift
      (Local := ctx.register) Reference
      ((instrumentAlong same (Window.Sampling.Locality.queryInstrument (services := services)
        q body environment)).operator store path) =
      q.insertedBranchOperator (services := services) body store path
        environment.quantum Reference := by
  exact (congrArg (fun operator : HilbertOperator ctx.register =>
    Execution.Instrument.referenceLift
      (Local := ctx.register) Reference operator)
    (instrumentAlong_operator same
      (Window.Sampling.Locality.queryInstrument (services := services) q body environment)
      store path)).trans
    (queryInstrument_reference_operator (services := services) (environment := environment)
      q body store path Reference)

/-- This carrier uses the finite paths of the same literal measurement sequence. -/
instance queryOutcomeFintype (occurrence : Fin 6) :
    Fintype (parameters.QueryOutcome (services := services) occurrence) :=
  Circuit.pathFintype
    (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts (parameters.queryParameters occurrence).physical
        (parameters.queryParameters occurrence).sameWires
        (parameters.queryParameters occurrence).frame.result
        (parameters.queryParameters occurrence).output))

/-- The original native fragment, including its actual unique path and unchanged Store. -/
def nativeFragmentInstrument
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum) :
    Execution.Instrument (parameters.native (services := services) body)
      Unit environment :=
  Window.Sampling.Locality.nativeInstrument
    (unitaryOfEqualWires _ _ parameters.sameWires body) environment

/-- The original query's full retained path, on the same allocated source and native body. -/
def queryFragmentInstrument (occurrence : Fin 6) :
    Execution.Instrument (parameters.query (services := services) occurrence)
      (parameters.QueryOutcome (services := services) occurrence) environment :=
  instrumentAlong (parameters.query_eq_inserted (services := services) occurrence).symm
    (Window.Sampling.Locality.queryInstrument (services := services)
      (parameters.queryParameters occurrence)
      (unitaryOfEqualWires _ _ parameters.sameWires
        (Window.QueryColumns.body parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound occurrence))
      environment)

/-- Both original arithmetic calls retain their same actual reset and paid feedback record. -/
def arithmeticFragmentInstrument (kind : Arithmetic.Call.Kind) :
    Execution.Instrument (parameters.arithmetic (services := services) kind)
      (Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
        parameters.output) environment :=
  Window.Sampling.Locality.callInstrument parameters.sameWires parameters.output parameters.mask
    kind parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound environment

/-- The named native instrument has exactly the original full-reference native matrix. -/
lemma nativeFragmentInstrument_operator
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (store : Store ctx) (Reference : Register) :
    Execution.Instrument.referenceLift
      (Local := ctx.register) Reference
        ((parameters.nativeFragmentInstrument environment body).operator store ()) =
      parameters.nativeOperator body environment.quantum Reference :=
  (Window.Sampling.Locality.unitary_referenceLift _).symm

attribute [local irreducible] queryBranchOperator
  instrumentAlong Window.Sampling.Locality.queryInstrument
  Window.QueryColumns.body unitaryOfEqualWires

/-- Equality transport leaves the actual query's original full-reference matrix unchanged. -/
lemma queryFragmentInstrument_operator (occurrence : Fin 6) (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) occurrence) (Reference : Register) :
    Execution.Instrument.referenceLift
      (Local := ctx.register) Reference
        ((parameters.queryFragmentInstrument environment occurrence).operator store path) =
      parameters.queryBranchOperator (services := services)
        occurrence store path environment.quantum Reference := by
  unfold queryFragmentInstrument queryBranchOperator
  exact queryInstrumentAlong_reference_operator (services := services)
    (environment := environment) (q := parameters.queryParameters occurrence)
    (body := unitaryOfEqualWires _ _ parameters.sameWires
      (Window.QueryColumns.body parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound occurrence))
    (same := (parameters.query_eq_inserted (services := services) occurrence).symm)
    (store := store) (path := path) (Reference := Reference)

/-- The named arithmetic instrument has the same actual measured full-reference branch matrix. -/
lemma arithmeticFragmentInstrument_operator (kind : Arithmetic.Call.Kind) (store : Store ctx)
    (path : Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
      parameters.output) (Reference : Register) :
    Execution.Instrument.referenceLift
      (Local := ctx.register) Reference
        ((parameters.arithmeticFragmentInstrument environment kind).operator store path) =
      Arithmetic.Call.branchOperator (services := services) parameters.sameWires parameters.output
        parameters.mask kind parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        store path environment.quantum Reference :=
  ((Window.Sampling.Locality.call_branch_tensor_reference parameters.sameWires parameters.output
    parameters.mask kind parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound store path environment.quantum Reference).trans
      (Window.Sampling.Locality.kronecker_referenceLift _)).symm

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
