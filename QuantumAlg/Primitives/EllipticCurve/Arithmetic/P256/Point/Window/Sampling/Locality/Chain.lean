/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Core.Execution.Instrument.Exists
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Query
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Call
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program

/-!
# Full-record locality of the literal six-query, two-call point body

Only the outer sequential syntax is composed. Native word loops and table
sizes stay symbolic inside their proved factors. This is the same actual
program on all input labels, including exceptional and unclean labels;
arithmetic correctness is not a premise of reference locality.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  (parameters : Chain.Program.Parameters ctx)
  (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
    services).Environment)

private lemma chain_native_instrument
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum) :
    Execution.HasInstrument (parameters.native (services := services) body) environment :=
  (nativeInstrument (unitaryOfEqualWires _ _ parameters.sameWires body) environment).to_exists

private lemma chain_query_instrument (occurrence : Fin 6) :
    Execution.HasInstrument (parameters.query (services := services) occurrence) environment :=
  (queryInstrument
    (QueryDirect.parameters parameters.stream parameters.highRemaining parameters.lowWidth
      parameters.addressBound parameters.lowBound parameters.sameWires
      (parameters.arrays.column (QueryColumns.column occurrence)).toCStorageRef parameters.output
      parameters.mask parameters.parity parameters.temporary)
    (unitaryOfEqualWires _ _ parameters.sameWires
      (QueryColumns.body parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound occurrence)) environment).to_exists

private lemma chain_call_instrument (kind : Chain.Arithmetic.Call.Kind) :
    Execution.HasInstrument (parameters.arithmetic (services := services) kind) environment :=
  (callInstrument parameters.sameWires parameters.output parameters.mask kind parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment).to_exists

/-- Every block of the actual complete point body has a finite reference-local Kraus expansion. -/
lemma chain_hasInstrument :
    Execution.HasInstrument (parameters.circuit (services := services)) environment := by
  have native := chain_native_instrument parameters environment
  have query := chain_query_instrument parameters environment
  have arithmetic := chain_call_instrument parameters environment
  have enabled : Execution.HasInstrument (parameters.enable (services := services)) environment :=
    native _
  have cleared : Execution.HasInstrument (parameters.clearEnable (services := services))
    environment :=
    native _
  have differences : Execution.HasInstrument (parameters.differences (services := services))
    environment :=
    (native _).seq ((query 0).seq (query 1))
  have division : Execution.HasInstrument (parameters.division (services := services)) environment
    :=
    enabled.seq ((arithmetic .division).seq cleared)
  have multiplication :
      Execution.HasInstrument (parameters.multiplication (services := services)) environment :=
    (query 2).seq (enabled.seq ((native _).seq
      ((native _).seq ((arithmetic .multiplication).seq cleared))))
  have reflection : Execution.HasInstrument (parameters.reflection (services := services))
    environment :=
    (query 3).seq (enabled.seq ((native _).seq ((native _).seq cleared)))
  have finish : Execution.HasInstrument (parameters.finish (services := services)) environment :=
    (query 4).seq ((query 5).seq (native _))
  exact differences.seq (division.seq (multiplication.seq (reflection.seq finish)))

/-- The literal complete point body commutes with every unitary on the arbitrary reference. -/
lemma chain_reference_unitary (Reference : Register) (operator : UnitaryOperator Reference)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (parameters.circuit (services := services)).execute environment Reference
        (state.applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)) =
      ((parameters.circuit (services := services)).execute environment Reference state).applyUnitary
        (fun _ => UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator) :=
  (chain_hasInstrument parameters environment).reference_unitary Reference operator state

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
