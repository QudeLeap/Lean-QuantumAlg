/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Store
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Store

/-!
# Original protected reads at literal point-instrument records

These laws concern the actual returned Store of each original fragment.
They apply to arbitrary original input reads and every measurement path,
without a quantum promise. Chronological composition retains the same
read at the literal intermediate Store, so the paid builder's columns
can be reused throughout the point operation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup Window.Sampling

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment}

/-- Every actual retained record preserves the same original structural input read. -/
def InstrumentPreservesRead {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false}
    (actual : Execution.Instrument code Outcome environment)
    {shape : CShape} (observed : CInputRef ctx shape) : Prop :=
  ∀ store outcome, (actual.record store outcome).1.read observed = store.read observed

/-- Sequential records pass exactly the first returned Store to the second fragment. -/
lemma instrumentPreservesRead_seq {First Second : Type} [Fintype First] [Fintype Second]
    {first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    (head : Execution.Instrument first First environment)
    (tail : Execution.Instrument second Second environment)
    {shape : CShape} (observed : CInputRef ctx shape)
    (headRead : InstrumentPreservesRead head observed)
    (tailRead : InstrumentPreservesRead tail observed) :
    InstrumentPreservesRead (head.seq tail) observed := by
  intro store outcomes
  change (tail.record (head.record store outcomes.1).1 outcomes.2).1.read observed = _
  exact (tailRead _ _).trans (headRead store outcomes.1)

variable (parameters : Parameters ctx) (environment)

attribute [local irreducible] Circuit.measurementSequence resultReadouts
  instrumentAlong Locality.queryInstrument

/-- Every original native fragment keeps the entire actual classical Store. -/
lemma nativeFragmentInstrument_read
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    {shape : CShape} (observed : CInputRef ctx shape) :
    InstrumentPreservesRead (parameters.nativeFragmentInstrument environment body) observed := by
  intro store outcome
  rfl

private lemma queryFragmentInstrument_store (occurrence : Fin 6) (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) occurrence) :
    ((parameters.queryFragmentInstrument environment occurrence).record store path).1 =
      (RuntimeUnlookup.record (parameters.queryParameters occurrence).frame
        (parameters.queryParameters occurrence).physical parameters.sameWires
        parameters.output parameters.mask parameters.parity parameters.temporary
        (RuntimeTable.splitInputs (parameters.queryParameters occurrence).source)
        store path).1 := by
  unfold queryFragmentInstrument instrumentAlong Locality.queryInstrument
  rfl

/-- The real query writes only its actual four families of feedback destinations. -/
lemma queryFragmentInstrument_read (occurrence : Fin 6)
    {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parameters.parity index).key ∉ observed.storageKeys)
    (temporaryFree : parameters.temporary.key ∉ observed.storageKeys) :
    InstrumentPreservesRead
      (parameters.queryFragmentInstrument environment occurrence) observed := by
  intro store path
  rw [queryFragmentInstrument_store]
  exact RuntimeUnlookup.record_read_input
    (parameters.queryParameters occurrence).frame
    (parameters.queryParameters occurrence).physical parameters.sameWires
    parameters.output parameters.mask parameters.parity parameters.temporary
    (RuntimeTable.splitInputs (parameters.queryParameters occurrence).source)
    observed outputFree maskFree parityFree temporaryFree store path

/-- Both real arithmetic records write only their original measurement outputs and mask. -/
lemma arithmeticFragmentInstrument_read (kind : Arithmetic.Call.Kind)
    {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (parameters.output index).key ∉ observed.storageKeys)
    (maskFree : parameters.mask.key ∉ observed.storageKeys) :
    InstrumentPreservesRead
      (parameters.arithmeticFragmentInstrument environment kind) observed := by
  intro store outcome
  exact Arithmetic.Call.callRecord_read_input (services := services)
    parameters.sameWires parameters.output parameters.mask kind parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    observed outputFree maskFree store outcome

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
