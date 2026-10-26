/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Loading
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Outcomes
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Table

/-!
# Actual point-query columns on every original measurement record

The original stored array, full physical address and native ordinary or
exceptional addition supply the actual body and graph obligations. The
caller supplies only canonical operands when their actual enable is set,
the initialized original pool and the genuine zero result word, together
with the classical storage separation of the real enclosing allocation.
No body-action or phase-action callback is assumed. Every measurement
record has the same coefficient, including zero-digit and disabled inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open Execution NormalizedVector EncodedBit.WindowLookup
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment) (exceptional : Bool)
    (same : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (store : Store ctx)

/-- The real stored-table query has concrete native columns with one coefficient on every path. -/
lemma nativeBranchOperator_all_paths
    (outputDistinct : Function.Injective fun index => (output index).key)
    (protection : RuntimeRow.Protection (.storage mask.toCStorageRef) parity temporary
      (fun topHigh : Bool × Fin (2 ^ highRemaining) =>
        RuntimeTable.splitInputs (.storage source) topHigh.1 topHigh.2))
    (outputFree : ∀ index top high low,
      (output index).key ∉
        (RuntimeTable.splitInputs (.storage source) top high low).storageKeys)
    (maskFree : ∀ top high low,
      mask.key ∉ (RuntimeTable.splitInputs (.storage source) top high low).storageKeys)
    (environment : OracleModel.empty.Interpretation) (seed : Raw)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts (QubitLayout.canonical encoding.width) same
        (resultWord ports.source) output)).Path)
    {Reference : Register} {Index : Type} [Fintype Index] (initial : Index → Raw)
    (clean : ∀ index, Frame.CleanPool (initial index).1)
    (zero : ∀ index bit, ((resultWord ports.source).bit bit).get (initial index) = false)
    (admitted : ∀ index,
      let table := RuntimeTable.tableValue (store.read (.storage source))
      let prepared := arithmeticSource stream (highRemaining + lowWidth) bounded
        (loadedState stream ports.source highRemaining lowWidth bounded lowBound table
          (initial index))
      let retained := ((Placement.layout ports).grouping prepared).2.2
      (if exceptional then (Native.BorrowedControl.controlBit ports).get retained &&
          Bool.not ((Native.controlBit ports .normal).get retained)
        else (Native.BorrowedControl.controlBit ports).get retained) = true →
        Canonical (ports.source.value prepared) ∧ Canonical (ports.target.value prepared))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    let parameters :=
      (queryPlacement stream ports.source highRemaining lowWidth bounded lowBound same
        output mask parity temporary).parameters (.storage source)
    let table := RuntimeTable.tableValue (store.read (.storage source))
    let loaded := loadedState stream ports.source highRemaining lowWidth bounded lowBound table
    let body : Body :=
      if exceptional then selectedBody stream (highRemaining + lowWidth) bounded
          (Chain.Offset.Exceptional.Placed.program ports)
        else ordinaryBody stream (highRemaining + lowWidth) bounded ports
    let after := fun state : Raw =>
      if exceptional then exceptionalStep stream (highRemaining + lowWidth) bounded ports
          (loaded state)
        else ordinaryStep stream (highRemaining + lowWidth) bounded ports (loaded state)
    (parameters.insertedBranchOperator
      (unitaryOfEqualWires _ _ same body) store path environment Reference).applyVec
      (∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical encoding.width) same (initial index),
            reference index)).vec) =
      invSqrt2 ^ 256 • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical encoding.width) same
            (resultSetConstant (resultWord ports.source) 0 (after (initial index))),
              reference index)).vec := by
  let parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining :=
    (queryPlacement stream ports.source highRemaining lowWidth bounded lowBound same
      output mask parity temporary).parameters (.storage source)
  let table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256) :=
    RuntimeTable.tableValue (store.read (.storage source))
  let loaded := loadedState stream ports.source highRemaining lowWidth bounded lowBound table
  let body : Body :=
    if exceptional then selectedBody stream (highRemaining + lowWidth) bounded
        (Chain.Offset.Exceptional.Placed.program ports)
      else ordinaryBody stream (highRemaining + lowWidth) bounded ports
  let after := fun state : Raw =>
    if exceptional then exceptionalStep stream (highRemaining + lowWidth) bounded ports
        (loaded state)
      else ordinaryStep stream (highRemaining + lowWidth) bounded ports (loaded state)
  have loadedClean (index : Index) : Frame.CleanPool (loaded (initial index)).1 :=
    loadedState_cleanPool stream ports.source highRemaining lowWidth bounded lowBound
      table (initial index) (clean index)
  refine parameters.insertedBranchOperator_all_paths (unitaryOfEqualWires _ _ same body)
    outputDistinct protection
    outputFree maskFree environment store seed path initial (fun index => after (initial index))
    ?_ ?_ ?_ ?_ reference amplitude
  · intro index
    exact selector_cleanFrom_of_cleanPool stream _ bounded (initial index) (clean index)
  · intro index
    apply UnitaryCircuit.equalWires_apply_encoded_ket_of_eq ctx.quantumLayout same
    cases exceptional with
    | false =>
        exact ordinaryBody_apply_of_cleanPool stream _ bounded ports environment
          (loaded (initial index)) (loadedClean index) (admitted index)
    | true =>
        exact exceptionalBody_apply_of_cleanPool stream _ bounded ports environment
          (loaded (initial index)) (loadedClean index) (admitted index)
  · intro index
    change (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph
      (fun top high => RuntimeRow.readTable
        (RuntimeTable.splitInputs (.storage source) top high) store) (after (initial index))
    rw [RuntimeTable.splitInputs_readTable]
    have graph := loadedState_graph stream ports.source highRemaining lowWidth bounded lowBound
      table (initial index) (zero index)
    cases exceptional with
    | false =>
        exact ordinaryStep_graph stream highRemaining lowWidth bounded lowBound ports
          (loaded (initial index)) (loadedClean index) _ graph
    | true =>
        exact exceptionalStep_graph stream highRemaining lowWidth bounded lowBound ports
          (loaded (initial index)) (loadedClean index) _ graph
  · intro index
    apply selector_cleanFrom_of_cleanPool stream highRemaining (by omega)
    cases exceptional with
    | false =>
        exact ordinaryStep_cleanPool stream _ bounded ports
          (loaded (initial index)) (loadedClean index)
    | true =>
        exact exceptionalStep_cleanPool stream _ bounded ports
          (loaded (initial index)) (loadedClean index)

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
