/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Coherent
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Effect

/-!
# Concrete per-record query output in the complete original label

Every actual loader/body/paid-unlookup record has the same coefficient.
Only the original numerical target changes to the independently specified
selected table addition. The original source, padding, complete pool,
controls, address and arbitrary external Reference retain their values.
Canonicality is required only on the actual original active sectors.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open Execution NormalizedVector EncodedBit.WindowLookup
open scoped BigOperators

attribute [local implicit_reducible] capacity width

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

/-- Actual query records change exactly the selected target in the original complete label. -/
lemma nativeBranchOperator_value_all_paths
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
      querySelected stream (highRemaining + lowWidth) bounded exceptional (initial index) = true →
        Canonical (selectedWord stream (highRemaining + lowWidth) bounded
          (RuntimeTable.tableValue (store.read (.storage source))) (initial index)) ∧
        Canonical (ports.target.value (initial index).1))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    let parameters :=
      (queryPlacement stream ports.source highRemaining lowWidth bounded lowBound same
        output mask parity temporary).parameters (.storage source)
    let body : Body :=
      if exceptional then selectedBody stream (highRemaining + lowWidth) bounded
          (Chain.Offset.Exceptional.Placed.program ports)
        else ordinaryBody stream (highRemaining + lowWidth) bounded ports
    (parameters.insertedBranchOperator
      (unitaryOfEqualWires _ _ same body) store path environment Reference).applyVec
      (∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical encoding.width) same (initial index),
            reference index)).vec) =
      invSqrt2 ^ 256 • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical encoding.width) same
            (resultSetConstant (resultWord ports.target)
              (queryValue stream (highRemaining + lowWidth) bounded ports exceptional
                (RuntimeTable.tableValue (store.read (.storage source))) (initial index))
              (initial index)), reference index)).vec := by
  let table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256) :=
    RuntimeTable.tableValue (store.read (.storage source))
  let loaded := loadedState stream ports.source highRemaining lowWidth bounded lowBound table
  have physicalCanonical (index : Index) :
      let prepared := arithmeticSource stream (highRemaining + lowWidth) bounded
        (loaded (initial index))
      let retained := ((Placement.layout ports).grouping prepared).2.2
      (if exceptional then (Native.BorrowedControl.controlBit ports).get retained &&
          Bool.not ((Native.controlBit ports .normal).get retained)
        else (Native.BorrowedControl.controlBit ports).get retained) = true →
        Canonical (ports.source.value prepared) ∧ Canonical (ports.target.value prepared) := by
    dsimp only
    intro active
    have selected := loaded_arithmeticSource_selected stream highRemaining lowWidth bounded
      lowBound ports table (initial index) (clean index)
    have normal := (arithmeticSource_normal stream (highRemaining + lowWidth) bounded ports
      (loaded (initial index))).trans
      (loadedState_normal stream ports.source highRemaining lowWidth bounded lowBound table
        (initial index))
    have enabled : querySelected stream (highRemaining + lowWidth) bounded exceptional
        (initial index) = true := by
      unfold querySelected
      rw [selected, normal] at active
      exact active
    have known := admitted index enabled
    constructor
    · rw [arithmeticSource_word,
        loadedState_source stream ports.source highRemaining lowWidth bounded lowBound table
          (initial index) (zero index)]
      exact known.1
    · rw [arithmeticSource_word,
        loadedState_word_other stream ports.source ports.target ports.source_target highRemaining
          lowWidth bounded lowBound table (initial index)]
      exact known.2
  have actual := nativeBranchOperator_all_paths (stream := stream)
    (highRemaining := highRemaining) (lowWidth := lowWidth) (bounded := bounded)
    (lowBound := lowBound) (ports := ports) (exceptional := exceptional) (same := same)
    (source := source) (output := output) (mask := mask) (parity := parity)
    (temporary := temporary) (store := store) outputDistinct protection outputFree maskFree
    environment seed path initial clean zero physicalCanonical reference amplitude
  dsimp only at actual ⊢
  refine actual.trans ?_
  apply congrArg (fun vector : HilbertVector (Register.prod ctx.register Reference) =>
    invSqrt2 ^ 256 • vector)
  apply Finset.sum_congr rfl
  intro index _
  rw [query_cleared_eq_target_set stream highRemaining lowWidth bounded lowBound ports exceptional
    table (initial index) (clean index) (zero index)]

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
