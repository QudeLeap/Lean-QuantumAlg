/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Coherent.Output
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Columns.Action

/-!
# Actual per-record action of each original native query body

The exact original six query bodies consume the same concrete loader,
paid arithmetic and measured unlookup. This specializes the original-label
query law to the actual occurrence and its genuine (decide (occurrence.val = 3)) selection.
Only original active-sector canonicality is required; arbitrary finite
coherent input families and external Reference retain the common coefficient.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryColumns

noncomputable section

open Execution NormalizedVector EncodedBit.WindowLookup QueryInsertion
open scoped BigOperators

attribute [local implicit_reducible] capacity width

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (occurrence : Fin 6)
    (same : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (store : Store ctx)

/-- Actual query records change exactly the selected target in the original complete label. -/
lemma columnBranchOperator_value_all_paths
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
        (resultWord (assignment occurrence).source) output)).Path)
    {Reference : Register} {Index : Type} [Fintype Index] (initial : Index → Raw)
    (clean : ∀ index, Frame.CleanPool (initial index).1)
    (zero : ∀ index bit,
      ((resultWord (assignment occurrence).source).bit bit).get (initial index) = false)
    (admitted : ∀ index,
      querySelected stream (highRemaining + lowWidth) bounded (decide (occurrence.val = 3))
          (initial index) = true →
        Canonical (selectedWord stream (highRemaining + lowWidth) bounded
          (RuntimeTable.tableValue (store.read (.storage source))) (initial index)) ∧
        Canonical ((assignment occurrence).target.value (initial index).1))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    let parameters :=
      (queryPlacement stream (assignment occurrence).source highRemaining lowWidth bounded lowBound
        same output mask parity temporary).parameters (.storage source)
    let nativeBody := body stream (highRemaining + lowWidth) bounded occurrence
    (parameters.insertedBranchOperator
      (unitaryOfEqualWires _ _ same nativeBody) store path environment Reference).applyVec
      (∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical encoding.width) same (initial index),
            reference index)).vec) =
      invSqrt2 ^ 256 • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical encoding.width) same
            (resultSetConstant (resultWord (assignment occurrence).target)
              (queryValue stream (highRemaining + lowWidth) bounded (assignment occurrence)
                (decide (occurrence.val = 3))
                (RuntimeTable.tableValue (store.read (.storage source))) (initial index))
              (initial index)), reference index)).vec := by
  have actual := QueryInsertion.nativeBranchOperator_value_all_paths (stream := stream)
    (highRemaining := highRemaining) (lowWidth := lowWidth) (bounded := bounded)
    (lowBound := lowBound) (ports := assignment occurrence)
    (exceptional := decide (occurrence.val = 3)) (same := same) (source := source)
    (output := output) (mask := mask) (parity := parity) (temporary := temporary) (store := store)
    outputDistinct protection outputFree maskFree environment seed path initial clean zero admitted
    reference amplitude
  simpa only [body_eq_native, decide_eq_true_eq] using actual

end

end QueryColumns

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
