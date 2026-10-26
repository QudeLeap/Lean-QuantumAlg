/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Columns.Coherent

/-!
# Single-label specialization before placing a concrete point-parameter record

The finite-family law is specialized while its physical references and
selector widths remain independent variables. Later chronological callers
can apply the single-label law without re-elaborating its coherent sum at
every concrete parameter projection. The actual body, paths, coefficient,
original input conditions and arbitrary reference are unchanged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryColumns

noncomputable section

open Execution NormalizedVector EncodedBit.WindowLookup QueryInsertion

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Circuit.measurementSequence resultReadouts

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

/-- Every actual retained outcome has the same complete original single-label field action. -/
lemma columnBranchOperator_value_single_path
    (distinct : Function.Injective fun index => (output index).key)
    (protection : RuntimeRow.Protection (.storage mask.toCStorageRef) parity temporary
      (fun topHigh : Bool × Fin (2 ^ highRemaining) =>
        RuntimeTable.splitInputs (.storage source) topHigh.1 topHigh.2))
    (outputFree : ∀ index top high low, (output index).key ∉
      (RuntimeTable.splitInputs (.storage source) top high low).storageKeys)
    (maskFree : ∀ top high low,
      mask.key ∉ (RuntimeTable.splitInputs (.storage source) top high low).storageKeys)
    (environment : OracleModel.empty.Interpretation) (seed initial : Raw)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts (QubitLayout.canonical encoding.width) same
        (resultWord (assignment occurrence).source) output)).Path)
    (clean : Frame.CleanPool initial.1)
    (zero : ∀ bit, ((resultWord (assignment occurrence).source).bit bit).get initial = false)
    (admitted : querySelected stream (highRemaining + lowWidth) bounded
      (decide (occurrence.val = 3)) initial = true →
        Canonical (selectedWord stream (highRemaining + lowWidth) bounded
          (RuntimeTable.tableValue (store.read (.storage source))) initial) ∧
        Canonical ((assignment occurrence).target.value initial.1))
    {Reference : Register} (reference : Reference.Index) :
    let parameters :=
      (queryPlacement stream (assignment occurrence).source highRemaining lowWidth bounded lowBound
        same output mask parity temporary).parameters (.storage source)
    let nativeBody := body stream (highRemaining + lowWidth) bounded occurrence
    (parameters.insertedBranchOperator (services := services)
      (unitaryOfEqualWires _ _ same nativeBody) store path environment Reference).applyVec
      (NormalizedVector.ket (R := ctx.register.prod Reference)
        (measuredEncodedBasis (QubitLayout.canonical encoding.width) same initial,
          reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := ctx.register.prod Reference)
        (measuredEncodedBasis (QubitLayout.canonical encoding.width) same
          (resultSetConstant (resultWord (assignment occurrence).target)
            (queryValue stream (highRemaining + lowWidth) bounded (assignment occurrence)
              (decide (occurrence.val = 3))
              (RuntimeTable.tableValue (store.read (.storage source))) initial) initial),
            reference)).vec := by
  have actual := columnBranchOperator_value_all_paths (ctx := ctx) (services := services)
    stream highRemaining lowWidth bounded lowBound occurrence same source output mask parity
    temporary store distinct protection outputFree maskFree environment seed path
    (Reference := Reference) (Index := Unit) (fun _ => initial) (fun _ => clean)
    (fun _ => zero) (fun _ => admitted) (fun _ => reference) (fun _ => (1 : ℂ))
  simpa only [Fintype.sum_unique, one_smul] using actual

end

end QueryColumns

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
