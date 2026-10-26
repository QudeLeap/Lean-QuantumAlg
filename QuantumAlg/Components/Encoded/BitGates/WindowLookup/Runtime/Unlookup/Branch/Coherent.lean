/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Branch.Comparison
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Coherent

/-!
# Common actual runtime-unlookup coefficient with arbitrary coherent reference

The lookup graph is the value of the actual supplied table reads in the
original Store. The complete real reset and paid runtime feedback branch
has the exact observed-table matrix, hence the same positive coefficient
on every coherent family member and every external reference label.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution NormalizedVector
open scoped BigOperators

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}

/-- A real runtime outcome has a common positive coefficient on its actual original table graph. -/
lemma branchOperator_graph_coherent
    (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (protection : RuntimeRow.Protection (.storage mask.toCStorageRef) parity temporary
      (fun row : Bool × Fin (2 ^ highRemaining) => table row.1 row.2))
    (outputFree : ∀ index top row column,
      (output index).key ∉ (table top row column).storageKeys)
    (maskFree : ∀ top row column, mask.key ∉ (table top row column).storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx)
    (seed : Data) (outcome : Fin (2 ^ resultWidth))
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (graph : ∀ index, frame.Graph
      (fun top row => RuntimeRow.readTable (table top row) store) (state index))
    (clean : ∀ index, frame.high.CleanFrom 0 (state index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (branchOperator frame (services := services) physical sameWires output mask parity temporary
      table store (namedResultPath (oracles := .empty) (services := services)
        physical sameWires frame.result output seed outcome) environment Reference).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod ctx.register Reference)
              (measuredEncodedBasis physical sameWires (state index), reference index)).vec) =
      invSqrt2 ^ resultWidth •
        ∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires
              (resultSetConstant frame.result 0 (state index)), reference index)).vec := by
  have actual := branchOperator_eq_observed (services := services)
    frame physical sameWires output mask parity temporary
    table protection outputFree maskFree store
    (namedResultPath (oracles := .empty) (services := services)
      physical sameWires frame.result output seed outcome) environment Reference
  have observed := frame.branchOperator_graph_coherent (services := services)
    physical sameWires output outputDistinct
    mask parity (fun top row => RuntimeRow.readTable (table top row) store) protection.maskFree
    environment store seed outcome state graph clean reference amplitude
  exact (congrArg (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
    matrix.applyVec (∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis physical sameWires (state index), reference index)).vec))
    actual).trans observed

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
