/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Branch.Coherent
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Mass

/-!
# Normalized masses of the actual runtime unlookup branches

The exact matrix bridge retains the same physical outcome and original
runtime-table graph. Its injective graph clearing preserves every coherent
reference norm. Thus each actual named outcome has the full-width uniform
mass, and the already established complete outcome sum is one.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution NormalizedVector
open scoped BigOperators

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}

/-- Every actual runtime branch has its exact normalized full-result-width probability. -/
lemma branchOperator_graph_mass
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
    (reference : Index → Reference.Index)
    (injective : Function.Injective fun index =>
      (measuredEncodedBasis physical sameWires (state index), reference index))
    (amplitude : Index → ℂ)
    (normalized : ‖∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis physical sameWires (state index), reference index)).vec‖ = 1) :
    ‖(branchOperator frame (services := services) physical sameWires output mask parity temporary
      table store (namedResultPath (oracles := .empty) (services := services)
        physical sameWires frame.result output seed outcome) environment Reference).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod ctx.register Reference)
              (measuredEncodedBasis physical sameWires (state index), reference index)).vec)‖ ^ 2 =
      ((2 : ℝ)⁻¹) ^ resultWidth := by
  have actual := branchOperator_eq_observed (services := services)
    frame physical sameWires output mask parity temporary
    table protection outputFree maskFree store
    (namedResultPath (oracles := .empty) (services := services)
      physical sameWires frame.result output seed outcome) environment Reference
  have observed := frame.branchOperator_graph_mass (services := services)
    physical sameWires output outputDistinct
    mask parity (fun top row => RuntimeRow.readTable (table top row) store) protection.maskFree
    environment store seed outcome state graph clean reference injective amplitude normalized
  exact (congrArg (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
    ‖matrix.applyVec (∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis physical sameWires (state index), reference index)).vec)‖ ^ 2)
    actual).trans observed

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
