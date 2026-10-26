/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Branch
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Store
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Restoration.Comparison
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Branch

/-!
# Exact runtime branch matrix at the original actual table snapshot

Physical reset writes cannot change the supplied protected table reads.
The complete actual paid restoration therefore has the proved static matrix
for that same original Store, on every state and every external reference.
The mathematical snapshot never supplies constructors to the runtime code.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}

/-- Every actual physical measurement path has the exact original observed-table branch matrix. -/
lemma branchOperator_eq_observed
    (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (protection : RuntimeRow.Protection (.storage mask.toCStorageRef) parity temporary
      (fun row : Bool × Fin (2 ^ highRemaining) => table row.1 row.2))
    (outputFree : ∀ index top row column,
      (output index).key ∉ (table top row column).storageKeys)
    (maskFree : ∀ top row column, mask.key ∉ (table top row column).storageKeys)
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path)
    (environment : OracleModel.Interpretation .empty) (Reference : Register) :
    branchOperator frame (services := services) physical sameWires output mask parity temporary
      table store path environment Reference =
      frame.branchOperator (services := services) physical sameWires output mask parity
        (fun top row => RuntimeRow.readTable (table top row) store) store path
        environment Reference := by
  let next := measuredWordFinalStore (oracles := .empty) (services := services)
    physical sameWires frame.result output mask store path
  have preserved : ∀ top row,
      RuntimeRow.readTable (table top row) next =
        RuntimeRow.readTable (table top row) store := by
    intro top row
    funext column
    exact congrArg (fun value =>
      (⟨value.toNat, value.toNat_lt⟩ : Fin (2 ^ resultWidth)))
      (measuredWordFinalStore_read_other (oracles := .empty) (services := services)
        physical sameWires frame.result output mask
        (table top row column) (fun index => outputFree index top row column)
        (maskFree top row column) store path)
  have restored := restorationOperator_eq_observed (services := services) frame physical sameWires
    (.storage mask.toCStorageRef) parity temporary table protection
    (fun top row => RuntimeRow.readTable (table top row) store) environment next next preserved rfl
  exact congrArg (fun restored : UnitaryOperator ctx.register =>
    (UnitaryOperator.prodTensor restored (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod ctx.register Reference)) *
    measuredWordKraus physical sameWires frame.result frame.resultDistinct output mask store
      path environment Reference) restored

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
