/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Comparison
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Execution
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Complete

/-!
# Full runtime feedback equals its original observed-table matrix

Both real traversals retain the original table and mask. Their different
paid work-cell records do not change the exact native quantum product.
The two original address flips and every physical wire remain identical.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

/-- The actual paid feedback product equals the original observed-table product on all states. -/
lemma phaseOperator_eq_observed
    (protection : RuntimeRow.Protection measured parity temporary
      (fun row : Bool × Fin (2 ^ highRemaining) => table row.1 row.2))
    (snapshot : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (environment : OracleModel.Interpretation .empty) (firstStore secondStore : Store ctx)
    (sameTable : ∀ top row, RuntimeRow.readTable (table top row) firstStore = snapshot top row)
    (sameMask : firstStore.read measured = secondStore.read measured) :
    phaseOperator frame (services := services) physical sameWires measured parity temporary table
      environment firstStore =
      frame.phaseOperator (services := services) physical sameWires measured parity snapshot
        environment secondStore := by
  let firstLeft := halfRecord frame (services := services) physical sameWires measured parity
    temporary (table false) firstStore
  let secondLeft := frame.halfRecord (services := services) physical sameWires measured parity
    (snapshot false) secondStore
  have firstObservation : halfObservation measured (table false) firstStore =
      (snapshot false, secondStore.read measured) := by
    apply Prod.ext
    · funext row
      exact sameTable false row
    · exact sameMask
  have firstMatrix := halfOperator_eq_observed (services := services)
    frame physical sameWires measured parity temporary
    (table false) (protection.reindex fun row => (false, row)) (snapshot false)
    environment firstStore secondStore firstObservation
  have secondObservation : halfObservation measured (table true) firstLeft.1 =
      (snapshot true, secondLeft.1.read measured) := by
    apply Prod.ext
    · funext row column
      have unchanged := halfRecord_read_other (services := services)
        frame physical sameWires measured parity temporary
        (table false) (table true row column)
        (fun index => protection.tableFree index (true, row) column)
        (protection.temporaryTableFree (true, row) column) firstStore
      have original := congrFun (sameTable true row) column
      exact (congrArg (fun value =>
        (⟨value.toNat, value.toNat_lt⟩ : Fin (2 ^ resultWidth))) unchanged).trans original
    · have actual := halfRecord_read_other (services := services)
        frame physical sameWires measured parity temporary
        (table false) measured protection.maskFree protection.temporaryMaskFree firstStore
      have observed := frame.halfRecord_read_mask (services := services) physical sameWires
        measured parity (snapshot false) protection.maskFree secondStore
      exact actual.trans (sameMask.trans observed.symm)
  have secondMatrix := halfOperator_eq_observed (services := services)
    frame physical sameWires measured parity temporary
    (table true) (protection.reindex fun row => (true, row)) (snapshot true)
    environment firstLeft.1 secondLeft.1 secondObservation
  change halfOperator frame (services := services) physical sameWires measured parity temporary
      (table true) environment firstLeft.1 *
      (topFlipProgram frame physical sameWires).matrix environment *
      halfOperator frame (services := services) physical sameWires measured parity temporary
        (table false) environment firstStore *
      (topFlipProgram frame physical sameWires).matrix environment =
    frame.halfOperator (services := services) physical sameWires measured parity (snapshot true)
        environment secondLeft.1 *
      (frame.topFlipProgram physical sameWires).matrix environment *
      frame.halfOperator (services := services) physical sameWires measured parity (snapshot false)
        environment secondStore *
      (frame.topFlipProgram physical sameWires).matrix environment
  rw [secondMatrix, firstMatrix]
  rfl

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
