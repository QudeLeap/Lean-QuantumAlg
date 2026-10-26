/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Instrument
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Comparison
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Store

/-!
# Original protected caller data through all real unlookup records

Both actual high traversals write only their supplied parity and temporary
cells. Together with the actual measurement and paid mask packing, they
preserve every separate original structural read on every outcome path.
The proof uses symbolic traversals, never an expanded address tree.
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
  (output : Fin resultWidth → CWriteRef ctx (.finite 2))
  (mask : CWriteRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

/-- Both real paid high-address traversals retain every separate original structural input. -/
lemma phaseRecord_read_input (measured : CInputRef ctx (.bits resultWidth))
    {shape : CShape} (observed : CInputRef ctx shape)
    (parityFree : ∀ index, (parity index).key ∉ observed.storageKeys)
    (temporaryFree : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (phaseRecord frame (services := services) physical sameWires measured parity temporary
      table store).1.read observed = store.read observed := by
  unfold phaseRecord
  exact (halfRecord_read_other frame physical sameWires measured parity temporary (table true)
    observed parityFree temporaryFree _).trans
      (halfRecord_read_other frame physical sameWires measured parity temporary (table false)
        observed parityFree temporaryFree store)

/-- The actual preparation and its inverse have no additional classical write destination. -/
lemma restorationRecord_read_input (measured : CInputRef ctx (.bits resultWidth))
    {shape : CShape} (observed : CInputRef ctx shape)
    (parityFree : ∀ index, (parity index).key ∉ observed.storageKeys)
    (temporaryFree : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (restorationRecord frame (services := services) physical sameWires measured parity temporary
      table store).1.read observed = store.read observed :=
  phaseRecord_read_input frame physical sameWires parity temporary table measured observed
    parityFree temporaryFree store

/-- The real reset record preserves a separate original structural read at every outcome. -/
lemma resetRecord_read_input {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (output index).key ∉ observed.storageKeys)
    (maskFree : mask.key ∉ observed.storageKeys) (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path) :
    (resetRecord frame (services := services) physical sameWires output mask store path).1.read
        observed = store.read observed :=
  measuredWordFinalStore_read_other physical sameWires frame.result output mask observed
    outputFree maskFree store path

/-- Complete original table reads survive every real measured unlookup and paid feedback. -/
lemma record_read_input {shape : CShape} (observed : CInputRef ctx shape)
    (outputFree : ∀ index, (output index).key ∉ observed.storageKeys)
    (maskFree : mask.key ∉ observed.storageKeys)
    (parityFree : ∀ index, (parity index).key ∉ observed.storageKeys)
    (temporaryFree : temporary.key ∉ observed.storageKeys) (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path) :
    (record frame (services := services) physical sameWires output mask parity temporary table
      store path).1.read observed = store.read observed := by
  unfold record
  exact (restorationRecord_read_input frame physical sameWires parity temporary table
    (.storage mask.toCStorageRef) observed parityFree temporaryFree _).trans
      (resetRecord_read_input frame physical sameWires output mask observed outputFree maskFree
        store path)

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
