/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Correctness
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Half
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Observation.Operator

/-!
# Exact matrix comparison for the actual paid runtime high traversal

The comparison freezes only a mathematical observation of the input Store.
The executed program still reads its real table and pays every AND/XOR.
The equality holds on the entire quantum space, without clean-state promises.
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
  (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

/-- The actual whole high traversal retains every caller read outside its paid work cells. -/
lemma halfRecord_read_other {shape : CShape} (observed : CInputRef ctx shape)
    (freeParity : ∀ index, (parity index).key ∉ observed.storageKeys)
    (freeTemporary : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (halfRecord frame (services := services) physical sameWires measured parity temporary
      table store).1.read observed = store.read observed := by
  exact frame.high.circuitAtRecord_observe physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (halfCallbackRecord frame (services := services)
      physical sameWires measured parity temporary table)
    (fun current => current.read observed)
    (fun label current => RuntimeRow.rowCircuitRecord_read_other physical sameWires measured
      parity temporary (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      observed freeParity freeTemporary current)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store

/-- The real runtime traversal equals the static observed-table matrix on every quantum state. -/
lemma halfOperator_eq_observed
    (protection : RuntimeRow.Protection measured parity temporary table)
    (snapshot : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (environment : OracleModel.Interpretation .empty) (firstStore secondStore : Store ctx)
    (same : halfObservation measured table firstStore = (snapshot, secondStore.read measured)) :
    halfOperator frame (services := services) physical sameWires measured parity temporary table
      environment firstStore =
      frame.halfOperator (services := services) physical sameWires measured parity snapshot
        environment secondStore := by
  have callbacks : ∀ label first second,
      halfObservation measured table first = (snapshot, second.read measured) →
      halfCallbackOperator frame (services := services) physical sameWires measured parity temporary
        table environment label first =
        frame.halfCallbackOperator physical sameWires measured snapshot environment
          label second := by
    intro label first second equal
    have tables := congrArg (fun observation => observation.1 label) equal
    have masks := congrArg Prod.snd equal
    change RuntimeRow.readTable (table label) first = snapshot label at tables
    change first.read measured = second.read measured at masks
    have actual := RuntimeRow.actualOperator_eq_original (services := services)
      physical sameWires measured parity temporary table protection label frame.lowWord
      frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
      (frame.highStack_lowWord _) lowWidth environment first
    apply actual.trans
    change MaskParity.rowOperator physical sameWires measured
      (RuntimeRow.readTable (table label) first) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      environment first = _
    rw [tables]
    unfold UnlookupFrame.halfCallbackOperator MaskParity.rowOperator
    rw [masks]
  exact frame.high.circuitAtOperator_congr_observation physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (frame.halfCallback (services := services) physical sameWires measured parity snapshot)
    (halfCallbackRecord frame (services := services)
      physical sameWires measured parity temporary table)
    (frame.halfCallbackRecord (services := services) physical sameWires measured parity snapshot)
    (halfCallbackOperator frame (services := services)
      physical sameWires measured parity temporary table environment)
    (frame.halfCallbackOperator physical sameWires measured snapshot environment)
    (halfObservation measured table) (fun current => (snapshot, current.read measured))
    (halfCallbackRecord_observation frame physical sameWires measured parity temporary
      table protection)
    (fun label current => congrArg (fun mask => (snapshot, mask))
      (MaskParity.rowCircuitRecord_read_other physical sameWires measured parity
        (snapshot label) frame.lowWord frame.low.targetDistinct
        (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
        measured protection.maskFree current))
    callbacks environment (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega)
    firstStore secondStore same

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
