/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Half
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Comparison
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Phase.Address
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Observation

/-!
# Selected original runtime-table character of the actual high traversal

Both the complete real table and measured mask are protected observations
of the actual chronological Store. Each paid callback has the exact native
row phase. Clean existing prefixes therefore select the original complete
high address while the native traversal restores every quantum label.
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

/-- The original complete runtime table and original measured mask observed in the same Store. -/
def halfObservation (store : Store ctx) :
    (Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth)) ×
      CShape.Value (.bits resultWidth) :=
  (fun row => RuntimeRow.readTable (table row) store, store.read measured)

/-- Every actual row preserves the complete real table and measured mask, including other rows. -/
lemma halfCallbackRecord_observation
    (protection : RuntimeRow.Protection measured parity temporary table)
    (label : Fin (2 ^ highRemaining)) (store : Store ctx) :
    halfObservation measured table
      (halfCallbackRecord frame (services := services) physical sameWires measured parity temporary
        table label store).1 = halfObservation measured table store := by
  apply Prod.ext
  · funext row column
    apply Fin.ext
    change ((halfCallbackRecord frame (services := services) physical sameWires measured parity
      temporary table label store).1.read (table row column)).toNat =
        (store.read (table row column)).toNat
    exact congrArg CShape.Value.toNat
      (RuntimeRow.rowCircuitRecord_read_other physical sameWires measured parity temporary
        (table label) frame.lowWord frame.low.targetDistinct
        (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
        (table row column) (fun index => protection.tableFree index row column)
        (protection.temporaryTableFree row column) store)
  · exact RuntimeRow.rowCircuitRecord_read_other physical sameWires measured parity temporary
      (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      measured protection.maskFree protection.temporaryMaskFree store

/-- The selected original row character is evaluated on the original protected table/mask pair. -/
def halfRowPhase (label : Fin (2 ^ highRemaining))
    (observation : (Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth)) ×
      CShape.Value (.bits resultWidth)) (state : Data) : ℂ :=
  if wordMaskParity frame.lowWord
    (MaskParity.rowConstant (observation.1 label) observation.2) state then -1 else 1

/-- Every native high-prefix flip is outside the original low unary word's physical support. -/
lemma halfRowPhase_flip_stack (label : Fin (2 ^ highRemaining))
    (observation : (Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth)) ×
      CShape.Value (.bits resultWidth))
    (index : Fin (highRemaining + 1)) (state : Data) :
    halfRowPhase frame label observation ((frame.high.stack index).flip state) =
      halfRowPhase frame label observation state := by
  apply congrArg (fun bit : Bool => if bit then (-1 : ℂ) else 1)
  apply bitParity_congr
  intro bit member
  obtain ⟨target, _, rfl⟩ := List.mem_map.mp member
  exact EncodedBit.get_flip_of_wire_ne (frame.high.stack index) (frame.lowWord.bit target)
    (frame.highStack_lowWord index target) state

/-- The callback's actual stored-mask matrix has precisely the original runtime row phase. -/
lemma halfCallbackOperator_applyVec
    (protection : RuntimeRow.Protection measured parity temporary table)
    (environment : OracleModel.Interpretation .empty) (label : Fin (2 ^ highRemaining))
    (store : Store ctx) (state : Data) :
    (halfCallbackOperator frame (services := services) physical sameWires measured parity temporary
      table environment label store).applyVec (SelectorFrame.ctxVector physical sameWires state) =
      (if (frame.high.stack ⟨highRemaining, by omega⟩).get state then
        halfRowPhase frame label (halfObservation measured table store) state else 1) •
          SelectorFrame.ctxVector physical sameWires state := by
  have actual := RuntimeRow.actualOperator_eq_original (services := services)
    physical sameWires measured parity temporary table protection label frame.lowWord
    frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
    (frame.highStack_lowWord _) lowWidth environment store
  have original := RuntimeRow.rowOperator_applyVec physical sameWires measured (table label)
    frame.lowWord
    frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
    (frame.highStack_lowWord _) lowWidth (Nat.le_refl _) environment store state
  exact (congrArg (fun operator : UnitaryOperator ctx.register =>
    operator.applyVec (SelectorFrame.ctxVector physical sameWires state)) actual).trans original

/-- The actual paid traversal selects the original full high address and restores all data. -/
lemma halfOperator_applyVec
    (protection : RuntimeRow.Protection measured parity temporary table)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx) (state : Data)
    (clean : frame.high.CleanFrom 0 state) :
    (halfOperator frame (services := services) physical sameWires measured parity temporary table
      environment store).applyVec (SelectorFrame.ctxVector physical sameWires state) =
      (if (frame.high.stack ⟨0, by omega⟩).get state then
        halfRowPhase frame
          (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state)
          (halfObservation measured table store) state else 1) •
          SelectorFrame.ctxVector physical sameWires state := by
  have actual := frame.high.circuitAtOperator_selectedPhase physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (halfCallbackRecord frame (services := services)
      physical sameWires measured parity temporary table)
    (halfCallbackOperator frame (services := services)
      physical sameWires measured parity temporary table environment)
    (halfObservation measured table)
    (halfCallbackRecord_observation frame physical sameWires measured parity temporary table
      protection)
    (halfRowPhase frame) (halfRowPhase_flip_stack frame)
    (fun label store state => halfCallbackOperator_applyVec frame physical sameWires measured
      parity temporary table protection environment label store state)
    environment (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store state clean
  rw [frame.high.selectedPhaseAt_full] at actual
  exact actual

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
