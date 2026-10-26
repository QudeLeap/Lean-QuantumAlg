/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Address
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Observation

/-!
# Actual lookup establishes the original split-table graph

The selected native program has the previously proved full dirty-target
XOR action. A real zero target therefore becomes the same table graph used
by paid measured unlookup. Literal physical address agreement supplies
the full high/low correspondence; no truncation or new input restriction
is substituted for this correspondence.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
    {resultWidth lowWidth highWidth : Nat}
    (frame : UnlookupFrame encoding resultWidth lowWidth highWidth)

/-- Equal physical graph readouts preserve the exact original selected table word. -/
lemma tableAt_congr
    (table : Bool → Fin (2 ^ highWidth) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (first second : Data)
    (root : (frame.high.stack ⟨0, by omega⟩).get first =
      (frame.high.stack ⟨0, by omega⟩).get second)
    (high : ∀ index, (frame.high.address index).get first =
      (frame.high.address index).get second)
    (low : ∀ index, (frame.low.address index).get first =
      (frame.low.address index).get second) :
    frame.tableAt table first = frame.tableAt table second := by
  unfold tableAt
  rw [root, frame.high.addressLabelAt_congr first second high,
    frame.low.prefixLabel_congr _ _ first second low]

/-- Preserving the result and complete original address preserves its actual table graph. -/
lemma Graph.of_readouts
    (table : Bool → Fin (2 ^ highWidth) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (first second : Data) (graph : frame.Graph table first)
    (result : ∀ index, (frame.result.bit index).get second = (frame.result.bit index).get first)
    (root : (frame.high.stack ⟨0, by omega⟩).get second =
      (frame.high.stack ⟨0, by omega⟩).get first)
    (high : ∀ index, (frame.high.address index).get second =
      (frame.high.address index).get first)
    (low : ∀ index, (frame.low.address index).get second =
      (frame.low.address index).get first) : frame.Graph table second := by
  intro index
  rw [result, graph index, frame.tableAt_congr table second first root high low]

/-- The full native selector and actual split feedback name the identical table value. -/
lemma tableAt_split_eq_lookup (lookup : SelectorFrame encoding (highWidth + lowWidth))
    (split : AddressSplit lookup frame.high frame.low)
    (table : Bool → Fin (2 ^ (highWidth + lowWidth)) → Fin (2 ^ resultWidth)) (state : Data) :
    frame.tableAt (splitTable table) state =
      table ((lookup.stack ⟨0, by omega⟩).get state)
        (lookup.addressLabelAt (highWidth + lowWidth) 0 (by omega) 0 (by omega) state) := by
  unfold tableAt splitTable
  rw [← split.root_get state, ← split.addressLabel state]

/-- Real zero-target XOR loading yields the same original graph on every complete basis label. -/
lemma splitLookupStep_graph (lookup : SelectorFrame encoding (highWidth + lowWidth))
    (outsideAddress : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.address index).wire)
    (outsideStack : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.stack index).wire)
    (split : AddressSplit lookup frame.high frame.low)
    (table : Bool → Fin (2 ^ (highWidth + lowWidth)) → Fin (2 ^ resultWidth))
    (state : Data) (zero : ∀ index, (frame.result.bit index).get state = false) :
    frame.Graph (splitTable table)
      (splitLookupStep lookup (frame.cycleTarget lookup outsideAddress outsideStack)
        table state) := by
  let target := frame.cycleTarget lookup outsideAddress outsideStack
  let constant := table ((lookup.stack ⟨0, by omega⟩).get state)
    (lookup.addressLabelAt (highWidth + lowWidth) 0 (by omega) 0 (by omega) state)
  have preserved := target.xor_preserves constant
  change lookup.Preserves (Word.xorConstantStep frame.result constant) at preserved
  have selected : frame.tableAt (splitTable table)
      (Word.xorConstantStep frame.result constant state) = constant := by
    rw [frame.tableAt_split_eq_lookup lookup split,
      preserved.2 ⟨0, by omega⟩ state,
      lookup.addressLabelAt_congr _ state (fun index => preserved.1 index state)]
  intro index
  change (frame.result.bit index).get (Word.xorConstantStep frame.result constant state) =
    ((frame.tableAt (splitTable table)
      (Word.xorConstantStep frame.result constant state)).val.testBit index.val)
  rw [selected, Word.xorConstantStep_get_target frame.result constant index
    (fun other different same => different (frame.resultDistinct same)) state,
    zero index, Bool.false_xor]

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
