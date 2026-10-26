/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Phase
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Observation

/-!
# Protected scalar values during the actual two-child phase traversal

The actual zero-child preparation and child switch flip only the same
supplied current prefix. Protected payload phases and original addresses
therefore retain their scalar value throughout both native child traversals.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- An actual controlled prefix flip preserves the selected original payload scalar. -/
lemma selectedPhaseAt_conditionalFlip (frame : SelectorFrame encoding width)
    (phase : Fin (2 ^ width) → Data → ℂ)
    (independent : ∀ label index state,
      phase label ((frame.stack index).flip state) = phase label state)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (index : Fin (width + 1)) (enabled : Bool) (state : Data) :
    frame.selectedPhaseAt phase tree depth fits offset bounded
      (if enabled then (frame.stack index).flip state else state) =
      frame.selectedPhaseAt phase tree depth fits offset bounded state := by
  cases enabled with
  | false => rfl
  | true =>
      exact frame.selectedPhaseAt_flip_stack phase independent tree depth fits
        offset bounded index state

/-- The zero-child's real native preparation preserves the original selected payload scalar. -/
lemma selectedPhaseAt_zeroChild (frame : SelectorFrame encoding width)
    (phase : Fin (2 ^ width) → Data → ℂ)
    (independent : ∀ label index state,
      phase label ((frame.stack index).flip state) = phase label state)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (parent : Nat) (present : parent < width) (state : Data) :
    frame.selectedPhaseAt phase tree depth fits offset bounded
      (zeroChildStep (frame.enableAt parent present) (frame.addressAt parent present)
        (frame.prefixAt parent present) state) =
      frame.selectedPhaseAt phase tree depth fits offset bounded state :=
  frame.selectedPhaseAt_conditionalFlip phase independent tree depth fits offset bounded
    ⟨parent + 1, by omega⟩ _ state

/-- The actual CNOT switching the child preserves the original selected payload scalar. -/
lemma selectedPhaseAt_nextChild (frame : SelectorFrame encoding width)
    (phase : Fin (2 ^ width) → Data → ℂ)
    (independent : ∀ label index state,
      phase label ((frame.stack index).flip state) = phase label state)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (parent : Nat) (present : parent < width) (state : Data) :
    frame.selectedPhaseAt phase tree depth fits offset bounded
      ((frame.nextGate parent present).step state) =
      frame.selectedPhaseAt phase tree depth fits offset bounded state :=
  frame.selectedPhaseAt_conditionalFlip phase independent tree depth fits offset bounded
    ⟨parent + 1, by omega⟩ _ state

/-- The real computed and switched prefixes are the two original enabled address indicators. -/
lemma nativeFork_prefix_values (frame : SelectorFrame encoding width)
    (depth : Nat) (present : depth < width) (state : Data)
    (clean : (frame.prefixAt depth present).get state = false) :
    (frame.prefixAt depth present).get
        (zeroChildStep (frame.enableAt depth present) (frame.addressAt depth present)
          (frame.prefixAt depth present) state) =
      ((frame.enableAt depth present).get state && !(frame.addressAt depth present).get state) ∧
    (frame.prefixAt depth present).get
        ((frame.nextGate depth present).step
          (zeroChildStep (frame.enableAt depth present) (frame.addressAt depth present)
            (frame.prefixAt depth present) state)) =
      ((frame.enableAt depth present).get state && (frame.addressAt depth present).get state) := by
  have flipEnable : ∀ value, (frame.enableAt depth present).get
      ((frame.prefixAt depth present).flip value) = (frame.enableAt depth present).get value :=
    EncodedBit.get_flip_of_wire_ne _ _ (Ne.symm (frame.enable_prefix depth present))
  cases enabled : (frame.enableAt depth present).get state <;>
    cases selected : (frame.addressAt depth present).get state <;>
      simp_all [zeroChildStep, nextGate, GateSpec.step, cnotStep, EncodedBit.get_flip_self,
        EncodedBit.flip_flip]

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
