/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Fold
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector

/-!
# Streaming with the same retained physical address

The immutable bits in this mathematical fold are the original reads of
the actual address wires. Preservation of those wires proves the bridge;
it supplies neither an input-dependent circuit nor a classical address.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The mathematical ordered visitor with explicit unchanged address bits. -/
def foldBitsAt (bits : Fin width → Bool)
    (action : Fin (2 ^ width) → Bool → Data → Data) :
    {remaining : Nat} → SelectorTrie remaining → (depth : Nat) →
      depth + remaining = width → (offset : Nat) →
      offset + 2 ^ remaining ≤ 2 ^ width → Bool → Data → Data
  | _, .skip _, _, _, _, _, _, state => state
  | 0, .leaf, _, _, offset, bounded, enabled, state =>
      action ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ enabled state
  | remaining + 1, .fork left right, depth, _, offset, bounded, enabled, state =>
      foldBitsAt bits action right (depth + 1) (by omega) (offset + 2 ^ remaining)
        (SelectorFrame.right_bound bounded) (enabled && bits ⟨depth, by omega⟩)
        (foldBitsAt bits action left (depth + 1) (by omega) offset
          (SelectorFrame.left_bound bounded) (enabled && !bits ⟨depth, by omega⟩) state)

/-- Every address read remains attached to its original physical state throughout the stream. -/
lemma foldAt_eq_bits (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Bool → Data → Data)
    (preserves : ∀ label selected, frame.Preserves (action label selected))
    (bits : Fin width → Bool) {remaining : Nat} (tree : SelectorTrie remaining)
    (depth : Nat) (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (enabled : Bool) (state : Data)
    (reads : ∀ index, (frame.address index).get state = bits index) :
    foldAt frame action tree depth fits offset bounded enabled state =
      foldBitsAt bits action tree depth fits offset bounded enabled state := by
  induction tree generalizing depth offset enabled state with
  | skip remaining => rfl
  | leaf => rfl
  | @fork remaining left right leftIH rightIH =>
      have current : (frame.addressAt depth (by omega)).get state = bits ⟨depth, by omega⟩ :=
        reads _
      have leftSame := leftIH (depth + 1) (by omega) offset
        (SelectorFrame.left_bound bounded) (enabled && !bits ⟨depth, by omega⟩) state reads
      have leftReads : ∀ index, (frame.address index).get
          (foldBitsAt bits action left (depth + 1) (by omega) offset
            (SelectorFrame.left_bound bounded) (enabled && !bits ⟨depth, by omega⟩) state) =
          bits index := by
        intro index
        rw [← leftSame]
        exact ((foldAt_preserves frame action preserves left _ _ _ _ _).1 index state).trans
          (reads index)
      dsimp only [foldAt, foldBitsAt]
      rw [current, leftSame]
      exact rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (SelectorFrame.right_bound bounded) (enabled && bits ⟨depth, by omega⟩) _ leftReads

end

end QuantumAlg.EncodedBit.StreamedSelector
