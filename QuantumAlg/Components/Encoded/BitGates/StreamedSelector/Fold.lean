/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Frame
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector

/-!
# Ordered semantic fold for streaming selector callbacks

Every retained leaf is visited in order and receives its own actual
selection bit. Both Boolean actions protect the complete selector frame;
only data outside that frame may evolve during the traversal.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Ordered visits retain nontrivial false actions instead of discarding unselected leaves. -/
def foldAt (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Bool → Data → Data) :
    {remaining : Nat} → SelectorTrie remaining → (depth : Nat) →
      depth + remaining = width → (offset : Nat) →
      offset + 2 ^ remaining ≤ 2 ^ width → Bool → Data → Data
  | _, .skip _, _, _, _, _, _, state => state
  | 0, .leaf, _, _, offset, bounded, enabled, state =>
      action ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ enabled state
  | remaining + 1, .fork left right, depth, _, offset, bounded, enabled, state =>
      let selected := (frame.addressAt depth (by omega)).get state
      foldAt frame action right (depth + 1) (by omega) (offset + 2 ^ remaining)
        (SelectorFrame.right_bound bounded) (enabled && selected)
        (foldAt frame action left (depth + 1) (by omega) offset
          (SelectorFrame.left_bound bounded) (enabled && !selected) state)

/-- Each Boolean leaf action protects every physical address and prefix throughout the fold. -/
lemma foldAt_preserves (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Bool → Data → Data)
    (preserves : ∀ label selected, frame.Preserves (action label selected))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (enabled : Bool) :
    frame.Preserves (foldAt frame action tree depth fits offset bounded enabled) := by
  induction tree generalizing depth offset enabled with
  | skip remaining => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | leaf => exact preserves _ enabled
  | @fork remaining left right leftIH rightIH =>
      constructor
      · intro index state
        dsimp only [foldAt]
        exact ((rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
          (SelectorFrame.right_bound bounded) _).1 index _).trans
          ((leftIH (depth + 1) (by omega) offset
            (SelectorFrame.left_bound bounded) _).1 index state)
      · intro index state
        dsimp only [foldAt]
        exact ((rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
          (SelectorFrame.right_bound bounded) _).2 index _).trans
          ((leftIH (depth + 1) (by omega) offset
            (SelectorFrame.left_bound bounded) _).2 index state)

/-- Explicit Boolean leaf parameters remove any dependency on temporary prefix values. -/
lemma foldAt_independent (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Bool → Data → Data)
    (independent : ∀ label selected, frame.IndependentPrefixes (action label selected))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (enabled : Bool) :
    frame.IndependentPrefixes (foldAt frame action tree depth fits offset bounded enabled) := by
  induction tree generalizing depth offset enabled with
  | skip remaining => exact fun _ _ => rfl
  | leaf => exact independent _ enabled
  | @fork remaining left right leftIH rightIH =>
      intro index state
      have addressKept : (frame.addressAt depth (by omega)).get
          ((frame.stack index.succ).flip state) =
          (frame.addressAt depth (by omega)).get state :=
        EncodedBit.get_flip_of_wire_ne _ _
          (frame.separate ⟨depth, by omega⟩ index.succ).symm state
      dsimp only [foldAt]
      rw [addressKept]
      rw [(leftIH (depth + 1) (by omega) offset
        (SelectorFrame.left_bound bounded) _ ) index state]
      exact (rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (SelectorFrame.right_bound bounded) _) index _

end

end QuantumAlg.EncodedBit.StreamedSelector
