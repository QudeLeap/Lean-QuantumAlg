/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Phase
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address

/-!
# Complete original address of the selected phase

The scalar follows the full-width original address and the retained static
leaf predicate. Skipped subtrees contribute exactly the identity scalar;
a complete traversal selects precisely its original finite address label.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The selected scalar follows exactly the same original address and retained leaf predicate. -/
lemma selectedPhaseAt_eq (frame : SelectorFrame encoding width)
    (phase : Fin (2 ^ width) → Data → ℂ) {remaining : Nat} (tree : SelectorTrie remaining)
    (depth : Nat) (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    frame.selectedPhaseAt phase tree depth fits offset bounded state =
      if frame.containsAt tree depth fits state then
        phase (frame.addressLabelAt remaining depth fits offset bounded state) state else 1 := by
  induction tree generalizing depth offset with
  | skip remaining => rfl
  | leaf => rfl
  | @fork remaining left right leftIH rightIH =>
      dsimp only [selectedPhaseAt, containsAt, addressLabelAt, addressAt]
      by_cases selected : (frame.address ⟨depth, by omega⟩).get state = true
      · simp only [selected, ↓reduceIte]
        exact rightIH (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded)
      · have cleared : (frame.address ⟨depth, by omega⟩).get state = false :=
          Bool.eq_false_iff.mpr selected
        simp only [cleared, Bool.false_eq_true, ↓reduceIte]
        exact leftIH (depth + 1) (by omega) offset (left_bound bounded)

/-- A full physical traversal selects the scalar at its original complete finite address. -/
lemma selectedPhaseAt_full (frame : SelectorFrame encoding width)
    (phase : Fin (2 ^ width) → Data → ℂ) (remaining depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    frame.selectedPhaseAt phase (SelectorTrie.full remaining) depth fits offset bounded state =
      phase (frame.addressLabelAt remaining depth fits offset bounded state) state := by
  induction remaining generalizing depth offset with
  | zero => rfl
  | succ remaining ih =>
      dsimp only [SelectorTrie.full, selectedPhaseAt, addressLabelAt, addressAt]
      by_cases selected : (frame.address ⟨depth, by omega⟩).get state = true
      · simp only [selected, ↓reduceIte]
        exact ih (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded)
      · have cleared : (frame.address ⟨depth, by omega⟩).get state = false :=
          Bool.eq_false_iff.mpr selected
        simp only [cleared, Bool.false_eq_true, ↓reduceIte]
        exact ih (depth + 1) (by omega) offset (left_bound bounded)

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
