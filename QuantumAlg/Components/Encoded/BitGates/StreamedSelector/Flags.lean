/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Address
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Enumeration
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address

/-!
# The unique selected boundary in an ordered native stream

Every retained static callback is visited. Exactly the callback whose full
label equals the unchanged original address receives the root enable; all
other callbacks receive false. The equality retains their execution order.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The original decoder remains within its full, untruncated static interval. -/
lemma addressLabelAt_bounds (frame : SelectorFrame encoding width)
    (remaining depth : Nat) (fits : depth + remaining = width)
    (offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    offset ≤ (frame.addressLabelAt remaining depth fits offset bounded state).val ∧
      (frame.addressLabelAt remaining depth fits offset bounded state).val <
        offset + 2 ^ remaining := by
  induction remaining generalizing depth offset with
  | zero => simp [SelectorFrame.addressLabelAt]
  | succ remaining ih =>
      dsimp only [SelectorFrame.addressLabelAt]
      split
      · have next := ih (depth + 1) (by omega) (offset + 2 ^ remaining)
          (SelectorFrame.right_bound bounded)
        rw [pow_succ]
        omega
      · have next := ih (depth + 1) (by omega) offset (SelectorFrame.left_bound bounded)
        rw [pow_succ]
        omega

private lemma foldl_flags_congr (action : Fin (2 ^ width) → Bool → Data → Data)
    (labels : List (Fin (2 ^ width))) (first second : Fin (2 ^ width) → Bool)
    (same : ∀ label, label ∈ labels → first label = second label) (state : Data) :
    labels.foldl (fun value label => action label (first label) value) state =
      labels.foldl (fun value label => action label (second label) value) state := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      simp only [List.foldl_cons]
      rw [same label (by simp)]
      exact ih (fun next present => same next (by simp [present])) _

private lemma foldBitsAt_false (bits : Fin width → Bool)
    (action : Fin (2 ^ width) → Bool → Data → Data)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    foldBitsAt bits action tree depth fits offset bounded false state =
      (labelsAt tree offset bounded).foldl (fun value label => action label false value) state := by
  induction tree generalizing depth offset state with
  | skip remaining => rfl
  | leaf => rfl
  | @fork remaining left right leftIH rightIH =>
      simp only [foldBitsAt, Bool.false_and, labelsAt, List.foldl_append]
      rw [leftIH, rightIH]

/-- One-hot boundary flags are attached to the actual ordered static callback list. -/
lemma foldBitsAt_eq_label_flags (frame : SelectorFrame encoding width)
    (bits : Fin width → Bool) (original : Data)
    (reads : ∀ index, (frame.address index).get original = bits index)
    (action : Fin (2 ^ width) → Bool → Data → Data)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (enabled : Bool) (state : Data) :
    foldBitsAt bits action tree depth fits offset bounded enabled state =
      (labelsAt tree offset bounded).foldl (fun value label =>
        action label (enabled && decide
          (label = frame.addressLabelAt remaining depth fits offset bounded original)) value)
        state := by
  induction tree generalizing depth offset enabled state with
  | skip remaining => rfl
  | leaf => simp [foldBitsAt, labelsAt, SelectorFrame.addressLabelAt]
  | @fork remaining left right leftIH rightIH =>
      have read : (frame.addressAt depth (by omega)).get original = bits ⟨depth, by omega⟩ :=
        reads _
      simp only [foldBitsAt, labelsAt, List.foldl_append]
      cases chosen : bits ⟨depth, by omega⟩ with
      | false =>
          simp only [SelectorFrame.addressLabelAt, read, chosen, Bool.not_false,
            Bool.and_true, Bool.and_false, Bool.false_eq_true, if_false]
          rw [leftIH, foldBitsAt_false]
          apply foldl_flags_congr
          intro label present
          have labelBounds := labelsAt_bounds right (offset + 2 ^ remaining)
            (SelectorFrame.right_bound bounded) label present
          have tagBounds := addressLabelAt_bounds frame remaining (depth + 1) (by omega)
            offset (SelectorFrame.left_bound bounded) original
          have different : label ≠ frame.addressLabelAt remaining (depth + 1) (by omega)
              offset (SelectorFrame.left_bound bounded) original := by
            intro same
            have := congrArg Fin.val same
            omega
          simp [different]
      | true =>
          simp only [SelectorFrame.addressLabelAt, read, chosen, Bool.not_true,
            Bool.and_false, Bool.and_true, if_true]
          rw [foldBitsAt_false, rightIH]
          have leftOff : (labelsAt left offset (SelectorFrame.left_bound bounded)).foldl
              (fun value label => action label false value) state =
                (labelsAt left offset (SelectorFrame.left_bound bounded)).foldl
                  (fun value label => action label (enabled && decide
                    (label = frame.addressLabelAt remaining (depth + 1) (by omega)
                      (offset + 2 ^ remaining) (SelectorFrame.right_bound bounded) original))
                    value) state := by
            apply foldl_flags_congr
            intro label present
            have labelBounds := labelsAt_bounds left offset (SelectorFrame.left_bound bounded)
              label present
            have tagBounds := addressLabelAt_bounds frame remaining (depth + 1) (by omega)
              (offset + 2 ^ remaining) (SelectorFrame.right_bound bounded) original
            have different : label ≠ frame.addressLabelAt remaining (depth + 1) (by omega)
                (offset + 2 ^ remaining) (SelectorFrame.right_bound bounded) original := by
              intro same
              have := congrArg Fin.val same
              omega
            simp [different]
          rw [leftOff]

end

end QuantumAlg.EncodedBit.StreamedSelector
