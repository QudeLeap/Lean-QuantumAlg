/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree

/-!
# Full-state semantic action of the native emitter, including dirty prefixes

This action exposes each original prefix value in the two child choices.
It changes only the supplied output word. Actual gate-list correspondence
is proved separately; no semantic predicate is a free circuit instruction.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- Retained dirty prefixes select both actual child visits; leaves xor only their public mask. -/
def actionAt : (tree : ListPriority.Tree (Fin count)) → (level : Nat) →
    (fits : level + tree.height ≤ depth) → Bool → Data → Data
  | .empty, _, _, _, state => state
  | .leaf label, _, _, enabled, state =>
      if enabled && (frame.source.bit label).get state then
        Word.xorConstantStep frame.output (leafMask (outputWidth := outputWidth) label) state
      else state
  | .fork higher lower, level, fits, enabled, state =>
      have present : level < depth := by
        change level + (max higher.height lower.height + 1) ≤ depth at fits
        omega
      have higherFits : level + 1 + higher.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).1
        omega
      have lowerFits : level + 1 + lower.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).2
        omega
      let old := (frame.nextAt level present).get state
      let zero := zeroPredicate (frame.subword higher.leaves) state
      let lowerDone := actionAt lower (level + 1) lowerFits
        (old ^^ (enabled && zero)) state
      actionAt higher (level + 1) higherFits (old ^^ (enabled && !zero)) lowerDone

/-- Every physical read outside the supplied output word retains its original exact value. -/
lemma actionAt_get_observed (tree : ListPriority.Tree (Fin count)) (level : Nat)
    (fits : level + tree.height ≤ depth) (enabled : Bool) (state : Data)
    (observed : EncodedBit encoding)
    (different : ∀ index, (frame.output.bit index).wire ≠ observed.wire) :
    observed.get (frame.actionAt tree level fits enabled state) = observed.get state := by
  induction tree generalizing level enabled state with
  | empty => rfl
  | leaf label =>
      dsimp only [actionAt]
      split
      · exact Word.xorConstantStep_get_observed_of_target_ne _ _ _ different state
      · rfl
  | fork higher lower higherCorrect lowerCorrect =>
      exact (higherCorrect _ _ _ _).trans (lowerCorrect _ _ _ _)

end

end QuantumAlg.EncodedBit.FirstOne.Frame
