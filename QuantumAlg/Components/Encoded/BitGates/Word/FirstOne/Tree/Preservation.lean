/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Action
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Fork

/-!
# Full source and retained-prefix laws of the first-one emitter action

Only actual output X flips occur in the semantic action. Every source,
prefix and arbitrary dirty-work read survives, and flipping an earlier
retained prefix commutes with an action whose enable is supplied explicitly.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

private lemma xorConstantStep_flip (target : Word encoding outputWidth)
    (constant : Fin (2 ^ outputWidth)) (observed : EncodedBit encoding) (state : Data) :
    Word.xorConstantStep target constant (observed.flip state) =
      observed.flip (Word.xorConstantStep target constant state) := by
  unfold Word.xorConstantStep Word.xorConstantGates
  generalize Word.constantOneIndices constant = indices
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      change GateSpec.stepList (rest.map fun bit => .x (target.bit bit))
          ((target.bit index).flip (observed.flip state)) =
        observed.flip (GateSpec.stepList (rest.map fun bit => .x (target.bit bit))
          ((target.bit index).flip state))
      rw [flip_comm (target.bit index) observed state, ih]

/-- A retained prefix flip cannot change any full original static subword zero predicate. -/
lemma subwordZero_flip_stack (labels : List (Fin count)) (index : Fin (depth + 1))
    (state : Data) :
    zeroPredicate (frame.subword labels) ((frame.stack.bit index).flip state) =
      zeroPredicate (frame.subword labels) state := by
  have stable (selected : Fin labels.length) :
      ((frame.subword labels).bit selected).get ((frame.stack.bit index).flip state) =
        ((frame.subword labels).bit selected).get state :=
    get_flip_of_wire_ne _ _ (Ne.symm (frame.sourceStack (labels.get selected) index)) state
  unfold zeroPredicate
  simp only [stable]

/-- The output-only action retains each complete original source zero predicate. -/
lemma subwordZero_actionAt (labels : List (Fin count)) (tree : ListPriority.Tree (Fin count))
    (level : Nat) (fits : level + tree.height ≤ depth) (enabled : Bool) (state : Data) :
    zeroPredicate (frame.subword labels) (frame.actionAt tree level fits enabled state) =
      zeroPredicate (frame.subword labels) state := by
  have stable (selected : Fin labels.length) :
      ((frame.subword labels).bit selected).get (frame.actionAt tree level fits enabled state) =
        ((frame.subword labels).bit selected).get state :=
    frame.actionAt_get_observed tree level fits enabled state _
      (fun output => Ne.symm (frame.sourceOutput (labels.get selected) output))
  unfold zeroPredicate
  simp only [stable]

/-- An explicitly selected action commutes with every current or earlier retained prefix flip. -/
lemma actionAt_flip_stack (tree : ListPriority.Tree (Fin count)) (level : Nat)
    (fits : level + tree.height ≤ depth) (enabled : Bool) (state : Data)
    (index : Fin (depth + 1)) (earlier : index.val ≤ level) :
    frame.actionAt tree level fits enabled ((frame.stack.bit index).flip state) =
      (frame.stack.bit index).flip (frame.actionAt tree level fits enabled state) := by
  induction tree generalizing level enabled state with
  | empty => rfl
  | leaf label =>
      dsimp only [actionAt]
      rw [get_flip_of_wire_ne _ _ (Ne.symm (frame.sourceStack label index))]
      split
      · exact xorConstantStep_flip _ _ _ _
      · rfl
  | fork higher lower higherCorrect lowerCorrect =>
      have present : level < depth := by
        change level + (max higher.height lower.height + 1) ≤ depth at fits
        omega
      have different : (frame.stack.bit index).wire ≠ (frame.nextAt level present).wire := by
        intro same
        have equal := frame.stackDistinct same
        have values := congrArg (fun position : Fin (depth + 1) => position.val) equal
        change index.val = level + 1 at values
        omega
      have nextRead : ∀ value,
          (frame.nextAt level present).get ((frame.stack.bit index).flip value) =
            (frame.nextAt level present).get value :=
        get_flip_of_wire_ne _ _ different
      dsimp only [actionAt]
      simp only [nextRead, frame.subwordZero_flip_stack]
      rw [lowerCorrect _ _ _ _ (by omega), higherCorrect _ _ _ _ (by omega)]

/-- An explicitly selected child protects its retained parent, next prefix and full test word. -/
lemma actionAt_forkAction (labels : List (Fin count)) (tree : ListPriority.Tree (Fin count))
    (level : Nat) (fits : level + tree.height ≤ depth) (enabled : Bool)
    (parent next : Fin (depth + 1)) (earlier : next.val ≤ level) :
    ForkAction (frame.stack.bit parent) (frame.stack.bit next)
      (zeroPredicate (frame.subword labels)) (frame.actionAt tree level fits enabled) where
  enable_get state := frame.actionAt_get_observed tree level fits enabled state _
    (fun output => frame.outputStack output parent)
  next_get state := frame.actionAt_get_observed tree level fits enabled state _
    (fun output => frame.outputStack output next)
  next_flip state := frame.actionAt_flip_stack tree level fits enabled state next earlier
  predicate_get state := frame.subwordZero_actionAt labels tree level fits enabled state

end

end QuantumAlg.EncodedBit.FirstOne.Frame
