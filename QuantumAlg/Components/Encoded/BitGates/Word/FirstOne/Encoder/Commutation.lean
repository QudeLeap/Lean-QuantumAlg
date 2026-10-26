/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Semantics

/-!
# Actual encoder commutation with an original outside metadata XOR

These are complete native step-list equalities on every encoded input.
No prefix cleanliness is assumed. Arbitrary work values and correlations
are restored by every actual test before the next external operation.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

private lemma constantMask_flip_comm (target : Word encoding outputWidth)
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

private lemma subwordZero_flip_outside (labels : List (Fin count)) (observed : EncodedBit encoding)
    (sourceOutside : ∀ index, (frame.source.bit index).wire ≠ observed.wire) (state : Data) :
    zeroPredicate (frame.subword labels) (observed.flip state) =
      zeroPredicate (frame.subword labels) state := by
  have retained (index : Fin labels.length) :
      ((frame.subword labels).bit index).get (observed.flip state) =
        ((frame.subword labels).bit index).get state :=
    get_flip_of_wire_ne _ _ (Ne.symm (sourceOutside (labels.get index))) state
  unfold zeroPredicate
  simp only [retained]

/-- The complete dirty-prefix action commutes with an outside bit on every encoded input. -/
lemma actionAt_flip_outside (tree : ListPriority.Tree (Fin count)) (level : Nat)
    (fits : level + tree.height ≤ depth) (enabled : Bool) (state : Data)
    (observed : EncodedBit encoding)
    (sourceOutside : ∀ index, (frame.source.bit index).wire ≠ observed.wire)
    (stackOutside : ∀ index, (frame.stack.bit index).wire ≠ observed.wire) :
    frame.actionAt tree level fits enabled (observed.flip state) =
      observed.flip (frame.actionAt tree level fits enabled state) := by
  induction tree generalizing level enabled state with
  | empty => rfl
  | leaf label =>
      dsimp only [actionAt]
      rw [get_flip_of_wire_ne _ _ (Ne.symm (sourceOutside label))]
      split
      · exact constantMask_flip_comm _ _ _ _
      · rfl
  | fork higher lower higherCorrect lowerCorrect =>
      have nextRead : ∀ value,
          (frame.nextAt level (by
            change level + (max higher.height lower.height + 1) ≤ depth at fits
            omega)).get (observed.flip value) =
            (frame.nextAt level (by
              change level + (max higher.height lower.height + 1) ≤ depth at fits
              omega)).get value :=
        get_flip_of_wire_ne _ _ (Ne.symm (stackOutside _))
      dsimp only [actionAt]
      simp only [nextRead, frame.subwordZero_flip_outside _ observed sourceOutside]
      rw [lowerCorrect, higherCorrect]

/-- The complete actual native encoder commutes with an outside bit without any clean promise. -/
lemma encoderStepList_flip_comm (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (observed : EncodedBit encoding)
    (sourceOutside : ∀ index, (frame.source.bit index).wire ≠ observed.wire)
    (outputOutside : ∀ index, (frame.output.bit index).wire ≠ observed.wire)
    (stackOutside : ∀ index, (frame.stack.bit index).wire ≠ observed.wire) (state : Data) :
    GateSpec.stepList (frame.encoderGates height capacity fits) (observed.flip state) =
      observed.flip (GateSpec.stepList (frame.encoderGates height capacity fits) state) := by
  have sentinelComm : GateSpec.stepList frame.sentinelGates (observed.flip state) =
      observed.flip (GateSpec.stepList frame.sentinelGates state) := by
    apply GateSpec.stepList_flip_comm_of_bitDisjoint
    intro gate member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact ⟨stackOutside _, outputOutside index⟩
  simp only [encoderGates, GateSpec.stepList_append]
  rw [sentinelComm, frame.gatesAt_step, frame.gatesAt_step]
  rw [get_flip_of_wire_ne _ _ (Ne.symm (stackOutside _))]
  exact frame.actionAt_flip_outside _ _ _ _ _ observed sourceOutside stackOutside

/-- The actual native encoder commutes with original metadata constant XOR
on every complete input. -/
lemma encoderStepList_xorConstantStep_comm {metadataWidth : Nat}
    (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth)
    (metadata : Word encoding metadataWidth) (constant : Fin (2 ^ metadataWidth))
    (sourceOutside : ∀ source target,
      (frame.source.bit source).wire ≠ (metadata.bit target).wire)
    (outputOutside : ∀ output target,
      (frame.output.bit output).wire ≠ (metadata.bit target).wire)
    (stackOutside : ∀ stack target,
      (frame.stack.bit stack).wire ≠ (metadata.bit target).wire) (state : Data) :
    GateSpec.stepList (frame.encoderGates height capacity fits)
        (Word.xorConstantStep metadata constant state) =
      Word.xorConstantStep metadata constant
        (GateSpec.stepList (frame.encoderGates height capacity fits) state) := by
  rw [Word.xorConstantStep_eq_indicesStep]
  unfold Word.xorConstantIndicesStep
  generalize Word.constantOneIndices constant = indices
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.foldl_cons]
      rw [ih, frame.encoderStepList_flip_comm height capacity fits (metadata.bit index)
        (sourceOutside · index) (outputOutside · index) (stackOutside · index)]

end

end QuantumAlg.EncodedBit.FirstOne.Frame
