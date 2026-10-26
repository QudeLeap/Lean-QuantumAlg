/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Semantics
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Selection
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor.Composition

/-!
# Full-state clean-prefix semantics of the actual balanced first-one encoder

The output word starts arbitrary. The same original root selects XOR of
its original first marked source position, or the original count sentinel.
Only future prefixes start zero; every other physical system and every
external reference follows the complete actual native unitary.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

private def sentinelStep (state : Data) : Data :=
  GateSpec.stepList frame.sentinelGates state

private lemma sentinelStep_get (observed : EncodedBit encoding)
    (outside : ∀ output, (frame.output.bit output).wire ≠ observed.wire) (state : Data) :
    observed.get (frame.sentinelStep state) = observed.get state :=
  Word.controlledXorConstantStep_get_observed_of_target_ne _ _ _ _ observed outside state

private lemma sentinelStep_selected (state : Data) :
    frame.sentinelStep state = if (frame.stack.bit ⟨0, by omega⟩).get state then
      Word.xorConstantStep frame.output (BitVec.ofNat outputWidth count).toFin state else state :=
  Word.controlledXorConstantStep_eq_selected _ _ _ _ state

/-- The complete actual encoder XORs the original first position, retaining the full complement. -/
lemma encoderGates_step (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    GateSpec.stepList (frame.encoderGates height capacity fits) state =
      if (frame.stack.bit ⟨0, by omega⟩).get state then
        Word.xorConstantStep frame.output
          (BitVec.ofNat outputWidth (frame.firstPosition state)).toFin state else state := by
  let tree := priorityTree count height
  let loaded := frame.sentinelStep state
  have cleanLoaded : frame.CleanFrom 0 loaded := by
    intro index later
    rw [frame.sentinelStep_get (frame.stack.bit index) (frame.outputStack · index)]
    exact clean index later
  have rootLoaded : (frame.stack.bit ⟨0, by omega⟩).get loaded =
      (frame.stack.bit ⟨0, by omega⟩).get state :=
    frame.sentinelStep_get _ (frame.outputStack · _) state
  have sourceLoaded : ∀ label, (frame.source.bit label).get loaded =
      (frame.source.bit label).get state :=
    fun label => frame.sentinelStep_get _
      (fun output => Ne.symm (frame.sourceOutput label output)) _
  have sameSearch : tree.first (fun label => (frame.source.bit label).get loaded) =
      tree.first (fun label => (frame.source.bit label).get state) := by
    congr 1
    funext label
    exact sourceLoaded label
  rw [encoderGates, GateSpec.stepList_append, frame.gatesAt_step]
  change frame.actionAt tree 0 _
    ((frame.stack.bit ⟨0, by omega⟩).get loaded) loaded = _
  rw [frame.actionAt_clean _ _ _ _ _ cleanLoaded]
  change frame.emitAt tree ((frame.stack.bit ⟨0, by omega⟩).get loaded) loaded = _
  rw [rootLoaded]
  unfold emitAt
  rw [sameSearch, ListPriority.Tree.first_eq_position tree (priorityTree_leaves capacity)]
  cases selected : (frame.stack.bit ⟨0, by omega⟩).get state
  · simp only [Bool.false_eq_true, if_false]
    exact (frame.sentinelStep_selected state).trans (by simp only [selected, Bool.false_eq_true,
      if_false])
  · simp only [if_true]
    have loadedValue : loaded =
        Word.xorConstantStep frame.output (BitVec.ofNat outputWidth count).toFin state :=
      (frame.sentinelStep_selected state).trans (by simp only [selected, if_true])
    by_cases present : (ListPriority.Tree.position
        (fun label => (frame.source.bit label).get state)) < count
    · rw [dif_pos present]
      dsimp only
      rw [loadedValue, leafMask, Word.xorConstantStep_xor _ _ _ frame.outputDistinct]
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
      rfl
    · rw [dif_neg present]
      dsimp only
      have sentinel : frame.firstPosition state = count :=
        Nat.le_antisymm (ListPriority.Tree.position_le _) (Nat.le_of_not_gt present)
      rw [loadedValue, sentinel]

end

end QuantumAlg.EncodedBit.FirstOne.Frame
