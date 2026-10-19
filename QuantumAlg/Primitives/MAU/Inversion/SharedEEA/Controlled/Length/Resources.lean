/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Length.Refresh
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Resources

/-!
# Actual resources of retained-Ctrl native length refresh

The bounds count every real boundary key, leading position, and set bit
of its length label. Every candidate includes the extra positive Ctrl
source, both actual masks, and complete dirty Iter cleanup. The four
writes retain the registered source order
[LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341].

These are bounds on the emitted controlled patterns and their actual
strict unit depth. No selector is discounted because its input fails to
match, and the original full-frame width is unchanged.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthResources

noncomputable section

open EncodedBit LengthCoordinates

/-- A full-word candidate envelope includes the actual additional Ctrl source. -/
def predicateBound (width : Nat) : Nat := 10 * (width.size + (width + 3) + 1) + 1

/-- An independent bound counts four writes, every boundary key, word position, and output bit. -/
def refreshBound (width : Nat) : Nat :=
  4 * (2 ^ width.size * ((width + 3) * (width.size * predicateBound width)))

lemma predicate_length_le (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (output : Fin width.size) :
    (ControlledLengthPredicate.gates width field key firstWord position output).length ≤
      predicateBound width := by
  have actual := ControlledLengthPredicate.gates_length_le
    width field key firstWord position output
  have within := position.isLt
  have regionBound := region_le width field key
  unfold predicateBound
  omega

lemma position_length_le (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) :
    (ControlledLengthWrite.positionGates width field key firstWord position).length ≤
      width.size * predicateBound width := by
  unfold ControlledLengthWrite.positionGates
  calc
    _ ≤ (Word.constantOneIndices (LengthWrite.positionConstant width field key position)).length *
        predicateBound width :=
      LengthResources.flatMap_length_le _ _ _ (fun output _ =>
        predicate_length_le width field key firstWord position output)
    _ ≤ _ := Nat.mul_le_mul_right _ (Word.constantOneIndices_length_le _)

lemma key_length_le (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool) :
    (ControlledLengthWrite.keyGates width field key firstWord).length ≤
      (width + 3) * (width.size * predicateBound width) := by
  unfold ControlledLengthWrite.keyGates
  calc
    _ ≤ (List.ofFn (fun position : Fin (region width field key) => position)).length *
        (width.size * predicateBound width) :=
      LengthResources.flatMap_length_le _ _ _ (fun position _ =>
        position_length_le width field key firstWord position)
    _ = region width field key * (width.size * predicateBound width) := by
      rw [List.length_ofFn]
    _ ≤ _ := Nat.mul_le_mul_right _ (region_le width field key)

lemma schedule_length_le (width : Nat) (field : Field) (firstWord : Bool) :
    (ControlledLengthWrite.gates width field firstWord).length ≤
      2 ^ width.size * ((width + 3) * (width.size * predicateBound width)) := by
  unfold ControlledLengthWrite.gates
  calc
    _ ≤ (LengthSchedule.keys width).length *
        ((width + 3) * (width.size * predicateBound width)) :=
      LengthResources.flatMap_length_le _ _ _
        (fun key _ => key_length_le width field key firstWord)
    _ = _ := by rw [LengthSchedule.keys_length]

/-- The actual four complete source-ordered native schedules satisfy the independent envelope. -/
lemma refresh_length_le (width : Nat) :
    (ControlledLengthRefresh.gates width).length ≤ refreshBound width := by
  unfold ControlledLengthRefresh.gates
  have actual := LengthResources.flatMap_length_le ControlledLengthRefresh.blocks
    (fun block => ControlledLengthWrite.gates width block.1 block.2)
    (2 ^ width.size * ((width + 3) * (width.size * predicateBound width)))
    (fun block _ => schedule_length_le width block.1 block.2)
  exact actual

/-- The same bound applies to actual strict unit depth of the same native program. -/
lemma program_depth_le (width : Nat) :
    (ControlledLengthRefresh.program width).evaluatedEventDepth (fun _ => 1) ≤
      refreshBound width := by
  rw [ControlledLengthRefresh.program_unitDepth]
  exact refresh_length_le width

/-- The exact actual event pool cardinality has the same independently stated finite bound. -/
lemma program_eventCount_le (width : Nat) :
    (ControlledLengthRefresh.program width).eventCost.card ≤ refreshBound width := by
  rw [ControlledLengthRefresh.program, GateSpec.programList_eventCost_card]
  exact refresh_length_le width

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlledLengthResources
