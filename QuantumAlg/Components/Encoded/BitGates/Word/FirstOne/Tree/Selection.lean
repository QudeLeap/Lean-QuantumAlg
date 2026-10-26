/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Preservation

/-!
# Unique original first-marked selection under clean future prefixes

The selection is independently the ordered tree search, hence List.find?.
Only the future prefix bits are required to start zero. The source word,
old output, parent enable and arbitrary work retain their original values.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- The actual complete static subword zero test is the pure ordered-tree zero predicate. -/
lemma subwordZero_eq_allZero (tree : ListPriority.Tree (Fin count)) (state : Data) :
    zeroPredicate (frame.subword tree.leaves) state =
      tree.allZero (fun label => (frame.source.bit label).get state) := by
  unfold zeroPredicate subword ListPriority.Tree.allZero
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.not_eq_true', List.any_eq_false]
  constructor
  · intro all label member
    rcases List.mem_iff_get.mp member with ⟨index, rfl⟩
    exact Bool.eq_false_iff.mp (all index)
  · intro all index
    exact Bool.eq_false_iff.mpr (all _ (List.get_mem _ index))

/-- Independent first-marked output action: one selected original public leaf mask or identity. -/
def emitAt (tree : ListPriority.Tree (Fin count)) (enabled : Bool) (state : Data) : Data :=
  if enabled then
    match tree.first (fun label => (frame.source.bit label).get state) with
    | none => state
    | some label => Word.xorConstantStep frame.output
        (leafMask (outputWidth := outputWidth) label) state
  else state

/-- Two mutually exclusive child visits select exactly the original ordered first marked leaf. -/
lemma emitAt_fork (higher lower : ListPriority.Tree (Fin count)) (enabled : Bool) (state : Data) :
    frame.emitAt higher (enabled && !zeroPredicate (frame.subword higher.leaves) state)
      (frame.emitAt lower (enabled && zeroPredicate (frame.subword higher.leaves) state) state) =
      frame.emitAt (.fork higher lower) enabled state := by
  cases enabled <;> cases zero : zeroPredicate (frame.subword higher.leaves) state
  all_goals
    simp only [emitAt, Bool.false_and, Bool.true_and,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
      ListPriority.Tree.first_fork, ← frame.subwordZero_eq_allZero, zero]

/-- Every strictly future supplied prefix starts in its original zero value. -/
def CleanFrom (level : Nat) (state : Data) : Prop :=
  ∀ index : Fin (depth + 1), level < index.val → (frame.stack.bit index).get state = false

/-- Clean future prefixes make the actual restored action select the unique original marked leaf. -/
lemma actionAt_clean (tree : ListPriority.Tree (Fin count)) (level : Nat)
    (fits : level + tree.height ≤ depth) (enabled : Bool) (state : Data)
    (clean : frame.CleanFrom level state) :
    frame.actionAt tree level fits enabled state = frame.emitAt tree enabled state := by
  induction tree generalizing level enabled state with
  | empty => cases enabled <;> rfl
  | leaf label =>
      cases enabled <;> cases marked : (frame.source.bit label).get state <;>
        simp [actionAt, emitAt, ListPriority.Tree.first, marked]
  | fork higher lower higherCorrect lowerCorrect =>
      have present : level < depth := by
        change level + (max higher.height lower.height + 1) ≤ depth at fits
        omega
      have higherFits : level + 1 + higher.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).1
        omega
      have lowerFits : level + 1 + lower.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).2
        omega
      let zero := zeroPredicate (frame.subword higher.leaves) state
      let lowerAction := frame.actionAt lower (level + 1) lowerFits
      let higherAction := frame.actionAt higher (level + 1) higherFits
      let lowerDone := lowerAction (enabled && zero) state
      have nextClean : (frame.nextAt level present).get state = false :=
        clean ⟨level + 1, by omega⟩ (show level < level + 1 by omega)
      have lowerActual : lowerDone = frame.emitAt lower (enabled && zero) state :=
        lowerCorrect _ _ _ _ (fun index after => clean index (by omega))
      have higherClean : frame.CleanFrom (level + 1) lowerDone := by
        intro index after
        rw [frame.actionAt_get_observed lower (level + 1) lowerFits (enabled && zero) state
          (frame.stack.bit index) (fun output => frame.outputStack output index)]
        exact clean index (by omega)
      have higherActual : higherAction (enabled && !zero) lowerDone =
          frame.emitAt higher (enabled && !zero) lowerDone :=
        higherCorrect _ _ _ _ higherClean
      change higherAction ((frame.nextAt level present).get state ^^ (enabled && !zero))
        (lowerAction ((frame.nextAt level present).get state ^^ (enabled && zero)) state) = _
      rw [nextClean]
      simp only [Bool.false_xor]
      rw [higherActual, lowerActual]
      exact frame.emitAt_fork higher lower enabled state

end

end QuantumAlg.EncodedBit.FirstOne.Frame
