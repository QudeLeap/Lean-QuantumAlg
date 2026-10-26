/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy.Tree
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Fork
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Preservation
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree.Leaf

/-!
# Full-state semantics of the actual policy-compiled first-one word

Every physical test restores its complete borrowed bank. The actual word
then has the same independent dirty-prefix action as the original emitter.
-/

namespace QuantumAlg.EncodedBit.FirstOne.TestPolicy

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  {frame : Frame encoding count outputWidth depth} (policy : TestPolicy frame)

/-- The literal native emitter realizes its full output-only action
on every original encoded state. -/
lemma policy_gatesAt_step (tree : ListPriority.Tree (Fin count)) (distinct : tree.leaves.Nodup)
    (level : Nat) (fits : level + tree.height ≤ depth) (state : Data) :
    GateSpec.stepList (policy.gatesAt tree distinct level fits) state =
      frame.actionAt tree level fits
        ((frame.stack.bit ⟨level, by omega⟩).get state) state := by
  induction tree generalizing level state with
  | empty => rfl
  | leaf label => exact frame.leafGates_step label _ state
  | fork higher lower higherCorrect lowerCorrect =>
      have present : level < depth := by
        change level + (max higher.height lower.height + 1) ≤ depth at fits
        omega
      let parent : Fin (depth + 1) := ⟨level, by omega⟩
      let next : Fin (depth + 1) := ⟨level + 1, by omega⟩
      have higherDistinct : higher.leaves.Nodup := (List.nodup_append.mp distinct).1
      have lowerDistinct : lower.leaves.Nodup := (List.nodup_append.mp distinct).2.1
      have higherFits : level + 1 + higher.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).1
        omega
      have lowerFits : level + 1 + lower.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).2
        omega
      let lowerStep := frame.actionAt lower (level + 1) lowerFits
      let higherStep := frame.actionAt higher (level + 1) higherFits
      have lowerLaw := lowerCorrect lowerDistinct (level + 1) lowerFits
      have higherLaw := higherCorrect higherDistinct (level + 1) higherFits
      have raw : GateSpec.stepList (policy.gatesAt (.fork higher lower) distinct level fits) state =
          forkStep (frame.enableAt level present) (frame.nextAt level present)
            (zeroPredicate (frame.subword higher.leaves)) lowerStep higherStep state := by
        dsimp only [gatesAt]
        simp only [GateSpec.stepList_append, GateSpec.stepList,
          policy.correct, GateSpec.step, lowerLaw, higherLaw]
        rfl
      exact raw.trans (forkStep_dirty_correct _ _ (Ne.symm (frame.enable_next_ne level present))
        (zeroPredicate (frame.subword higher.leaves))
        (frame.subwordZero_flip_stack higher.leaves next) lowerStep higherStep
        (fun selected => frame.actionAt_forkAction higher.leaves lower (level + 1) lowerFits
          selected parent next (Nat.le_refl _))
        (fun selected => frame.actionAt_forkAction higher.leaves higher (level + 1) higherFits
          selected parent next (Nat.le_refl _)) state)

/-- Every amplitude and external coherence follows
the same actual native encoded action. -/
lemma policy_programAt_realizes (tree : ListPriority.Tree (Fin count))
    (distinct : tree.leaves.Nodup)
    (level : Nat) (fits : level + tree.height ≤ depth)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding (policy.programAt tree distinct level fits) environment
      (fun state => frame.actionAt tree level fits
        ((frame.stack.bit ⟨level, by omega⟩).get state) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (policy.policy_gatesAt_step tree distinct level fits) environment

end

end QuantumAlg.EncodedBit.FirstOne.TestPolicy
