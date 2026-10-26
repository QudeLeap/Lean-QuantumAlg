/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.ManyDirty.Frame
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.ZeroTest
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern

/-!
# Actual complete source zero test with an existing restored arbitrary bank

The physical enable is an additional positive control. All original
source bits are masked and unmasked by actual X gates; the real borrowed
conjunction restores every arbitrary bank bit on every input.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame.BorrowedBank

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {count outputWidth depth bankWidth : Nat}
  {frame : Frame encoding count outputWidth depth} (bank : frame.BorrowedBank bankWidth)

/-- Both source masks and the complete actual borrowed conjunction, with its true empty case. -/
def testGates : (labels : List (Fin count)) → labels.Nodup →
    (level : Nat) → level < depth → List (GateSpec encoding)
  | [], _, level, present =>
      [.cnot (frame.enableAt level present) (frame.nextAt level present)
        (frame.enable_next_ne level present)]
  | head :: rest, unique, level, present =>
      let mask := (frame.testLayout (head :: rest) unique level present).patternMaskGates
        (fun _ => false)
      mask ++ (bank.conjunctionLayout head rest unique level present).borrowedAndGates ++
        mask.reverse

private lemma maskedConjunction (head : Fin count) (rest : List (Fin count))
    (unique : (head :: rest).Nodup) (level : Nat) (present : level < depth) (state : Data) :
    Word.ZeroTestLayout.sourceConjunction (bank.conjunctionLayout head rest unique level present)
        (GateSpec.stepList ((frame.testLayout (head :: rest) unique level present).patternMaskGates
          (fun _ => false)) state) (rest.length + 2) =
      ((frame.enableAt level present).get state &&
        zeroPredicate (frame.subword (head :: rest)) state) := by
  let original := frame.testLayout (head :: rest) unique level present
  let mask := original.patternMaskGates (fun _ => false)
  have enableRead : (frame.enableAt level present).get (GateSpec.stepList mask state) =
      (frame.enableAt level present).get state := by
    apply GateSpec.stepList_get_of_bitDisjoint
    intro gate member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact frame.sourceStack ((head :: rest).get index) ⟨level, by omega⟩
  apply Bool.eq_iff_iff.mpr
  rw [Word.ZeroTestLayout.sourceConjunction_eq_true_iff, Bool.and_eq_true_iff]
  change (∀ index : Fin (rest.length + 2),
      (Fin.cases (motive := fun _ : Fin (rest.length + 2) => EncodedBit encoding)
        (frame.enableAt level present) original.source.bit index).get
        (GateSpec.stepList mask state) = true) ↔ _
  rw [Fin.forall_fin_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, enableRead]
  have matched := original.masked_all_iff (fun _ => false) state
  change (∀ index : Fin (rest.length + 1),
    (original.source.bit index).get (GateSpec.stepList mask state) = true) ↔ _ at matched
  rw [matched]
  simp only [zeroPredicate, Word.OneDirtyLayout.PatternMatches, decide_eq_true_eq]
  rfl

/-- Every original source, output complement and arbitrary bank value
has the exact restored action. -/
lemma manyDirtyTest_step (labels : List (Fin count)) (unique : labels.Nodup)
    (level : Nat) (present : level < depth) (state : Data) :
    GateSpec.stepList (bank.testGates labels unique level present) state =
      predicateFlip (frame.nextAt level present)
        (fun value => (frame.enableAt level present).get value &&
          zeroPredicate (frame.subword labels) value) state := by
  cases labels with
  | nil =>
      simp [testGates, GateSpec.stepList, GateSpec.step, cnotStep, predicateFlip, zeroPredicate]
  | cons head rest =>
      let original := frame.testLayout (head :: rest) unique level present
      let mask := original.patternMaskGates (fun _ => false)
      have outputOutside : ∀ gate ∈ mask,
          GateSpec.bitDisjoint (frame.nextAt level present) gate := by
        intro gate member
        obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
        exact frame.sourceStack ((head :: rest).get index) _
      rw [testGates, GateSpec.stepList_append, GateSpec.stepList_append,
        Word.ZeroTestLayout.borrowedAndGates_step, bank.maskedConjunction]
      change GateSpec.stepList mask.reverse
        (if _ then (frame.nextAt level present).flip (GateSpec.stepList mask state)
          else GateSpec.stepList mask state) = _
      unfold predicateFlip
      split
      · rw [GateSpec.stepList_flip_comm_of_bitDisjoint mask.reverse (frame.nextAt level present)
          (fun gate member => outputOutside gate (List.mem_reverse.mp member)),
          GateSpec.stepList_reverse_stepList]
      · exact GateSpec.stepList_reverse_stepList mask state

/-- The policy compiles only actual native gates and proves complete arbitrary-bank restoration. -/
def policy : TestPolicy frame where
  gates := bank.testGates
  correct := bank.manyDirtyTest_step

end

end QuantumAlg.EncodedBit.FirstOne.Frame.BorrowedBank
