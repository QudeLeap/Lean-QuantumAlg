/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.ManyDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Counts.Concrete

/-! # Exact native coordinates of the actual arbitrary-bank first-one encoder -/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Both real complete arbitrary-bank test conjunctions at each original fork. -/
def manyDirtyToffoliCharge (count : Nat) : Nat :=
  2 * (if count = 0 then 0 else if count = 1 then 1 else 4 * (count - 1))

private lemma manyTrace_single (count : Nat) :
    (manyDirtyTrace count).count (.gate .singleQubit) = 2 * count := by
  by_cases empty : count = 0 <;> simp [manyDirtyTrace, empty, List.count_replicate, two_mul]

private lemma manyTrace_cnot (count : Nat) :
    (manyDirtyTrace count).count (.gate .cnot) = if count = 0 then 1 else 0 := by
  by_cases empty : count = 0 <;> simp [manyDirtyTrace, empty, List.count_replicate]

private lemma manyTrace_toffoli (count : Nat) :
    (manyDirtyTrace count).count (.gate .toffoli) =
      if count = 0 then 0 else if count = 1 then 1 else 4 * (count - 1) := by
  by_cases empty : count = 0 <;> simp [manyDirtyTrace, empty, List.count_replicate]

private lemma manyEmitter_single {count : Nat} (outputWidth : Nat)
    (tree : ListPriority.Tree (Fin count)) :
    (policyEmitterTrace manyDirtyTrace outputWidth tree).count (.gate .singleQubit) =
      4 * tree.testVolume := by
  induction tree with
  | empty => rfl
  | leaf label => simp [policyEmitterTrace, List.count_replicate, ListPriority.Tree.testVolume]
  | fork higher lower higherCount lowerCount =>
      have expanded : (policyEmitterTrace manyDirtyTrace outputWidth (.fork higher lower)).count
          (.gate .singleQubit) = 2 * higher.leaves.length +
            (4 * lower.testVolume + (4 * higher.testVolume + 2 * higher.leaves.length)) := by
        simp [policyEmitterTrace, higherCount, lowerCount, manyTrace_single]
      rw [expanded, ListPriority.Tree.testVolume]
      omega

private lemma manyEmitter_cnot {count : Nat} (outputWidth : Nat)
    (tree : ListPriority.Tree (Fin count)) :
    (policyEmitterTrace manyDirtyTrace outputWidth tree).count (.gate .cnot) =
      emitterCnotCount tree := by
  induction tree with
  | empty => rfl
  | leaf label => simp [policyEmitterTrace, List.count_replicate, emitterCnotCount]
  | fork higher lower higherCount lowerCount =>
      have regroup (first second test : Nat) :
          test + (second + (1 + (first + (test + 1)))) = first + second + 2 + 2 * test := by omega
      simpa [policyEmitterTrace, emitterCnotCount, higherCount, lowerCount, manyTrace_cnot,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        regroup (emitterCnotCount higher) (emitterCnotCount lower)
          (if higher.leaves.length = 0 then 1 else 0)

private lemma manyEmitter_toffoli {count : Nat} (outputWidth : Nat)
    (tree : ListPriority.Tree (Fin count)) :
    (policyEmitterTrace manyDirtyTrace outputWidth tree).count (.gate .toffoli) =
      tree.tally (fun label => positionMaskCount count outputWidth label.val)
        manyDirtyToffoliCharge := by
  induction tree with
  | empty => rfl
  | leaf label =>
      simp only [policyEmitterTrace, List.count_replicate_self, ListPriority.Tree.tally,
        Frame.leafMask, positionMaskCount]
  | fork higher lower higherCount lowerCount =>
      have regroup (first second test : Nat) :
          test + (second + (first + test)) = first + second + 2 * test := by omega
      simpa [policyEmitterTrace, ListPriority.Tree.tally, higherCount, lowerCount,
        manyTrace_toffoli, manyDirtyToffoliCharge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using regroup
          (higher.tally (fun label => positionMaskCount count outputWidth label.val)
            manyDirtyToffoliCharge)
          (lower.tally (fun label => positionMaskCount count outputWidth label.val)
            manyDirtyToffoliCharge)
          (if higher.leaves.length = 0 then 0 else if higher.leaves.length = 1 then 1
            else 4 * (higher.leaves.length - 1))

/-- Independent exact bank-backed scalar Toffoli recurrence at the actual 259 original positions. -/
lemma manyDirty259_toffoli_scalar :
    ListPriority.Tree.balancedTally (positionMaskCount 259 10) manyDirtyToffoliCharge 9 0 259 =
      7868 := by decide

namespace Frame.BorrowedBank

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {depth bankWidth : Nat}
  {frame : Frame encoding 259 10 depth} (bank : frame.BorrowedBank bankWidth)

/-- Actual full encoder native coordinates include both source masks and the paid sentinel load. -/
lemma manyDirtyEncoder259_counts (fits : 9 ≤ depth) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (bank.policy.encoderProgram 9 (by decide) fits).eventCost = 7868 ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (bank.policy.encoderProgram 9 (by decide) fits).eventCost = 519 ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (bank.policy.encoderProgram 9 (by decide) fits).eventCost = 4196 := by
  have toffoliTally := ListPriority.Tree.balanced_tally Fin.val (positionMaskCount 259 10)
    manyDirtyToffoliCharge 9 (List.finRange 259) 0
    (by simpa only [List.length_finRange] using ListPriority.Tree.finRange_address_order 259)
    (by simp only [List.length_finRange]; decide)
  simp only [List.length_finRange] at toffoliTally
  constructor
  · rw [bank.manyDirtyEncoder_eventCost, ResourcePool.count_ofList]
    simp only [policyEncoderTrace, List.count_append]
    have sentinel : (List.replicate
        (Word.constantOneIndices (BitVec.ofNat 10 259).toFin).length
        (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot)).count
          (.gate .toffoli) = 0 := by simp [List.count_replicate]
    rw [sentinel, Nat.zero_add, manyEmitter_toffoli]
    simpa only [priorityTree] using toffoliTally.trans manyDirty259_toffoli_scalar
  · constructor
    · rw [bank.manyDirtyEncoder_eventCost, ResourcePool.count_ofList]
      simp only [policyEncoderTrace, List.count_append, List.count_replicate_self,
        manyEmitter_cnot, priority259_cnot]
      rw [priority259_sentinel]
    · rw [bank.manyDirtyEncoder_eventCost, ResourcePool.count_ofList]
      simp [policyEncoderTrace, List.count_replicate, manyEmitter_single, priority259_testVolume]

/-- Every actual sequential native gate contributes to the dependency depth. -/
lemma manyDirtyEncoder259_unitDepth (fits : 9 ≤ depth) :
    (bank.policy.encoderProgram 9 (by decide) fits).evaluatedEventDepth (fun _ => 1) = 12583 := by
  have counts := bank.manyDirtyEncoder259_counts fits
  rw [TestPolicy.encoderProgram, GateSpec.programList_evaluatedEventDepth_unit,
    ← GateSpec.primitiveEventCount_programList]
  change GateSpec.primitiveEventCount (bank.policy.encoderProgram 9 (by decide) fits) = 12583
  rw [GateSpec.primitiveEventCount, counts.1, counts.2.1, counts.2.2]

end Frame.BorrowedBank

end

end QuantumAlg.EncodedBit.FirstOne
