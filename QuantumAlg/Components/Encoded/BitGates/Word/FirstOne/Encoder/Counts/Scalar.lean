/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Counts
import all QuantumAlg.Util.List.PriorityTree.Tally

/-! # Exact original-tree coordinates through a scalar balanced recurrence -/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Independent public sentinel-XOR leaf weight at its original natural address. -/
def positionMaskCount (count outputWidth address : Nat) : Nat :=
  (Word.constantOneIndices
    ((BitVec.ofNat outputWidth count) ^^^ BitVec.ofNat outputWidth address).toFin).length

/-- Both complete original one-dirty conjunction calls at each real fork. -/
def testToffoliCharge (count : Nat) : Nat :=
  2 * (if count = 0 then 0 else Word.OneDirtyLayout.gateCount (count + 1))

/-- Both prefix CNOTs and both possible empty complete tests at each original fork. -/
def testCnotCharge (count : Nat) : Nat :=
  2 + 2 * (if count = 0 then 1 else 0)

private lemma toffoli_tally {count : Nat} (outputWidth : Nat)
    (tree : ListPriority.Tree (Fin count)) :
    emitterToffoliCount outputWidth tree =
      tree.tally (fun label => positionMaskCount count outputWidth label.val)
        testToffoliCharge := by
  induction tree with
  | empty => rfl
  | leaf _ => rfl
  | fork higher lower higherCount lowerCount =>
      simp only [emitterToffoliCount, ListPriority.Tree.tally, testToffoliCharge,
        higherCount, lowerCount]

private lemma cnot_tally {count : Nat} (tree : ListPriority.Tree (Fin count)) :
    emitterCnotCount tree = tree.tally (fun _ => 0) testCnotCharge := by
  induction tree with
  | empty => rfl
  | leaf _ => rfl
  | fork higher lower higherCount lowerCount =>
      simp only [emitterCnotCount, ListPriority.Tree.tally, testCnotCharge, higherCount, lowerCount]
      omega

private lemma volume_tally {count : Nat} (tree : ListPriority.Tree (Fin count)) :
    tree.testVolume = tree.tally (fun _ => 0) (fun size => size) := by
  induction tree with
  | empty => rfl
  | leaf _ => rfl
  | fork higher lower higherCount lowerCount =>
      simp only [ListPriority.Tree.testVolume, ListPriority.Tree.tally, higherCount, lowerCount]
      omega

private lemma forks_tally {count : Nat} (tree : ListPriority.Tree (Fin count)) :
    tree.forks = tree.tally (fun _ => 0) (fun _ => 1) := by
  induction tree with
  | empty => rfl
  | leaf _ => rfl
  | fork higher lower higherCount lowerCount =>
      simp only [ListPriority.Tree.forks, ListPriority.Tree.tally, higherCount, lowerCount]

/-- Exact Toffoli resources follow the independent scalar tree
before any concrete specialization. -/
lemma priorityTree_toffoli_scalar (count outputWidth height : Nat) (capacity : count ≤ 2 ^ height) :
    emitterToffoliCount outputWidth (Frame.priorityTree count height) =
      ListPriority.Tree.balancedTally (positionMaskCount count outputWidth) testToffoliCharge
        height 0 count := by
  rw [toffoli_tally]
  simpa only [Frame.priorityTree, List.length_finRange] using
    ListPriority.Tree.balanced_tally Fin.val (positionMaskCount count outputWidth)
    testToffoliCharge height (List.finRange count) 0
    (by simpa only [List.length_finRange] using ListPriority.Tree.finRange_address_order count)
    (by simpa only [List.length_finRange] using capacity)

/-- Exact CNOT resources follow the independent scalar tree
without concrete finite-list unfolding. -/
lemma priorityTree_cnot_scalar (count height : Nat) (capacity : count ≤ 2 ^ height) :
    emitterCnotCount (Frame.priorityTree count height) =
      ListPriority.Tree.balancedTally (fun _ => 0) testCnotCharge height 0 count := by
  rw [cnot_tally]
  simpa only [Frame.priorityTree, List.length_finRange] using
    ListPriority.Tree.balanced_tally Fin.val (fun _ => 0) testCnotCharge height
    (List.finRange count) 0
    (by simpa only [List.length_finRange] using ListPriority.Tree.finRange_address_order count)
    (by simpa only [List.length_finRange] using capacity)

/-- Complete test volume follows the independent scalar tree for every original finite source. -/
lemma priorityTree_volume_scalar (count height : Nat) (capacity : count ≤ 2 ^ height) :
    (Frame.priorityTree count height).testVolume =
      ListPriority.Tree.balancedTally (fun _ => 0) (fun size => size) height 0 count := by
  rw [volume_tally]
  simpa only [Frame.priorityTree, List.length_finRange] using
    ListPriority.Tree.balanced_tally Fin.val (fun _ => 0) (fun size => size) height
    (List.finRange count) 0
    (by simpa only [List.length_finRange] using ListPriority.Tree.finRange_address_order count)
    (by simpa only [List.length_finRange] using capacity)

/-- Original compact fork count follows the scalar tree without allocating padded leaves. -/
lemma priorityTree_forks_scalar (count height : Nat) (capacity : count ≤ 2 ^ height) :
    (Frame.priorityTree count height).forks =
      ListPriority.Tree.balancedTally (fun _ => 0) (fun _ => 1) height 0 count := by
  rw [forks_tally]
  simpa only [Frame.priorityTree, List.length_finRange] using
    ListPriority.Tree.balanced_tally Fin.val (fun _ => 0) (fun _ => 1) height
    (List.finRange count) 0
    (by simpa only [List.length_finRange] using ListPriority.Tree.finRange_address_order count)
    (by simpa only [List.length_finRange] using capacity)

end

end QuantumAlg.EncodedBit.FirstOne
