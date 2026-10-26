/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Resources

/-! # Separate exact native coordinates from the same original first-one tree -/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Exact native Toffoli recurrence, including both complete tests at every original fork. -/
def emitterToffoliCount {count : Nat} (outputWidth : Nat) : ListPriority.Tree (Fin count) → Nat
  | .empty => 0
  | .leaf label =>
      (Word.constantOneIndices (Frame.leafMask (outputWidth := outputWidth) label)).length
  | .fork higher lower => emitterToffoliCount outputWidth higher +
      emitterToffoliCount outputWidth lower +
      2 * (if higher.leaves.length = 0 then 0 else
        Word.OneDirtyLayout.gateCount (higher.leaves.length + 1))

/-- Exact native CNOT recurrence retains the two prefix CNOTs and the possible empty test. -/
def emitterCnotCount {count : Nat} : ListPriority.Tree (Fin count) → Nat
  | .empty => 0
  | .leaf _ => 0
  | .fork higher lower => emitterCnotCount higher + emitterCnotCount lower +
      2 + 2 * (if higher.leaves.length = 0 then 1 else 0)

private lemma zeroTrace_single (count : Nat) :
    (zeroTrace count).count (.gate .singleQubit) = 2 * count := by
  by_cases empty : count = 0 <;> simp [zeroTrace, empty, List.count_replicate, two_mul]

private lemma zeroTrace_cnot (count : Nat) :
    (zeroTrace count).count (.gate .cnot) = if count = 0 then 1 else 0 := by
  by_cases empty : count = 0 <;> simp [zeroTrace, empty, List.count_replicate]

private lemma zeroTrace_toffoli (count : Nat) :
    (zeroTrace count).count (.gate .toffoli) = if count = 0 then 0 else
      Word.OneDirtyLayout.gateCount (count + 1) := by
  by_cases empty : count = 0 <;> simp [zeroTrace, empty, List.count_replicate]

/-- Every test-volume occurrence contributes exactly four real mask X gates. -/
lemma emitterTrace_single {count : Nat} (outputWidth : Nat) (tree : ListPriority.Tree (Fin count)) :
    (emitterTrace outputWidth tree).count (.gate .singleQubit) = 4 * tree.testVolume := by
  induction tree with
  | empty => rfl
  | leaf label => simp [emitterTrace, List.count_replicate, ListPriority.Tree.testVolume]
  | fork higher lower higherCount lowerCount =>
      have expanded : (emitterTrace outputWidth (.fork higher lower)).count
          (.gate .singleQubit) = 2 * higher.leaves.length +
            (4 * lower.testVolume + (4 * higher.testVolume + 2 * higher.leaves.length)) := by
        simp [emitterTrace, higherCount, lowerCount, zeroTrace_single]
      rw [expanded, ListPriority.Tree.testVolume]
      omega

/-- The exact CNOT recurrence is the CNOT coordinate of the original native trace. -/
lemma emitterTrace_cnot {count : Nat} (outputWidth : Nat) (tree : ListPriority.Tree (Fin count)) :
    (emitterTrace outputWidth tree).count (.gate .cnot) = emitterCnotCount tree := by
  induction tree with
  | empty => rfl
  | leaf label => simp [emitterTrace, List.count_replicate, emitterCnotCount]
  | fork higher lower higherCount lowerCount =>
      have regroup (first second test : Nat) :
          test + (second + (1 + (first + (test + 1)))) = first + second + 2 + 2 * test := by
        omega
      simpa [emitterTrace, emitterCnotCount, higherCount, lowerCount, zeroTrace_cnot,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        regroup (emitterCnotCount higher) (emitterCnotCount lower)
          (if higher.leaves.length = 0 then 1 else 0)

/-- The exact Toffoli recurrence is the Toffoli coordinate of the original native trace. -/
lemma emitterTrace_toffoli {count : Nat} (outputWidth : Nat)
    (tree : ListPriority.Tree (Fin count)) :
    (emitterTrace outputWidth tree).count (.gate .toffoli) =
      emitterToffoliCount outputWidth tree := by
  induction tree with
  | empty => rfl
  | leaf label => simp [emitterTrace, emitterToffoliCount]
  | fork higher lower higherCount lowerCount =>
      have regroup (first second test : Nat) :
          test + (second + (first + test)) = first + second + 2 * test := by omega
      simpa [emitterTrace, emitterToffoliCount, higherCount, lowerCount, zeroTrace_toffoli,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        regroup (emitterToffoliCount outputWidth higher) (emitterToffoliCount outputWidth lower)
          (if higher.leaves.length = 0 then 0 else
            Word.OneDirtyLayout.gateCount (higher.leaves.length + 1))

namespace Frame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- The actual complete encoder's single-qubit coordinate counts both masks of both tests. -/
lemma encoderProgram_singleCount (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (frame.encoderProgram height capacity fits).eventCost =
      4 * (priorityTree count height).testVolume := by
  rw [frame.encoderProgram_eventCount]
  simp [encoderTrace, List.count_replicate, emitterTrace_single]

/-- The actual complete encoder's CNOT coordinate includes the paid sentinel load. -/
lemma encoderProgram_cnotCount (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (frame.encoderProgram height capacity fits).eventCost =
      (Word.constantOneIndices (BitVec.ofNat outputWidth count).toFin).length +
        emitterCnotCount (priorityTree count height) := by
  rw [frame.encoderProgram_eventCount]
  simp [encoderTrace, emitterTrace_cnot]

/-- The actual complete encoder's Toffoli coordinate includes every public leaf mask. -/
lemma encoderProgram_toffoliCount (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (frame.encoderProgram height capacity fits).eventCost =
      emitterToffoliCount outputWidth (priorityTree count height) := by
  rw [frame.encoderProgram_eventCount]
  simp [encoderTrace, List.count_replicate, emitterTrace_toffoli]

end Frame

end

end QuantumAlg.EncodedBit.FirstOne
