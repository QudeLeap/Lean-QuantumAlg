/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Validity.Positive

/-! # Exact native resources of the actual complete finite geometry validity test -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- Each retained physical leaf pays one real CNOT, in addition to all actual selector forks. -/
lemma program_native_count (width : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (program width).eventCost =
      (tree width).forks * selectorForkCount .empty focus +
        (tree width).leafSum (fun _ => if .gate .cnot = focus then 1 else 0) := by
  rw [program, SelectorFrame.program_event_count]
  simp only [callback, leafGate, GateSpec.program_eventCost, GateSpec.event,
    ResourcePool.count_singleton]
  rfl

/-- The actual positive interval has 259 leaves and exactly 266 required fork nodes. -/
lemma p256_tree_counts : (tree 256).forks = 266 ∧
    (tree 256).leafSum (fun _ => 1) = 259 ∧
      (tree 256).leafSum (fun _ => 0) = 0 := by decide

private lemma p256_program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256).eventCost = 532 := by
  rw [program_native_count]
  change (tree 256).forks * 2 + (tree 256).leafSum (fun _ => 0) = 532
  rw [p256_tree_counts.1, p256_tree_counts.2.2]

private lemma p256_program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256).eventCost = 525 := by
  rw [program_native_count]
  change (tree 256).forks * 1 + (tree 256).leafSum (fun _ => 1) = 525
  rw [p256_tree_counts.1, p256_tree_counts.2.1]

private lemma p256_program_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256).eventCost = 532 := by
  rw [program_native_count]
  change (tree 256).forks * 2 + (tree 256).leafSum (fun _ => 0) = 532
  rw [p256_tree_counts.1, p256_tree_counts.2.2]

private lemma p256_program_quantumTime :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration = 1589 := by
  rw [program, SelectorFrame.program_quantumTime]
  change 5 * (tree 256).forks + (tree 256).leafSum (fun _ => 1) = 1589
  rw [p256_tree_counts.1, p256_tree_counts.2.1]

private lemma p256_highProgram_eventCost : (highProgram 256).eventCost = 0 := by
  rw [highProgram, p256_highTree]
  rfl

private lemma p256_highProgram_quantumTime :
    (highProgram 256).evaluatedEventDepth Resource.Event.quantumDuration = 0 := by
  rw [highProgram, p256_highTree]
  rfl

/-- The complete full-carry predicate keeps both actual negative-root X masks. -/
lemma p256_fullProgram_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (fullProgram 256).eventCost = 532 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (fullProgram 256).eventCost = 525 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (fullProgram 256).eventCost = 534 := by
  have maskTF : ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      ((maskGate 256).program (QubitLayout.canonical _) .empty).eventCost = 0 := rfl
  have maskCX : ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      ((maskGate 256).program (QubitLayout.canonical _) .empty).eventCost = 0 := rfl
  have maskX : ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit)
      ((maskGate 256).program (QubitLayout.canonical _) .empty).eventCost = 1 := rfl
  simp only [fullProgram, negativeProgram, UnitaryCircuit.seq_eventCost,
    p256_highProgram_eventCost, ResourcePool.count_add, ResourcePool.count_zero, maskTF,
    maskCX, maskX, p256_program_toffoli_count, p256_program_cnot_count,
    p256_program_singleQubit_count]
  decide

/-- Actual default duration follows the same native predicate, including both public X masks. -/
lemma p256_fullProgram_quantumTime :
    (fullProgram 256).evaluatedEventDepth Resource.Event.quantumDuration = 1591 := by
  rw [fullProgram, UnitaryCircuit.evaluatedEventDepth_seq, p256_highProgram_quantumTime,
    negativeProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, p256_program_quantumTime]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity
