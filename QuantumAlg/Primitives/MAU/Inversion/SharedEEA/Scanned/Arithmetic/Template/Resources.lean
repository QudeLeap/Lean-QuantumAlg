/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Forward
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Resources

/-!
# Native resources of each actual streamed TTK stage

The full static traversal is charged, including gates on inactive coherent
branches, every reversible fork and the paid initial control copy. Original
source Toffolis use four actual Toffolis with restored arbitrary dirty work.
Shared controls retain their actual sequential quantum duration.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The original native traversal accounts for both forks and every visited payload. -/
lemma program_toffoli_count (width : Nat) (stage : Stage) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program width stage).eventCost =
      2 * (tree width).forks + (tree width).leafSum (fun label =>
        ((source width stage label.val).map GateSpec.cnotMultiplicity).sum +
          4 * ((source width stage label.val).map GateSpec.toffoliMultiplicity).sum) :=
  (family width stage).program_toffoli_count (QubitLayout.canonical _) .empty (tree width)

/-- Every retained boundary has one real CNOT, beside the actual selector forks. -/
lemma program_cnot_count (width : Nat) (stage : Stage) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program width stage).eventCost =
      (tree width).forks + (tree width).leafSum (fun label =>
        ((source width stage label.val).map GateSpec.xMultiplicity).sum + 1) :=
  (family width stage).program_cnot_count (QubitLayout.canonical _) .empty (tree width)

/-- Only the actual selector forks contain single-qubit instructions. -/
lemma program_single_count (width : Nat) (stage : Stage) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program width stage).eventCost =
      2 * (tree width).forks + (tree width).leafSum (fun _ => 0) :=
  (family width stage).program_single_count (QubitLayout.canonical _) .empty (tree width)

/-- The default duration is derived from the original native gate sequence. -/
lemma program_quantumTime (width : Nat) (stage : Stage) :
    (program width stage).evaluatedEventDepth Resource.Event.quantumDuration =
      5 * (tree width).forks + (tree width).leafSum (fun label =>
        ((source width stage label.val).map GateSpec.dirtyControlCount).sum + 1) :=
  (family width stage).program_quantumTime (QubitLayout.canonical _) .empty (tree width)

/-- The moving flag is prepared by one paid CNOT on the existing source and pool positions. -/
lemma forwardProgram_eventCost (width : Nat) (stage : Stage) :
    (forwardProgram width stage).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) +
        (program width stage).eventCost := by
  rw [forwardProgram, UnitaryCircuit.seq_eventCost]
  rfl

/-- The control copy precedes the actual traversal, so its duration is included. -/
lemma forwardProgram_quantumTime (width : Nat) (stage : Stage) :
    (forwardProgram width stage).evaluatedEventDepth Resource.Event.quantumDuration =
      1 + (program width stage).evaluatedEventDepth Resource.Event.quantumDuration := by
  rw [forwardProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  rfl

/-- Exact Toffoli occurrences for each actual P-256 source stage. -/
lemma p256_program_toffoli_count (stage : Stage) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 stage).eventCost =
      match stage with
      | .preXor => 790
      | .descendingXor | .ascendingXor => 789
      | .carry => 1564
      | .descendingUncompute => 1822
      | .finalXor => 791 := by
  rw [program_toffoli_count]
  cases stage <;> decide

/-- The same P-256 traversal has 525 CNOTs before the paid initial copy. -/
lemma p256_program_cnot_count (stage : Stage) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 stage).eventCost = 525 := by
  rw [program_cnot_count]
  cases stage <;> decide

/-- Every P-256 traversal executes the 532 actual fork X instructions. -/
lemma p256_program_single_count (stage : Stage) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 stage).eventCost = 532 := by
  rw [program_single_count]
  decide

/-- Exact default duration of each P-256 native traversal before its initial control copy. -/
lemma p256_program_quantumTime (stage : Stage) :
    (program 256 stage).evaluatedEventDepth Resource.Event.quantumDuration =
      match stage with
      | .preXor => 1847
      | .descendingXor | .ascendingXor => 1846
      | .carry => 2621
      | .descendingUncompute => 2879
      | .finalXor => 1848 := by
  rw [program_quantumTime]
  cases stage <;> decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
