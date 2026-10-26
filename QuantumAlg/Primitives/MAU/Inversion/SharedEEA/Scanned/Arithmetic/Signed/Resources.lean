/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Prefix
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Resources

/-!
# Resources of the actual fused signed source stages

The operand callbacks and selected top instructions share the same
physical unary forks. Both control lifts, all boundary CNOTs and the
paid initial moving-flag preparation come from the literal circuit.
These counts cover signed arithmetic stages; metadata geometry,
alignment and terminal length refresh are additional operations
[TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned

noncomputable section

open EncodedBit WindowLookup StreamedSelector NumberTheory.SharedEEA ArithmeticTemplate

private lemma operand_source (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    ((family width (stage kind)).payload label).source = source width (stage kind) label.val := rfl

private lemma top_source (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    (ArithmeticTop.payload width kind label).source =
      ArithmeticTop.source width kind label.val := rfl

/-- Native Toffolis count both actual controlled words and each shared retained fork. -/
lemma program_toffoli_count (width : Nat) (kind : ArithmeticTop.Kind) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program width kind).eventCost =
      2 * (tree width).forks + (tree width).leafSum (fun label =>
        ((source width (stage kind) label.val).map GateSpec.cnotMultiplicity).sum +
          4 * ((source width (stage kind) label.val).map GateSpec.toffoliMultiplicity).sum +
          ((ArithmeticTop.source width kind label.val).map GateSpec.cnotMultiplicity).sum +
          4 * ((ArithmeticTop.source width kind label.val).map GateSpec.toffoliMultiplicity).sum)
      := by
  rw [program, SelectorFrame.program_event_count]
  have forks : selectorForkCount .empty (.gate .toffoli) = 2 := by
    simp [selectorForkCount]
  rw [forks]
  simp only [callback, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    PayloadFamily.callback_toffoli, ArithmeticTop.callback, SelectedPayload.program_toffoli_count,
    operand_source, top_source, Nat.mul_comm, Nat.add_assoc]

/-- The boundary toggle is paid once per retained leaf, with no duplicated traversal. -/
lemma program_cnot_count (width : Nat) (kind : ArithmeticTop.Kind) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program width kind).eventCost =
      (tree width).forks + (tree width).leafSum (fun label =>
        ((source width (stage kind) label.val).map GateSpec.xMultiplicity).sum + 1 +
          ((ArithmeticTop.source width kind label.val).map GateSpec.xMultiplicity).sum) := by
  rw [program, SelectorFrame.program_event_count]
  have forks : selectorForkCount .empty (.gate .cnot) = 1 := by
    simp [selectorForkCount]
  rw [forks]
  simp only [callback, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    PayloadFamily.callback_cnot, ArithmeticTop.callback, SelectedPayload.program_cnot_count,
    operand_source, top_source, Nat.mul_one]

/-- Only the same retained physical forks emit single-qubit X instructions. -/
lemma program_single_count (width : Nat) (kind : ArithmeticTop.Kind) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program width kind).eventCost =
      2 * (tree width).forks + (tree width).leafSum (fun _ => 0) := by
  rw [program, SelectorFrame.program_event_count]
  have forks : selectorForkCount .empty (.gate .singleQubit) = 2 := by
    simp [selectorForkCount]
  rw [forks]
  simp only [callback, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    PayloadFamily.callback_single, ArithmeticTop.callback, SelectedPayload.program_single_count,
    Nat.add_zero, Nat.mul_comm]

/-- Actual dependency time includes each sequential native control lift and boundary toggle. -/
lemma program_quantumTime (width : Nat) (kind : ArithmeticTop.Kind) :
    (program width kind).evaluatedEventDepth Resource.Event.quantumDuration =
      5 * (tree width).forks + (tree width).leafSum (fun label =>
        ((source width (stage kind) label.val).map GateSpec.dirtyControlCount).sum + 1 +
          ((ArithmeticTop.source width kind label.val).map GateSpec.dirtyControlCount).sum) := by
  rw [program, SelectorFrame.program_quantumTime]
  simp only [callback, UnitaryCircuit.evaluatedEventDepth_seq,
    PayloadFamily.callback_quantumTime, ArithmeticTop.callback, SelectedPayload.program_quantumTime,
    operand_source, top_source]

/-- The initial control copy is an actual extra CNOT on the original source and pool wires. -/
lemma forwardProgram_eventCost (width : Nat) (kind : ArithmeticTop.Kind) :
    (forwardProgram width kind).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) +
        (program width kind).eventCost := by
  rw [forwardProgram, UnitaryCircuit.seq_eventCost]
  rfl

/-- The initial control preparation precedes the actual complete fused traversal. -/
lemma forwardProgram_quantumTime (width : Nat) (kind : ArithmeticTop.Kind) :
    (forwardProgram width kind).evaluatedEventDepth Resource.Event.quantumDuration =
      1 + (program width kind).evaluatedEventDepth Resource.Event.quantumDuration := by
  rw [forwardProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  rfl

/-- Exact Toffoli occurrences of the two actual P-256 fused traversals. -/
lemma p256_program_toffoli_count (kind : ArithmeticTop.Kind) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 kind).eventCost = match kind with
      | .pre => 1047
      | .carry => 2600 := by
  rw [program_toffoli_count]
  cases kind <;> decide

/-- Both actual fused P-256 traversals keep the same original 525 boundary and fork CNOTs. -/
lemma p256_program_cnot_count (kind : ArithmeticTop.Kind) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 kind).eventCost = 525 := by
  rw [program_cnot_count]
  cases kind <;> decide

/-- No second selector means the same 532 fork X instructions for each P-256 traversal. -/
lemma p256_program_single_count (kind : ArithmeticTop.Kind) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 kind).eventCost = 532 := by
  rw [program_single_count]
  decide

/-- Exact sequential native time of each P-256 traversal, before its paid initial copy. -/
lemma p256_program_quantumTime (kind : ArithmeticTop.Kind) :
    (program 256 kind).evaluatedEventDepth Resource.Event.quantumDuration = match kind with
      | .pre => 2104
      | .carry => 3657 := by
  rw [program_quantumTime]
  cases kind <;> decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned
