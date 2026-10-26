/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Predicates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Phase
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Gates

/-!
# Actual complete phase-update resources on the retained P-256 frame

Each original predicate preparation and its complete reverse execute.
Only the actual middle gates acquire external control. The zero-clock
case includes the complete high-clock predicate; it is not simplified
using a reachable-state invariant.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPhaseUpdates

noncomputable section

open EncodedBit

private lemma p256_prepare_counts (zero : Bool) :
    ((prepare 256 (by decide) zero).map GateSpec.toffoliMultiplicity).sum =
        (if zero then 228 else 92) ∧
      ((prepare 256 (by decide) zero).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((prepare 256 (by decide) zero).map GateSpec.xMultiplicity).sum =
        (if zero then 94 else 54) := by
  cases zero
  · exact ControlledCounts.p256_ordered_source_counts
  · exact ControlledCounts.p256_terminal_source_counts

private lemma middle_counts (width : Nat) (zero : Bool) :
    ((middle width zero).map GateSpec.toffoliMultiplicity).sum = (if zero then 0 else 3) ∧
      ((middle width zero).map GateSpec.cnotMultiplicity).sum = (if zero then 2 else 0) ∧
      ((middle width zero).map GateSpec.xMultiplicity).sum = 0 := by
  cases zero <;> exact ⟨rfl, rfl, rfl⟩

/-- Actual ordered and complete-clock phase words retain their exact native Toffoli counts. -/
lemma p256_program_toffoli_count (zero : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 (by decide) zero).eventCost = (if zero then 458 else 196) := by
  rw [program, ControlledPredicated.program_toffoli_count,
    (p256_prepare_counts zero).1, (middle_counts 256 zero).1,
    (middle_counts 256 zero).2.1]
  cases zero <;> decide

/-- These two actual middle words have no native selected X, and the predicates have no CNOT. -/
lemma p256_program_cnot_count (zero : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 (by decide) zero).eventCost = 0 := by
  rw [program, ControlledPredicated.program_cnot_count,
    (p256_prepare_counts zero).2.1, (middle_counts 256 zero).2.2]

/-- Both original predicate-mask directions remain charged in the actual native program. -/
lemma p256_program_singleQubit_count (zero : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 (by decide) zero).eventCost = (if zero then 188 else 108) := by
  rw [program, ControlledPredicated.program_singleQubit_count,
    (p256_prepare_counts zero).2.2]
  cases zero <;> decide

/-- Serial native duration includes both full original predicate words and selected payload. -/
lemma p256_program_quantumTime (zero : Bool) :
    (program 256 (by decide) zero).evaluatedEventDepth Resource.Event.quantumDuration =
      (if zero then 646 else 304) := by
  rw [program, ControlledPredicated.program_quantumTime,
    (p256_prepare_counts zero).1, (p256_prepare_counts zero).2.1,
    (p256_prepare_counts zero).2.2, (middle_counts 256 zero).1,
    (middle_counts 256 zero).2.1, (middle_counts 256 zero).2.2]
  cases zero <;> decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPhaseUpdates
