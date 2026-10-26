/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Boundary.Exchange
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Boundary.Prefix
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Boundary.Exchange
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Fredkin

/-!
# Native resources of the complete actual controlled P-256 boundary

Both actual external predicate directions execute around the original
body. The body retains every word exchange, all four complete scanned
length writers and the original parity CNOT, on the same resident pool.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.BoundaryExchange

noncomputable section

open EncodedBit

private lemma program_pool (width : Nat) :
    (program width).eventCost = (sourceProgram width).eventCost := by rfl

private lemma program_time (width : Nat) :
    (program width).evaluatedEventDepth Resource.Event.quantumDuration =
      (sourceProgram width).evaluatedEventDepth Resource.Event.quantumDuration := by rfl

private lemma p256_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256).eventCost = 259 := by
  rw [program_pool, sourceProgram, GateSpec.programList_eventCost, ResourcePool.count_ofList]
  exact (sourceGates_counts 256).1

private lemma p256_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256).eventCost = 518 := by
  rw [program_pool, sourceProgram, GateSpec.programList_eventCost, ResourcePool.count_ofList]
  exact (sourceGates_counts 256).2.1

private lemma p256_quantumTime :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration = 777 := by
  rw [program_time, sourceProgram, GateSpec.programList_quantumTime]
  exact (sourceGates_counts 256).2.2

private lemma source_singleQubit_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program width).eventCost = 0 := by
  rw [program_pool, sourceProgram, GateSpec.programList_eventCost, ResourcePool.count_ofList,
    sourceGates, Word.fredkinGates, Word.indices_events]
  have zero (indices : List (Fin (width + 3))) :
      (indices.flatMap fun _ =>
        [Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot,
          .gate .toffoli, .gate .cnot]).count (.gate .singleQubit) = 0 := by
    induction indices with
    | nil => rfl
    | cons index rest inductionHypothesis =>
        simp [List.flatMap_cons, inductionHypothesis]
  exact zero _

private lemma p256_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256).eventCost = 0 := source_singleQubit_count 256

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.BoundaryExchange

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TerminalBoundary

noncomputable section

open EncodedBit

private lemma parity_pool (width : Nat) :
    (parityProgram width).eventCost = (paritySourceProgram width).eventCost := by rfl

private lemma parity_time (width : Nat) :
    (parityProgram width).evaluatedEventDepth Resource.Event.quantumDuration =
      (paritySourceProgram width).evaluatedEventDepth Resource.Event.quantumDuration := by rfl

private lemma parity_counts (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (parityProgram width).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (parityProgram width).eventCost = 1 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (parityProgram width).eventCost = 0 := by
  simp only [parity_pool, paritySourceProgram]
  refine ⟨?_, ?_, ?_⟩
  · rw [GateSpec.programList_toffoli_count_eq_sum]
    rfl
  · rw [GateSpec.programList_cnot_count_eq_sum]
    rfl
  · rw [GateSpec.programList_x_count_eq_sum]
    rfl

private lemma parity_quantumTime (width : Nat) :
    (parityProgram width).evaluatedEventDepth Resource.Event.quantumDuration = 1 := by
  rw [parity_time, paritySourceProgram, GateSpec.programList_quantumTime]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TerminalBoundary

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundaryBody

noncomputable section

private lemma program_pool (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost = (BoundaryExchange.program width).eventCost +
      ((LengthRefresh.program width (TerminalBoundary.capacity width enough)).eventCost +
        (TerminalBoundary.parityProgram width).eventCost) := by rfl

private lemma program_time (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth Resource.Event.quantumDuration =
      (BoundaryExchange.program width).evaluatedEventDepth Resource.Event.quantumDuration +
        ((LengthRefresh.program width (TerminalBoundary.capacity width enough)).evaluatedEventDepth
          Resource.Event.quantumDuration +
          (TerminalBoundary.parityProgram width).evaluatedEventDepth
            Resource.Event.quantumDuration) := by rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundaryBody

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundary

noncomputable section

open EncodedBit

private lemma shell_bound {middle limit : Nat} (bounded : middle ≤ limit)
    (first before after last : Nat) :
    first + (before + (middle + after) + last) ≤
      first + (before + (limit + after) + last) := by omega

private lemma program_pool (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost = (predicateProgram width enough false).eventCost +
      ((ControlledBoundaryBody.program width enough).eventCost +
        (predicateProgram width enough true).eventCost) := by rfl

private lemma program_time (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth Resource.Event.quantumDuration =
      (predicateProgram width enough false).evaluatedEventDepth Resource.Event.quantumDuration +
        ((ControlledBoundaryBody.program width enough).evaluatedEventDepth
          Resource.Event.quantumDuration +
            (predicateProgram width enough true).evaluatedEventDepth
              Resource.Event.quantumDuration) := by rfl

private lemma p256_predicate_counts (inverse : Bool) :
    ((predicateGates 256 (by decide) inverse).map GateSpec.toffoliMultiplicity).sum = 464 ∧
      ((predicateGates 256 (by decide) inverse).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((predicateGates 256 (by decide) inverse).map GateSpec.xMultiplicity).sum = 148 := by
  cases inverse
  · exact ControlledCounts.p256_boundary_source_counts
  · simpa only [predicateGates, if_true, List.map_reverse, List.sum_reverse] using
      ControlledCounts.p256_boundary_source_counts

private lemma p256_predicate_toffoli_count (inverse : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (predicateProgram 256 (by decide) inverse).eventCost = 1856 := by
  rw [predicateProgram, ControlledSourceWord.program_toffoli_count,
    (p256_predicate_counts inverse).1, (p256_predicate_counts inverse).2.1]

private lemma p256_predicate_cnot_count (inverse : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (predicateProgram 256 (by decide) inverse).eventCost = 148 := by
  rw [predicateProgram, ControlledSourceWord.program_cnot_count,
    (p256_predicate_counts inverse).2.2]

private lemma p256_predicate_quantumTime (inverse : Bool) :
    (predicateProgram 256 (by decide) inverse).evaluatedEventDepth
      Resource.Event.quantumDuration = 2004 := by
  rw [predicateProgram, ControlledSourceWord.program_quantumTime,
    (p256_predicate_counts inverse).1, (p256_predicate_counts inverse).2.1,
    (p256_predicate_counts inverse).2.2]

/-- The actual two predicate directions and all four real writers remain in the Toffoli cap. -/
lemma p256_program_toffoli_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 (by decide)).eventCost ≤ 85995 := by
  have writers := LengthRefresh.p256_program_toffoli_count_le
    (TerminalBoundary.capacity 256 (by decide))
  simp only [program_pool, ControlledBoundaryBody.program_pool, ResourcePool.count_add,
    p256_predicate_toffoli_count, BoundaryExchange.p256_toffoli_count,
    (TerminalBoundary.parity_counts 256).1]
  exact (shell_bound writers 1856 259 0 1856).trans (by decide)

/-- All native CNOTs, including the selected predicate masks and original parity, are charged. -/
lemma p256_program_cnot_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 (by decide)).eventCost ≤ 46043 := by
  have writers := LengthRefresh.p256_program_cnot_count_le
    (TerminalBoundary.capacity 256 (by decide))
  simp only [program_pool, ControlledBoundaryBody.program_pool, ResourcePool.count_add,
    p256_predicate_cnot_count, BoundaryExchange.p256_cnot_count,
    (TerminalBoundary.parity_counts 256).2.1]
  exact (shell_bound writers 148 518 1 148).trans (by decide)

/-- Only the four actual full length writers emit single-qubit gates in this complete macro. -/
lemma p256_program_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 (by decide)).eventCost = 33612 := by
  simp only [program_pool, ControlledBoundaryBody.program_pool, predicateProgram,
    ResourcePool.count_add, ControlledSourceWord.program_singleQubit_count,
    BoundaryExchange.p256_singleQubit_count, LengthRefresh.p256_program_singleQubit_count,
    (TerminalBoundary.parity_counts 256).2.2, Nat.zero_add, Nat.add_zero]

/-- The complete serial macro retains each original component's actual dependency schedule. -/
lemma p256_program_quantumTime_le :
    (program 256 (by decide)).evaluatedEventDepth Resource.Event.quantumDuration ≤ 165518 := by
  have writers := LengthRefresh.p256_program_quantumTime_le
    (TerminalBoundary.capacity 256 (by decide))
  simp only [program_time, ControlledBoundaryBody.program_time, p256_predicate_quantumTime,
    BoundaryExchange.p256_quantumTime, TerminalBoundary.parity_quantumTime]
  exact (shell_bound writers 2004 777 1 2004).trans (by decide)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundary
