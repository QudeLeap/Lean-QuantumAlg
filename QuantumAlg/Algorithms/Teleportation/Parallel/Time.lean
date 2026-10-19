/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Construction
public import QuantumAlg.Core.Execution.Time
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Trace

/-!
# Quantum computation time of the actual teleportation path

Every nonempty bank takes Alice's two sequential native gate layers and
at most Bob's two sequential correction layers. Disjoint blocks execute
in parallel within each native word. Measurements have zero duration in
the canonical quantum computation time, but remain actual emitted events
and retain all measured systems and result cells [dW19, qcnotes.tex:790,804].
This bound does not model the transmission delay of Alice's classical bits.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

private lemma block_alice_time :
    Block.aliceWord.evaluatedEventDepth Resource.Event.quantumDuration = 2 := by
  let first := UnitaryCircuit.onBinaryPrefix 1 Block.aliceCnot
  let second := Gate.singleQubitAt Block.layout .empty Gate.HOp 0 rfl
  calc
    _ = first.evaluatedEventDepth Resource.Event.quantumDuration +
        second.evaluatedEventDepth Resource.Event.quantumDuration :=
      UnitaryCircuit.evaluatedEventDepth_seq Resource.Event.quantumDuration first second
    _ = Block.aliceCnot.evaluatedEventDepth Resource.Event.quantumDuration +
        second.evaluatedEventDepth Resource.Event.quantumDuration :=
      congrArg (fun value => value + second.evaluatedEventDepth Resource.Event.quantumDuration)
        (UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth
          1 Resource.Event.quantumDuration Block.aliceCnot)
    _ = 2 := by rfl

private lemma block_correction_time (first second : Bool) :
    (Block.correctionWord first second).evaluatedEventDepth Resource.Event.quantumDuration ≤ 2 := by
  cases first <;> cases second <;> decide

/-- Empty banks have no native work; every other Alice bank has exactly two gate layers. -/
lemma aliceWord_time (count : Nat) :
    (aliceWord count).evaluatedEventDepth Resource.Event.quantumDuration =
      if count = 0 then 0 else 2 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      refine (UnitaryCircuit.parallelBinary_evaluatedEventDepth Resource.Event.quantumDuration
        Block.aliceWord (aliceWord count)).trans ?_
      refine (congrArg₂ (max : Nat → Nat → Nat) block_alice_time ih).trans ?_
      simp only [Nat.succ_ne_zero, if_false]
      split <;> rfl

/-- Every stored outcome selects at most the original X layer followed by the original Z layer. -/
lemma correctionWord_time_le (count : Nat) (bits : Fin count → Bool × Bool) :
    (correctionWord count bits).evaluatedEventDepth Resource.Event.quantumDuration ≤ 2 := by
  induction count with
  | zero => change (0 : Nat) ≤ 2; exact Nat.zero_le _
  | succ count ih =>
      exact (UnitaryCircuit.parallelBinary_evaluatedEventDepth Resource.Event.quantumDuration
        (Block.correctionWord (bits 0).1 (bits 0).2)
        (correctionWord count (fun index => bits index.succ))).le.trans
          (max_le (block_correction_time _ _) (ih _))

/-- The real measurement sequence contributes zero canonical quantum computation time. -/
lemma readouts_time (count : Nat)
    (path : (Circuit.measurementSequence (allowAllocation := false)
      (gates := AlgorithmGate.model) (oracles := .empty) (operations := .empty)
      (classicalOracles := .empty) (readouts count)).Path) :
    (Circuit.measurementSequence (allowAllocation := false)
      (gates := AlgorithmGate.model) (oracles := .empty) (operations := .empty)
      (classicalOracles := .empty) (readouts count)).quantumTime path = 0 := by
  rw [Circuit.quantumTime, Circuit.measurementSequence_depth]
  simp only [Circuit.zEvent, Resource.Event.quantumDuration_measurement,
    List.map_const', List.sum_replicate, smul_zero]

/-- Bound the actual complete path, including the dependency through measured feedback. -/
lemma code_time_le (count : Nat) (path : (code count).Path) :
    (code count).quantumTime path ≤ if count = 0 then 0 else 4 := by
  change (aliceWord count).evaluatedEventDepth Resource.Event.quantumDuration +
    ((Circuit.measurementSequence (allowAllocation := false)
      (gates := AlgorithmGate.model) (oracles := .empty) (operations := .empty)
      (classicalOracles := .empty) (readouts count)).quantumTime path.2.1 +
      (correctionWord count (storedBits path.2.2.1)).evaluatedEventDepth
        Resource.Event.quantumDuration) ≤ _
  rw [aliceWord_time, readouts_time, zero_add]
  by_cases empty : count = 0
  · subst count
    rfl
  · rw [if_neg empty, if_neg empty]
    exact Nat.add_le_add_left (correctionWord_time_le count _) 2

end

end QuantumAlg.QuantumTeleportation.Parallel
