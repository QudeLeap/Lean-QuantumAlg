/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Events
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.ClassicalCoordinates
import all QuantumAlg.Core.Base.Accounting.Weighted
import QuantumAlg.Util.Nat.ChooseTwo

/-!
# Quantum event counts and closed Shor resource coordinates

This auxiliary weight counts quantum gates, source queries, preparation and
measurement, assigning zero to classical events. Its weighted sums preserve
the original complete event envelopes, including reset and initialization.
Algorithm time uses `Resource.Event.quantumDuration`; zero preparation and
measurement have zero time under that separate canonical observation.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar

open ClassicalRoutines
noncomputable section

/-- Unit event weight for the original quantum-event accounting identities. -/
public def quantumEventUnitWeight {model : ExecutionModel} : Resource.Event model → Nat
  | .classicalOperation _ => 0
  | .classicalQuery _ => 0
  | .gate _ => 1
  | .oracle _ => 1
  | .preparation _ => 1
  | .measurement _ => 1

private lemma quantum_weight_zero_of_classical {model : ExecutionModel}
    (pool : ResourcePool model)
    (onlyClassical : ∀ event, (∀ label, Resource.Event.classicalOperation label ≠ event) →
      ResourcePool.count event pool = 0) :
    ResourcePool.weightedCount quantumEventUnitWeight pool = 0 := by
  classical
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  by_cases classicalEvent : ∃ label, event = .classicalOperation label
  · obtain ⟨label, rfl⟩ := classicalEvent
    rfl
  · have zero := onlyClassical event (by
      intro label same
      exact classicalEvent ⟨label, same.symm⟩)
    have absent : event ∉ pool := Multiset.count_eq_zero.mp zero
    exact False.elim (absent present)

private lemma sampler_quantum_zero (N : Nat) :
    ResourcePool.weightedCount quantumEventUnitWeight
      (Sampler.Retained.nativeEnvelope (executionModel N) N) = 0 := by
  apply quantum_weight_zero_of_classical
  intro event outside
  exact sampler_nonclassical_zero event outside N

private lemma recovery_quantum_zero (N : Nat) :
    ResourcePool.weightedCount quantumEventUnitWeight
      (FactorRecovery.NativeFactorTail.eventEnvelope (executionModel N) N) = 0 := by
  apply quantum_weight_zero_of_classical
  intro event outside
  exact recovery_nonclassical_zero event outside N

private lemma mul_pred_add_self (width : Nat) :
    width * (width - 1) + width = width ^ 2 := by
  cases width with
  | zero => rfl
  | succ width => simp only [Nat.add_sub_cancel]; ring

/-- The native single-qubit bound expands to the reviewed polynomial. -/
lemma roundSingleQubit_closed (N : Nat) :
    roundSingleQubit N = 6 * (modulusBits N) ^ 2 + 4 * modulusBits N := by
  have pairs := ChooseTwo.twice_choose_two (2 * modulusBits N)
  have square := mul_pred_add_self (2 * modulusBits N)
  unfold roundSingleQubit phaseBits qubits
  nlinarith

/-- Native controlled phases and swaps expand to the reviewed CNOT polynomial. -/
lemma roundCnot_closed (N : Nat) :
    roundCnot N = 4 * (modulusBits N) ^ 2 + modulusBits N := by
  have pairs := ChooseTwo.twice_choose_two (2 * modulusBits N)
  have square := mul_pred_add_self (2 * modulusBits N)
  unfold roundCnot phaseBits
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  nlinarith

/-- The public classical bound covers the original even shortcut and odd recovery uniformly. -/
lemma classicalOperations_closed_le (N count : Nat) :
    classicalOperations N count ≤
      count * (56 * (modulusBits N) ^ 2 + 222 * modulusBits N + 316) + 2 := by
  unfold classicalOperations
  rw [roundClassicalOperations_polynomial]
  split_ifs
  · apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega
  · rfl

/-- The exact complete one-attempt quantum-event count. -/
lemma completion_quantum_event_weight (N : Nat) :
    ResourcePool.weightedCount quantumEventUnitWeight (completionEnvelope N) =
      roundSingleQubit N + roundCnot N + roundMeasurements N + 1 := by
  simp only [completionEnvelope, iterationEnvelope, observationEnvelope,
    NativeFactorScan.visitEnvelope, NativeFactorScan.selectionEnvelope,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    sampler_quantum_zero N, recovery_quantum_zero N]
  simp [DeclaredSource.eventEnvelope, ZReset.Bank.envelope, ZReset.eventEnvelope,
    FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents,
    quantumEventUnitWeight, roundSingleQubit, roundCnot, roundMeasurements,
    qubits, bankQubits_eq_three_mul]
  omega

/-- The first-round event count includes preparation, source sampling, readout and reset. -/
lemma first_quantum_event_weight (N : Nat) :
    ResourcePool.weightedCount quantumEventUnitWeight (Initialized.firstEnvelope N) =
      10 * (modulusBits N) ^ 2 + 13 * modulusBits N + 1 := by
  rw [Initialized.firstEnvelope, ResourcePool.weightedCount_add,
    completion_quantum_event_weight N, roundSingleQubit_closed, roundCnot_closed]
  simp [Initialized.readyEnvelope, quantumEventUnitWeight, bankQubits_eq_three_mul,
    roundMeasurements, phaseBits, qubits]
  ring

/-- With no attempt, only initial quantum preparation contributes to this event count. -/
lemma zero_quantum_event_weight (N : Nat) :
    ResourcePool.weightedCount quantumEventUnitWeight (Machine.eventEnvelope N 0) =
      3 * modulusBits N := by
  simp [Machine.eventEnvelope, Initialized.readyEnvelope, Finite.eventEnvelope,
    ResourcePool.scale, quantumEventUnitWeight, bankQubits_eq_three_mul]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar
