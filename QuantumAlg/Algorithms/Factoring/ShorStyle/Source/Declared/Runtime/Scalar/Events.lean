/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Cardinality
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.ClassicalCoordinates
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight

/-!
# Width-only scalar counts of the complete declared Shor execution

The same independent machine ledger charges initialization once, every complete
original attempt and the sole terminal pack. Quantum coordinates exclude all
native classical work by proved symbolic envelope laws. Classical capacities
add safe recovery branch bounds without evaluating operands or instruction lists.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar

open ClassicalRoutines

noncomputable section

private lemma classical_weight_le_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bounded := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event model => 1) (s := pool)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one] using bounded

private lemma unit_weight_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount (fun _ => 1) pool = pool.card := by
  simp [ResourcePool.weightedCount, Multiset.map_const']

/-- One complete actual round has a width-only ceiling before any fixed-instance substitution. -/
lemma completion_card_le (N : Nat) :
    (completionEnvelope N).card ≤ roundEvents N := by
  have recovered := recovery_card_le (executionModel N) N
  simp only [completionEnvelope, iterationEnvelope, observationEnvelope,
    DeclaredSource.eventEnvelope, NativeFactorScan.visitEnvelope,
    NativeFactorScan.selectionEnvelope, ZReset.Bank.envelope, ZReset.eventEnvelope,
    Multiset.card_add, Multiset.card_nsmul, ResourcePool.singleton, Multiset.card_replicate,
    Sampler.Retained.samplerRetainedEnvelope_card, FirstAccepted.firstAccepted_nativeEnvelope_card]
  unfold roundEvents roundSingleQubit roundCnot roundMeasurements roundClassicalOperations qubits
  rw [bankQubits_eq_three_mul]
  omega

/-- Every chronological attempt and the genuine terminal encoding count in the complete run. -/
lemma machine_depth_scalar (N : Nat) (count : Nat) :
    ResourcePool.weightedCount (fun _ => 1) (Machine.eventEnvelope N count) ≤
      wholeRunDepth N count := by
  have complete := Nat.mul_le_mul_left count (completion_card_le N)
  rw [unit_weight_card]
  simp only [Machine.eventEnvelope, Initialized.readyEnvelope, Finite.eventEnvelope,
    Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul, ResourcePool.singleton,
    Multiset.card_replicate]
  unfold wholeRunDepth qubits
  rw [bankQubits_eq_three_mul]
  omega

/-- Recovery and original native sampling charge no quantum coordinate. -/
lemma completion_nonclassical_count (N : Nat)
    (event : Resource.Event (executionModel N))
    (outside : ∀ label, Resource.Event.classicalOperation label ≠ event) :
    ResourcePool.count event (completionEnvelope N) =
      ResourcePool.count event
        (DeclaredSource.eventEnvelope (modulusBits N) (phaseBits N) BitWord.model .empty) +
      phaseBits N * ResourcePool.count event
        (ResourcePool.singleton (model := executionModel N) (.measurement (2 : ℕ+))) +
      ResourcePool.count event
        (ZReset.Bank.envelope (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
          (bankQubits N) BitWord.model) := by
  simp only [completionEnvelope, iterationEnvelope, observationEnvelope,
    NativeFactorScan.visitEnvelope, NativeFactorScan.selectionEnvelope,
    ResourcePool.count_add, ResourcePool.count_nsmul,
    sampler_nonclassical_zero event outside, recovery_nonclassical_zero event outside]
  have reverseOutside : ∀ label, event ≠ Resource.Event.classicalOperation label :=
    fun label => Ne.symm (outside label)
  simp_all [FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents,
    ResourcePool.ofList, ResourcePool.singleton, ResourcePool.count, add_assoc]

/-- Classical initialization and final packing add no quantum coordinate to the real finite run. -/
lemma machine_nonclassical_count (N : Nat) (count : Nat)
    (event : Resource.Event (executionModel N))
    (outside : ∀ label, Resource.Event.classicalOperation label ≠ event) :
    ResourcePool.count event (Machine.eventEnvelope N count) =
      bankQubits N * ResourcePool.count event
        (ResourcePool.singleton (model := executionModel N) (.preparation (2 : ℕ+))) +
      count * ResourcePool.count event (completionEnvelope N) := by
  simp only [Machine.eventEnvelope, Initialized.readyEnvelope, Finite.eventEnvelope,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_scale]
  simp [ResourcePool.count_singleton, outside]

/-- Every real selected native gate is bounded by the symbolic full-round scalar. -/
lemma machine_gate_count (N : Nat) (count : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := executionModel N) (.gate coordinate)
        (Machine.eventEnvelope N count) =
      count * (match coordinate with
        | .singleQubit => roundSingleQubit N
        | .cnot => roundCnot N
        | .toffoli => 0) := by
  rw [machine_nonclassical_count N count (.gate coordinate) (by intro label; simp),
    completion_nonclassical_count N (.gate coordinate) (by intro label; simp)]
  cases coordinate <;>
    simp [DeclaredSource.eventEnvelope, ZReset.Bank.envelope, ZReset.eventEnvelope,
      roundSingleQubit, roundCnot, qubits, bankQubits_eq_three_mul]

/-- Every original complete attempt contributes exactly one declared query allowance. -/
lemma machine_query_count (N : Nat) (count : Nat)
    (coordinate : (executionModel N).OracleCoordinate) :
    ResourcePool.count (model := executionModel N) (.oracle coordinate)
        (Machine.eventEnvelope N count) = count := by
  rw [machine_nonclassical_count N count (.oracle coordinate) (by intro label; simp),
    completion_nonclassical_count N (.oracle coordinate) (by intro label; simp)]
  cases coordinate
  simp [DeclaredSource.eventEnvelope, ZReset.Bank.envelope, ZReset.eventEnvelope]

/-- The single real initializer prepares every binary bank system and no other dimension. -/
lemma machine_preparation_count (N : Nat) (count : Nat)
    (dimension : ℕ+) :
    ResourcePool.count (model := executionModel N) (.preparation dimension)
        (Machine.eventEnvelope N count) = if 2 = dimension then qubits N else 0 := by
  rw [machine_nonclassical_count N count (.preparation dimension) (by intro label; simp),
    completion_nonclassical_count N (.preparation dimension) (by intro label; simp)]
  have tagged :
      (Resource.Event.preparation (model := executionModel N) (2 : ℕ+) =
        .preparation dimension) ↔ (2 : ℕ+) = dimension := by
    constructor
    · exact Resource.Event.preparation.inj
    · exact congrArg (Resource.Event.preparation (model := executionModel N))
  simp [DeclaredSource.eventEnvelope, ZReset.Bank.envelope, ZReset.eventEnvelope,
    bankQubits_eq_three_mul, qubits, mul_ite, tagged]

/-- Every actual phase and reset readout is charged at its binary system dimension. -/
lemma machine_measurement_count (N : Nat) (count : Nat)
    (dimension : ℕ+) :
    ResourcePool.count (model := executionModel N) (.measurement dimension)
        (Machine.eventEnvelope N count) =
      if 2 = dimension then count * roundMeasurements N else 0 := by
  rw [machine_nonclassical_count N count (.measurement dimension) (by intro label; simp),
    completion_nonclassical_count N (.measurement dimension) (by intro label; simp)]
  have tagged :
      (Resource.Event.measurement (model := executionModel N) (2 : ℕ+) =
        .measurement dimension) ↔ (2 : ℕ+) = dimension := by
    constructor
    · exact Resource.Event.measurement.inj
    · exact congrArg (Resource.Event.measurement (model := executionModel N))
  simp [DeclaredSource.eventEnvelope, ZReset.Bank.envelope, ZReset.eventEnvelope,
    bankQubits_eq_three_mul, roundMeasurements, qubits, mul_ite, ite_add_ite,
    tagged]

/-- The full real classical ledger includes both actual boundary operations. -/
lemma machine_classical_operations_le (N : Nat) (count : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Machine.eventEnvelope N count) ≤ classicalOperations N count := by
  have sampled := (classical_weight_le_card
    (Sampler.Retained.nativeEnvelope (executionModel N) N)).trans_eq
      (Sampler.Retained.samplerRetainedEnvelope_card (executionModel N) N)
  have recovered := (classical_weight_le_card
    (FactorRecovery.NativeFactorTail.eventEnvelope (executionModel N) N)).trans
      (recovery_card_le (executionModel N) N)
  have selected := (classical_weight_le_card
    (FirstAccepted.nativeEnvelope (executionModel N) (modulusBits N))).trans_eq
      (FirstAccepted.firstAccepted_nativeEnvelope_card (executionModel N) (modulusBits N))
  have roundBound : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (completionEnvelope N) ≤ roundClassicalOperations N := by
    simp only [completionEnvelope, iterationEnvelope, observationEnvelope,
      DeclaredSource.eventEnvelope, NativeFactorScan.visitEnvelope,
      NativeFactorScan.selectionEnvelope, ZReset.Bank.envelope, ZReset.eventEnvelope,
      ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
      ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight]
    unfold roundClassicalOperations
    omega
  have repeated := Nat.mul_le_mul_left count roundBound
  simp only [Machine.eventEnvelope, Initialized.readyEnvelope, Finite.eventEnvelope,
    ResourcePool.scale, ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight]
  unfold classicalOperations
  omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar
