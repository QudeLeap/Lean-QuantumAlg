/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf

/-!
# Literal arithmetic labels and the unchanged QFT coordinates

Arithmetic budgets contain native X, CNOT and Toffoli labels with their
actual additional controls. The support argument below preserves these
controls; it only observes family and name to distinguish the independent
QFT phase coordinate and literal T coordinate. No synthesis cost is inferred.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

private def arithmeticCoordinate (event : Resource.Event .quantum) : Prop :=
  ∃ label : Resource.GateLabel, event = .gate label ∧ label.family = "builtin" ∧
    (label.name = "x" ∨ label.name = "cnot" ∨ label.name = "toffoli")

private theorem primitive_supported (event : Resource.Event .quantum)
    (present : event ∈ EncodedBit.GateSpec.primitiveAlphabet) : arithmeticCoordinate event := by
  change event ∈ ([.gate (.builtin "x"), .gate (.builtin "cnot"),
    .gate (.builtin "toffoli")] : List (Resource.Event .quantum)) at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact ⟨_, rfl, rfl, Or.inl rfl⟩
  · exact ⟨_, rfl, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨_, rfl, rfl, Or.inr (Or.inr rfl)⟩

private theorem controlled_supported (pool : ResourcePool .quantum)
    (supported : ∀ event ∈ pool, arithmeticCoordinate event)
    (event : Resource.Event .quantum) (present : event ∈ ResourcePool.controlForDimension 2 pool) :
    arithmeticCoordinate event := by
  change event ∈ pool.map (fun source => source.controlForDimension 2) at present
  obtain ⟨source, sourcePresent, rfl⟩ := Multiset.mem_map.mp present
  obtain ⟨label, rfl, family, name⟩ := supported source sourcePresent
  exact ⟨label.controlForDimension 2, rfl, family, name⟩

private theorem offset_supported (event : Resource.Event .quantum)
    (present : event ∈ MAU.Addition.Gidney.offsetAlphabet) : arithmeticCoordinate event := by
  rcases Multiset.mem_add.mp present with primitive | controlled
  · exact primitive_supported event primitive
  · exact controlled_supported _ primitive_supported event controlled

private theorem accumulate_supported (width : Nat) (event : Resource.Event .quantum)
    (present : event ∈ MAU.Multiplication.Accumulate.Gidney.nativeBudget width) :
    arithmeticCoordinate event :=
  controlled_supported _ offset_supported event (Multiset.mem_of_mem_nsmul present)

private theorem unit_supported (width : Nat) (event : Resource.Event .quantum)
    (present : event ∈ MAU.Multiplication.Gidney.nativeBudget width) :
    arithmeticCoordinate event := by
  rcases Multiset.mem_add.mp present with firstTwo | last
  · rcases Multiset.mem_add.mp firstTwo with first | swap
    · exact accumulate_supported width event first
    · change event ∈ List.replicate (3 * width)
        (Resource.Event.gate (.builtin "cnot")) at swap
      have equal := (List.mem_replicate.mp swap).2
      subst event
      exact ⟨_, rfl, rfl, Or.inr (Or.inl rfl)⟩
  · exact accumulate_supported width event last

private theorem exponentiation_supported (bits width : Nat) (event : Resource.Event .quantum)
    (present : event ∈ MAU.Exponentiation.Gidney.nativeBudget bits width) :
    arithmeticCoordinate event :=
  controlled_supported _ (unit_supported width) event (Multiset.mem_of_mem_nsmul present)

private theorem exponentiationEnvelope_supported (bits width N : Nat)
    (event : Resource.Event .quantum)
    (present : event ∈ exponentiationEventEnvelope bits width N) : arithmeticCoordinate event := by
  unfold exponentiationEventEnvelope at present
  split at present
  · exact exponentiation_supported bits width event present
  · exact False.elim (Multiset.notMem_zero event present)

private theorem groupEnvelope_supported (m ell width N : Nat)
    (event : Resource.Event .quantum)
    (present : event ∈ compiledGroupActionEventEnvelope m ell width N) :
    arithmeticCoordinate event := by
  rcases Multiset.mem_add.mp present with first | second
  · exact exponentiationEnvelope_supported (ell + m) width N event first
  · exact exponentiationEnvelope_supported ell width N event second

private theorem group_phase_zero (m ell width N : Nat) :
    ResourcePool.count (.gate qftControlledPhaseLabel)
      (compiledGroupActionEventEnvelope m ell width N) = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro present
  obtain ⟨label, equal, family, _⟩ := groupEnvelope_supported m ell width N _ present
  cases equal
  exact (by decide : "qft" ≠ "builtin") family

private theorem group_t_zero (m ell width N : Nat) :
    ResourcePool.count (.gate (.builtin "t"))
      (compiledGroupActionEventEnvelope m ell width N) = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro present
  obtain ⟨label, equal, _, name⟩ := groupEnvelope_supported m ell width N _ present
  cases equal
  rcases name with x | cnot | toffoli
  · exact (by decide : "t" ≠ "x") x
  · exact (by decide : "t" ≠ "cnot") cnot
  · exact (by decide : "t" ≠ "toffoli") toffoli

/-- Arithmetic has no QFT phase coordinate, so the exact rotation count comes from readout. -/
theorem compiledCircuitEventEnvelope_qftRotation_count_eq (m ell width N : Nat) :
    ResourcePool.count (.gate qftControlledPhaseLabel)
        (compiledCircuitEventEnvelope m ell width N) = qftRotationCount m ell := by
  have preparation : ResourcePool.count (.gate qftControlledPhaseLabel)
      (preparationEventEnvelope m ell) = 0 := by
    simp only [preparationEventEnvelope, ResourcePool.count_add]
    rw [ResourcePool.count_singleton_of_ne (by decide),
      ResourcePool.count_singleton_of_ne (by decide)]
  have qft (bits : Nat) : ResourcePool.count (.gate qftControlledPhaseLabel)
      (qftEventEnvelope bits) = bits * (bits - 1) / 2 := by
    rw [← QFTCircuit_eventCost_eq_envelope]
    exact (QFTCircuit_exact_event_gate_counts bits).2.1
  rw [compiledCircuitEventEnvelope, ResourcePool.count_add, ResourcePool.count_add,
    preparation, group_phase_zero, readoutEventEnvelope, ResourcePool.count_add, qft, qft]
  simp only [Nat.zero_add, qftRotationCount, Nat.add_comm ell m]

/-- There is no literal T event in this unsynthesized native family budget. -/
theorem compiledCircuitEventEnvelope_tGateCount_zero (m ell width N : Nat) :
    ResourcePool.count (.gate (.builtin "t")) (compiledCircuitEventEnvelope m ell width N) = 0 := by
  have preparation : ResourcePool.count (.gate (.builtin "t"))
      (preparationEventEnvelope m ell) = 0 := by
    simp only [preparationEventEnvelope, ResourcePool.count_add]
    rw [ResourcePool.count_singleton_of_ne (by decide),
      ResourcePool.count_singleton_of_ne (by decide)]
  have qft (bits : Nat) : ResourcePool.count (.gate (.builtin "t"))
      (qftEventEnvelope bits) = 0 := by
    rw [← QFTCircuit_eventCost_eq_envelope]
    exact QFTCircuit_event_count_eq_zero_of_ne bits (.builtin "t")
      (by decide) (by decide) (by decide)
  rw [compiledCircuitEventEnvelope, ResourcePool.count_add, ResourcePool.count_add,
    preparation, group_t_zero, readoutEventEnvelope, ResourcePool.count_add, qft, qft]

end

end QuantumAlg.ShortDLP.CompiledMAU
