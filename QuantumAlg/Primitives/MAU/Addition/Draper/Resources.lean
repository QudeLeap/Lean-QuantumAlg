/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Draper.Correctness

/-!
# Native resources of the exact compiled-constant Draper adder

Every formula is derived from the same actual no-swap QFT, tensor phase layer,
and inverse QFT used in the correctness proof. Controlled QFT rotations and
uncontrolled constant phases retain their distinct native event coordinates.
The tensor phase layer executes in one parallel step at positive width; the
QFT portions retain their existing structural schedules. These are exact
counts for this construction, including retained zero-angle phases, rather
than optimal-scheduling or approximate-QFT estimates
[D00, paper.tex:302,352-367].
-/

namespace QuantumAlg.MAU.Addition.Draper

noncomputable section

private theorem twice_choose_two (n : Nat) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add, ih]
      cases n with
      | zero => simp
      | succ n =>
          simp only [Nat.succ_sub_one]
          ring

private theorem twice_qft_size (n : Nat) :
    2 * n + 2 * n.choose 2 = n * (n + 1) := by
  rw [twice_choose_two]
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_sub_one]
      ring

/-- The complete native ledger is obtained from the literal QFT/phase/adjoint syntax. -/
theorem draperAddition_eventCost (n constant : Nat) :
    (additionProgram n constant).eventCost =
      (2 * n) • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        (2 * n.choose 2) • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
        n • ResourcePool.singleton
          (.gate (.declared "QuantumAlg.Components.Gate" "phase")) := by
  simp only [additionProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.dagger_eventCost,
    qftNoSwapCircuit_eventCost, draperPhaseLayer_eventCost, two_mul, add_nsmul]
  abel

/-- Both actual Fourier transforms contribute one Hadamard per target wire. -/
theorem draperAddition_hadamard_count (n constant : Nat) :
    ResourcePool.count (.gate (.builtin "hadamard"))
      (additionProgram n constant).eventCost = 2 * n := by
  rw [draperAddition_eventCost]
  simp +decide [qftControlledPhaseLabel]

/-- The two exact QFT portions contribute `n(n-1)` native controlled rotations. -/
theorem draperAddition_controlled_phase_count (n constant : Nat) :
    ResourcePool.count (.gate qftControlledPhaseLabel)
      (additionProgram n constant).eventCost = n * (n - 1) := by
  rw [draperAddition_eventCost]
  simp +decide [qftControlledPhaseLabel, twice_choose_two]

/-- The compiled constant contributes precisely `n` uncontrolled one-qubit phase gates. -/
theorem draperAddition_phase_count (n constant : Nat) :
    ResourcePool.count (.gate (.declared "QuantumAlg.Components.Gate" "phase"))
      (additionProgram n constant).eventCost = n := by
  rw [draperAddition_eventCost]
  simp +decide [qftControlledPhaseLabel]

/-- The bit-reversed Fourier convention avoids any explicit SWAP network. -/
theorem draperAddition_swap_count (n constant : Nat) :
    ResourcePool.count (.gate (.builtin "swap"))
      (additionProgram n constant).eventCost = 0 := by
  rw [draperAddition_eventCost]
  simp +decide [qftControlledPhaseLabel]

/-- The actual event ledger contains `n^2+2n` gates, including at widths zero and one. -/
theorem draperAddition_event_count (n constant : Nat) :
    (additionProgram n constant).eventCost.card = n ^ 2 + 2 * n := by
  rw [draperAddition_eventCost]
  simp only [Multiset.card_add, Multiset.card_nsmul, ResourcePool.singleton,
    Multiset.card_replicate, Nat.mul_one]
  rw [twice_qft_size]
  ring

/-- Exact unit-duration depth of the stored QFT sequences and parallel phase tensor. -/
theorem draperAddition_unit_depth (n constant : Nat) :
    (additionProgram n constant).evaluatedEventDepth (fun _ => 1) =
      n * (n + 1) + (if n = 0 then 0 else 1) := by
  simp only [additionProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_dagger,
    qftNoSwapCircuit_evaluatedEventDepth_of_one, draperPhaseLayer_unit_depth]
  calc
    n + n.choose 2 + ((if n = 0 then 0 else 1) + (n + n.choose 2)) =
      (2 * n + 2 * n.choose 2) + (if n = 0 then 0 else 1) := by omega
    _ = n * (n + 1) + (if n = 0 then 0 else 1) := by rw [twice_qft_size]

/-- All three literal stages share exactly the canonical target interface. -/
@[simp] theorem draperAddition_physical_idx (n constant : Nat) :
    (additionProgram n constant).physical_idx = List.range n := by
  simp only [additionProgram, UnitaryCircuit.seq, UnitaryCircuit.dagger_physical_idx,
    qftNoSwapCircuit_physical_idx, draperPhaseLayer_physical_idx,
    UnitaryCircuit.unionPhysicalIdx_self]

/-- The complete circuit interface contains exactly `n` quantum wires. -/
theorem draperAddition_qubit_count (n constant : Nat) :
    (additionProgram n constant).physical_idx.length = n := by
  rw [draperAddition_physical_idx, List.length_range]

end

end QuantumAlg.MAU.Addition.Draper
