/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.Circuit.Ordered
import all QuantumAlg.Primitives.Trotter.Circuit.Ordered
import all QuantumAlg.Primitives.Trotter.Circuit.Term
import all QuantumAlg.Primitives.Trotter.PauliRotation.Construction
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf
import all QuantumAlg.Components.Gates.GlobalPhase
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Closed native resources of product formulas

The parity passes and literal basis changes give the native pool
[WBA11, h2.arxiv2.tex:384-412]. Identity terms contribute scalar-phase gates.
The statistics below inspect only the original term list; no rotation synthesis
or finite-basis T-count conversion is asserted.
-/

section
namespace QuantumAlg.Trotter

noncomputable section

/-- Indicator that a Pauli term has nonempty support. -/
@[expose] public def activeTerm {n : ℕ} (a : ℝ × PauliString n) : ℕ :=
  if a.2.support.Nonempty then 1 else 0

/-- Number of original terms with nonempty support. -/
@[expose] public def activeCount {n : ℕ} (H : PauliSum n) : ℕ :=
  (H.terms.map activeTerm).sum

/-- Sum of support weights in the original presentation. -/
@[expose] public def weightSum {n : ℕ} (H : PauliSum n) : ℕ :=
  (H.terms.map fun a => a.2.weight).sum

/-- Sum of occurrences of a specified Pauli letter in the input. -/
@[expose] public def letterSum {n : ℕ} (H : PauliSum n) (p : PauliLetter) : ℕ :=
  (H.terms.map fun a => pauliLetterCount a.2 p).sum

private lemma weight_split {n : ℕ} (a : ℝ × PauliString n) :
    a.2.weight - 1 + activeTerm a = a.2.weight := by
  by_cases h : a.2.support.Nonempty
  · have hw := Finset.card_pos.mpr h
    simp only [activeTerm, if_pos h, PauliString.weight]
    omega
  · simp [activeTerm, PauliString.weight, Finset.not_nonempty_iff_eq_empty.mp h]

/-- The active count is bounded by the number of original positions. -/
public lemma activeCount_le_length {n : ℕ} (H : PauliSum n) :
    activeCount H ≤ H.terms.length := by
  obtain ⟨terms⟩ := H
  induction terms with
  | nil => simp [activeCount]
  | cons a terms ih =>
      have h : activeTerm a ≤ 1 := by unfold activeTerm; split <;> omega
      simp only [activeCount, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

/-- The subtraction in the closed CNOT formula is exact, term by term. -/
public lemma weightSum_sub_activeCount {n : ℕ} (H : PauliSum n) :
    weightSum H - activeCount H = (H.terms.map fun a => a.2.weight - 1).sum := by
  have h : (H.terms.map fun a => a.2.weight - 1).sum + activeCount H = weightSum H := by
    obtain ⟨terms⟩ := H
    induction terms with
    | nil => simp [activeCount, weightSum]
    | cons a terms ih =>
        simp only [activeCount, weightSum, List.map_cons, List.sum_cons] at *
        have ha := weight_split a
        omega
  omega

private lemma identityCount_sum {n : ℕ} (H : PauliSum n) :
    H.terms.length - activeCount H = (H.terms.map fun a => 1 - activeTerm a).sum := by
  have h : (H.terms.map fun a => 1 - activeTerm a).sum + activeCount H = H.terms.length := by
    obtain ⟨terms⟩ := H
    induction terms with
    | nil => simp [activeCount]
    | cons a terms ih =>
        have ha : activeTerm a ≤ 1 := by unfold activeTerm; split <;> omega
        simp only [activeCount, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
  omega

private lemma empty_letterCount {n : ℕ} (P : PauliString n)
    (h : ¬ P.support.Nonempty) (a : PauliLetter) (ha : a ≠ .i) :
    pauliLetterCount P a = 0 := by
  have hs := Finset.not_nonempty_iff_eq_empty.mp h
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have heq : P j = a := (Finset.mem_filter.mp hj).2
  have hm : j ∈ P.support := by simp [PauliString.support, heq, ha]
  simp [hs] at hm

private lemma termPool_closed {n : ℕ} (a : ℝ × PauliString n) :
    termPool a =
      (2 * (a.2.weight - 1)) • {.gate .cnot} +
      activeTerm a • {.gate .singleQubit} +
      (2 * (pauliLetterCount a.2 .x + pauliLetterCount a.2 .y)) •
        {.gate .singleQubit} +
      (4 * pauliLetterCount a.2 .y) • {.gate .singleQubit} +
      (1 - activeTerm a) • {.gate .singleQubit} := by
  by_cases h : a.2.support.Nonempty
  · simp [termPool, activeTerm, h]
  · simp [termPool, activeTerm, PauliString.weight,
      Finset.not_nonempty_iff_eq_empty.mp h,
      empty_letterCount a.2 h .x (by decide), empty_letterCount a.2 h .y (by decide)]

private lemma sum_scaled {α M : Type*} [AddCommMonoid M]
    (as : List α) (f : α → ℕ) (k : ℕ) (v : M) :
    (as.map fun a => (k * f a) • v).sum = (k * (as.map f).sum) • v := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, Nat.mul_add, add_nsmul]

private lemma sum_unscaled {α M : Type*} [AddCommMonoid M]
    (as : List α) (f : α → ℕ) (v : M) :
    (as.map fun a => f a • v).sum = (as.map f).sum • v := by
  simpa using sum_scaled as f 1 v

/-- Closed pool for one original ordered pass. -/
@[expose] public def passPool {n : ℕ} (H : PauliSum n) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (2 * (weightSum H - activeCount H)) • {.gate .cnot} +
  activeCount H • {.gate .singleQubit} +
  (2 * (letterSum H .x + letterSum H .y)) • {.gate .singleQubit} +
  (4 * letterSum H .y) • {.gate .singleQubit} +
  (H.terms.length - activeCount H) • {.gate .singleQubit}

/-- Summing input term pools yields the independent closed formula. -/
public lemma sum_termPool {n : ℕ} (H : PauliSum n) :
    (H.terms.map termPool).sum = passPool H := by
  change (H.terms.map fun a => termPool a).sum = _
  simp only [termPool_closed, List.sum_map_add, sum_scaled, sum_unscaled]
  rw [passPool, weightSum_sub_activeCount, identityCount_sum]
  simp only [activeCount, letterSum]

/-- Closed native pool of one first-order pass. -/
public lemma firstStep_eventCost {n : ℕ} [NeZero n] (H : PauliSum n) (τ : ℝ) :
    (firstStep H τ).eventCost = passPool H := by
  simp only [firstStep, ordered_eventCost, List.map_map, Function.comp_def,
    termCircuit_eventCost, sum_termPool]

/-- Both symmetric half passes retain the same native pool. -/
public lemma secondStep_eventCost {n : ℕ} [NeZero n] (H : PauliSum n) (τ : ℝ) :
    (secondStep H τ).eventCost = 2 • passPool H := by
  simp only [secondStep, UnitaryCircuit.seq_eventCost, firstStep_eventCost,
    ordered_eventCost, List.map_map, Function.comp_def, termCircuit_eventCost,
    List.map_reverse, List.sum_reverse, sum_termPool, two_nsmul]

/-- Closed native pool of all repeated first-order passes. -/
public lemma first_eventCost {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) :
    (first H t r).eventCost = r • passPool H := by
  simp [first, firstStep_eventCost]

/-- Exact closed native counts for the actual repeated symmetric circuit. -/
public lemma second_eventCost {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) :
    (second H t r).eventCost = r • (
      (4 * (weightSum H - activeCount H)) • {.gate .cnot} +
      (2 * activeCount H) • {.gate .singleQubit} +
      (4 * (letterSum H .x + letterSum H .y)) • {.gate .singleQubit} +
      (8 * letterSum H .y) • {.gate .singleQubit} +
      (2 * (H.terms.length - activeCount H)) • {.gate .singleQubit}) := by
  simp only [second, UnitaryCircuit.iterate_eventCost, secondStep_eventCost, passPool,
    nsmul_add, smul_smul]
  have h2 (a : ℕ) : 2 * (2 * a) = 4 * a := by omega
  have h4 (a : ℕ) : 2 * (4 * a) = 8 * a := by omega
  simp only [h2, h4]

/-- Exact CNOT count of the retained two-pass circuit. -/
public lemma second_cnot_count {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (second H t r).eventCost =
      4 * r * (weightSum H - activeCount H) := by
  rw [second_eventCost]
  simp [ResourcePool.count, Nat.mul_assoc, Nat.mul_comm]

/-- Exact default-model single-qubit count, including every identity phase. -/
public lemma second_singleQubit_count {n : ℕ} [NeZero n]
    (H : PauliSum n) (t : ℝ) (r : ℕ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (second H t r).eventCost =
      2 * r * H.terms.length + 4 * r * letterSum H .x + 12 * r * letterSum H .y := by
  rw [second_eventCost]
  suffices h :
      r * (2 * activeCount H + 4 * (letterSum H .x + letterSum H .y) +
        8 * letterSum H .y + 2 * (H.terms.length - activeCount H)) =
        2 * r * H.terms.length + 4 * r * letterSum H .x + 12 * r * letterSum H .y by
    simpa [ResourcePool.count, Nat.mul_add] using h
  have ha := activeCount_le_length H
  have hs : 2 * activeCount H + 4 * (letterSum H .x + letterSum H .y) +
      8 * letterSum H .y + 2 * (H.terms.length - activeCount H) =
        2 * H.terms.length + 4 * letterSum H .x + 12 * letterSum H .y := by omega
  rw [hs]
  ring

/-- Conservative unit-event depth bound from the independent closed native pool. -/
public lemma second_depth_le {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) :
    (second H t r).evaluatedEventDepth (fun _ => 1) ≤
      r * (4 * (weightSum H - activeCount H) + 2 * H.terms.length +
        4 * (letterSum H .x + letterSum H .y) + 8 * letterSum H .y) := by
  have hb := DepthExpr.depthEval_le_costEval
    (fun _ : Resource.Event (.quantum AlgorithmGate.model .empty) => 1) (second H t r).eventDepth
  rw [DepthExpr.costEval_eq_weightedCount] at hb
  change (second H t r).evaluatedEventDepth (fun _ => 1) ≤
    ResourcePool.weightedCount (fun _ => 1) (second H t r).resourcesFromEventDepth at hb
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost, second_eventCost] at hb
  simp only [ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_add] at hb
  simp only [ResourcePool.weightedCount] at hb
  simp only [Multiset.map_singleton, Multiset.sum_singleton, mul_one] at hb
  have ha := activeCount_le_length H
  convert hb using 1
  congr 1
  omega

/-- Error and closed native resources belong to the same actual symmetric circuit. -/
public lemma secondRealization_correct {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ)
    (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    (secondRealization H t ht r hr).circuit = second H t r ∧
    HilbertOperator.opNorm (((second H t r).binaryOperator : HilbertOperator (Qubits n)) -
      (timeEvolution H.toHamiltonian t : HilbertOperator (Qubits n))) ≤ secondError H t r ∧
    (second H t r).eventCost = r • (
      (4 * (weightSum H - activeCount H)) • {.gate .cnot} +
      (2 * activeCount H) • {.gate .singleQubit} +
      (4 * (letterSum H .x + letterSum H .y)) • {.gate .singleQubit} +
      (8 * letterSum H .y) • {.gate .singleQubit} +
      (2 * (H.terms.length - activeCount H)) • {.gate .singleQubit}) :=
  ⟨rfl, by
    rw [second_matrix]
    exact secondOrder_repeated_error_bound H.family t ht r hr, second_eventCost H t r⟩

end
end QuantumAlg.Trotter
end
