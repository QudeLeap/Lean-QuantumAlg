/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.Circuit.Term
import all QuantumAlg.Primitives.Trotter.Circuit.Term
public import QuantumAlg.Analysis.Trotter.SecondOrder
import all QuantumAlg.Analysis.Trotter.SecondOrder
import all QuantumAlg.Analysis.Trotter.FirstOrder
import all QuantumAlg.Analysis.Trotter.Family
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Ordered product-formula circuits

Execution follows the supplied term list; matrices compose in the opposite
order. The symmetric formula keeps both half-time visits to every term
[CST+21, prelim.tex:30-35]. The repeated error bounds retain their respective
all-real-time and nonnegative-time hypotheses [CST+21, prefactor.tex:45-114].
-/

section

namespace QuantumAlg.Trotter

noncomputable section

/-- Execute a list in its literal order, with no simplification of native leaves. -/
public def ordered {n : ℕ} [NeZero n] : List (NativeCircuit n) → NativeCircuit n
  | [] => UnitaryCircuit.identity AlgorithmGate.model .empty (nativeLayout n)
  | c :: cs => c.seq (ordered cs)

/-- Matrix factors of a literal execution list occur in reverse order. -/
public lemma ordered_matrix {n : ℕ} [NeZero n] (cs : List (NativeCircuit n)) :
    (ordered cs).binaryOperator = (cs.reverse.map NativeCircuit.binaryOperator).prod := by
  induction cs with
  | nil => exact NativeCircuit.binaryOperator_identity n
  | cons c cs ih =>
      rw [ordered, NativeCircuit.binaryOperator_seq]
      simp [ih]

/-- Native pools add once per literal visit. -/
public lemma ordered_eventCost {n : ℕ} [NeZero n] (cs : List (NativeCircuit n)) :
    (ordered cs).eventCost = (cs.map UnitaryCircuit.eventCost).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ordered, ih]

/-- One first-order pass executes the original term order. -/
public def firstStep {n : ℕ} [NeZero n] (H : PauliSum n) (τ : ℝ) : NativeCircuit n :=
  ordered (H.terms.map fun a => termCircuit a τ)

/-- Forward and reverse half-time passes, retaining the two central visits. -/
public def secondStep {n : ℕ} [NeZero n] (H : PauliSum n) (τ : ℝ) : NativeCircuit n :=
  (firstStep H (τ / 2)).seq
    (ordered (H.terms.reverse.map fun a => termCircuit a (τ / 2)))

/-- Exactly `r` first-order passes at time `t / r`; total also at `r = 0`. -/
public def first {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) : NativeCircuit n :=
  UnitaryCircuit.iterate r (firstStep H (t / (r : ℝ)))

/-- Exactly `r` symmetric passes at time `t / r`; total also at `r = 0`. -/
public def second {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) : NativeCircuit n :=
  UnitaryCircuit.iterate r (secondStep H (t / (r : ℝ)))

/-- The first pass realizes the descending-index operator definition. -/
public lemma firstStep_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (τ : ℝ) :
    (firstStep H τ).binaryOperator = firstOrderStep H.family τ := by
  obtain ⟨terms⟩ := H
  induction terms with
  | nil => rw [firstOrderStep_empty]; exact NativeCircuit.binaryOperator_identity n
  | cons a terms ih =>
      rw [firstOrderStep_succ]
      rw [firstStep, List.map_cons, ordered, NativeCircuit.binaryOperator_seq]
      change (firstStep (⟨terms⟩ : PauliSum n) τ).binaryOperator *
        (termCircuit a τ).binaryOperator = _
      rw [ih, termCircuit_matrix]
      rfl

/-- Reverse execution realizes the ascending-index product. -/
public lemma reverseStep_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (τ : ℝ) :
    (ordered (H.terms.reverse.map fun a => termCircuit a τ)).binaryOperator =
      finiteFirstOrderTrotterStep H.family τ := by
  rw [ordered_matrix]
  simp only [← List.map_reverse, List.reverse_reverse, List.map_map,
    Function.comp_def, termCircuit_matrix, finiteFirstOrderTrotterStep, PauliSum.family]
  congr 1
  symm
  simpa only [List.get_eq_getElem] using
    List.ofFn_getElem_eq_map H.terms (fun a => timeEvolution (PauliSum.termHamiltonian a) τ)

/-- Exact Strang matrix order, with both half-time passes present. -/
public lemma secondStep_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (τ : ℝ) :
    (secondStep H τ).binaryOperator = secondOrderStep H.family τ := by
  rw [secondStep, NativeCircuit.binaryOperator_seq]
  rw [reverseStep_matrix, firstStep_matrix]
  rfl

/-- Actual repeated first-order circuit matrix. -/
public lemma first_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) :
    (first H t r).binaryOperator = firstOrderStep H.family (t / (r : ℝ)) ^ r := by
  rw [first, NativeCircuit.binaryOperator_iterate]
  rw [firstStep_matrix]

/-- Actual repeated second-order circuit matrix. -/
public lemma second_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (t : ℝ) (r : ℕ) :
    (second H t r).binaryOperator = secondOrderStep H.family (t / (r : ℝ)) ^ r := by
  rw [second, NativeCircuit.binaryOperator_iterate]
  rw [secondStep_matrix]

/-- First-order repeated commutator error budget. -/
@[expose] public def firstError {n : ℕ} (H : PauliSum n) (t : ℝ) (r : ℕ) : ℝ :=
  (t ^ 2 / (2 * (r : ℝ))) * firstOrderCommutatorSum H.family

/-- Second-order repeated nested-commutator error budget. -/
@[expose] public def secondError {n : ℕ} (H : PauliSum n) (t : ℝ) (r : ℕ) : ℝ :=
  (t ^ 3 / (12 * (r : ℝ) ^ 2)) * secondOrderCommutatorSum H.family

/-- Nonnegative-time symmetric error is an independent nonnegative specification budget. -/
public lemma secondError_nonneg {n : ℕ} (H : PauliSum n) (t : ℝ)
    (ht : 0 ≤ t) (r : ℕ) : 0 ≤ secondError H t r := by
  unfold secondError
  exact mul_nonneg (div_nonneg (pow_nonneg ht _) (by positivity))
    (secondOrderCommutatorSum_nonneg H.family)

/-- Certified first-order simulation for every real time and positive repetition count. -/
@[expose] public def firstRealization {n : ℕ} [NeZero n] (H : PauliSum n)
    (t : ℝ) (r : ℕ) (hr : 0 < r) :
    UnitaryCircuit.ApproxRealization AlgorithmGate.model .empty (nativeLayout n)
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
        (timeEvolution H.toHamiltonian t)) (firstError H t r) :=
  NativeCircuit.approximate (first H t r) _ _ (by
    rw [first_matrix]
    exact firstOrder_repeated_error_bound H.family t r hr)

/-- Certified symmetric simulation for nonnegative time and positive repetition count. -/
@[expose] public def secondRealization {n : ℕ} [NeZero n] (H : PauliSum n)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    UnitaryCircuit.ApproxRealization AlgorithmGate.model .empty (nativeLayout n)
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
        (timeEvolution H.toHamiltonian t)) (secondError H t r) :=
  NativeCircuit.approximate (second H t r) _ _ (by
    rw [second_matrix]
    exact secondOrder_repeated_error_bound H.family t ht r hr)

end
end QuantumAlg.Trotter

end
