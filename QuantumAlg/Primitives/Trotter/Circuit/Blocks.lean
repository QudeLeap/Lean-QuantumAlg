/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.Circuit.Ordered
import all QuantumAlg.Primitives.Trotter.Circuit.Ordered
public import QuantumAlg.Analysis.Trotter.Commuting
import all QuantumAlg.Analysis.Trotter.Commuting
import all QuantumAlg.Analysis.Trotter.SecondOrder
import all QuantumAlg.Analysis.Trotter.FirstOrder
import all QuantumAlg.Analysis.Trotter.Family
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization

/-!
# Product formulas from exact supplied block circuits

The supplied finite family fixes the literal circuit visits and their native
labels. Exactness certificates concern complete block Hamiltonians; no
commutation of a block's constituent Pauli strings is required. Symmetric
composition retains both central half-time visits.
-/

section
namespace QuantumAlg.Trotter
noncomputable section

/-- Execute the supplied circuits in increasing index order. -/
public def blockPass {n L : ℕ} [NeZero n] (C : Fin L → NativeCircuit n) :
    NativeCircuit n :=
  ordered (List.ofFn C)

/-- Execute the same supplied circuits in decreasing index order. -/
public def reverseBlockPass {n L : ℕ} [NeZero n] (C : Fin L → NativeCircuit n) :
    NativeCircuit n :=
  ordered (List.ofFn C).reverse

/-- Exact supplied blocks realize the descending-index operator product. -/
public lemma blockPass_matrix {n L : ℕ} [NeZero n] (C : Fin L → NativeCircuit n)
    (H : HamiltonianFamily (Qubits n) L) (τ : ℝ)
    (hC : ∀ j, (C j).binaryOperator = timeEvolution (H j) τ) :
    (blockPass C).binaryOperator = firstOrderStep H τ := by
  unfold blockPass
  induction L with
  | zero => rw [firstOrderStep_empty]; exact NativeCircuit.binaryOperator_identity n
  | succ L ih =>
      rw [List.ofFn_succ, firstOrderStep_succ]
      rw [ordered, NativeCircuit.binaryOperator_seq]
      change (ordered (List.ofFn fun j : Fin L => C j.succ)).binaryOperator *
        (C 0).binaryOperator = _
      rw [ih (fun j => C j.succ) (fun j => H j.succ) (fun j => hC j.succ), hC]

/-- Reverse execution realizes the ascending-index operator product. -/
public lemma reverseBlockPass_matrix {n L : ℕ} [NeZero n]
    (C : Fin L → NativeCircuit n) (H : HamiltonianFamily (Qubits n) L)
    (τ : ℝ) (hC : ∀ j, (C j).binaryOperator = timeEvolution (H j) τ) :
    (reverseBlockPass C).binaryOperator = finiteFirstOrderTrotterStep H τ := by
  simp only [reverseBlockPass, ordered_matrix, List.reverse_reverse, List.map_ofFn,
    Function.comp_def, hC, finiteFirstOrderTrotterStep]

/-- Commuting complete Hamiltonian blocks compose to exact evolution of their sum. -/
public lemma blockPass_matrix_of_pairwise_commute {n L : ℕ} [NeZero n]
    (C : Fin L → NativeCircuit n) (H : HamiltonianFamily (Qubits n) L)
    (τ : ℝ) (hC : ∀ j, (C j).binaryOperator = timeEvolution (H j) τ)
    (hcomm : PairwiseCommute H) :
    (blockPass C).binaryOperator = timeEvolution (Hamiltonian.sum H) τ := by
  rw [blockPass_matrix C H τ hC, firstOrderStep,
    ← timeEvolution_eq_finiteTrotterStep_of_pairwise_commute
      (fun j : Fin L => H j.rev) (fun i j => hcomm i.rev j.rev)]
  congr 1
  apply Hamiltonian.ext
  simp only [Hamiltonian.coe_sum]
  exact Equiv.sum_comp Fin.revPerm (fun j => (H j : HilbertOperator (Qubits n)))

/-- Reverse execution is also exact for commuting complete Hamiltonian blocks. -/
public lemma reverseBlockPass_matrix_of_pairwise_commute {n L : ℕ} [NeZero n]
    (C : Fin L → NativeCircuit n) (H : HamiltonianFamily (Qubits n) L)
    (τ : ℝ) (hC : ∀ j, (C j).binaryOperator = timeEvolution (H j) τ)
    (hcomm : PairwiseCommute H) :
    (reverseBlockPass C).binaryOperator = timeEvolution (Hamiltonian.sum H) τ := by
  rw [reverseBlockPass_matrix C H τ hC,
    ← timeEvolution_eq_finiteTrotterStep_of_pairwise_commute H hcomm]

/-- Forward then reverse half-time passes, preserving every supplied visit. -/
public def secondBlockStep {n L : ℕ} [NeZero n] (C : Fin L → ℝ → NativeCircuit n)
    (τ : ℝ) : NativeCircuit n :=
  (blockPass (fun j => C j (τ / 2))).seq (reverseBlockPass (fun j => C j (τ / 2)))

/-- Exactly `r` symmetric steps of duration `t / r`, including the zero-step circuit. -/
public def secondBlocks {n L : ℕ} [NeZero n] (C : Fin L → ℝ → NativeCircuit n)
    (t : ℝ) (r : ℕ) : NativeCircuit n :=
  UnitaryCircuit.iterate r (secondBlockStep C (t / (r : ℝ)))

/-- The actual symmetric circuit has the symmetric product-formula matrix. -/
public lemma secondBlockStep_matrix {n L : ℕ} [NeZero n]
    (C : Fin L → ℝ → NativeCircuit n) (H : HamiltonianFamily (Qubits n) L)
    (hC : ∀ j s, (C j s).binaryOperator = timeEvolution (H j) s) (τ : ℝ) :
    (secondBlockStep C τ).binaryOperator = secondOrderStep H τ := by
  rw [secondBlockStep, NativeCircuit.binaryOperator_seq]
  rw [reverseBlockPass_matrix _ H _ (fun j => hC j _),
    blockPass_matrix _ H _ (fun j => hC j _)]
  rfl

/-- The actual repeated circuit has the repeated symmetric product matrix. -/
public lemma secondBlocks_matrix {n L : ℕ} [NeZero n]
    (C : Fin L → ℝ → NativeCircuit n) (H : HamiltonianFamily (Qubits n) L)
    (hC : ∀ j s, (C j s).binaryOperator = timeEvolution (H j) s) (t : ℝ) (r : ℕ) :
    (secondBlocks C t r).binaryOperator = secondOrderStep H (t / (r : ℝ)) ^ r := by
  rw [secondBlocks, NativeCircuit.binaryOperator_iterate]
  rw [secondBlockStep_matrix C H hC]

/-- Full-sum approximation by the actual circuit for nonnegative time and positive count. -/
@[expose] public def secondBlocksRealization {n L : ℕ} [NeZero n]
    (C : Fin L → ℝ → NativeCircuit n) (H : HamiltonianFamily (Qubits n) L)
    (hC : ∀ j s, (C j s).binaryOperator = timeEvolution (H j) s)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    UnitaryCircuit.ApproxRealization AlgorithmGate.model .empty (nativeLayout n)
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
        (timeEvolution (Hamiltonian.sum H) t))
      ((t ^ 3 / (12 * (r : ℝ) ^ 2)) * secondOrderCommutatorSum H) :=
  NativeCircuit.approximate (secondBlocks C t r) _ _ (by
    rw [secondBlocks_matrix C H hC]
    exact secondOrder_repeated_error_bound H t ht r hr)

/-- The forward pass emits each circuit's actual native pool once. -/
public lemma blockPass_eventCost {n L : ℕ} [NeZero n] (C : Fin L → NativeCircuit n) :
    (blockPass C).eventCost = ∑ j, (C j).eventCost := by
  simp only [blockPass, ordered_eventCost, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- The reverse pass emits the same actual native pool. -/
public lemma reverseBlockPass_eventCost {n L : ℕ} [NeZero n]
    (C : Fin L → NativeCircuit n) :
    (reverseBlockPass C).eventCost = ∑ j, (C j).eventCost := by
  simp only [reverseBlockPass, ordered_eventCost, List.map_reverse, List.sum_reverse,
    List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- Each symmetric step emits both actual half-time visits without merging. -/
public lemma secondBlockStep_eventCost {n L : ℕ} [NeZero n]
    (C : Fin L → ℝ → NativeCircuit n) (τ : ℝ) :
    (secondBlockStep C τ).eventCost = 2 • ∑ j, (C j (τ / 2)).eventCost := by
  simp only [secondBlockStep, UnitaryCircuit.seq_eventCost, blockPass_eventCost,
    reverseBlockPass_eventCost, two_nsmul]

/-- The repeated event pool is computed at the actual emitted half-step time. -/
public lemma secondBlocks_eventCost {n L : ℕ} [NeZero n]
    (C : Fin L → ℝ → NativeCircuit n) (t : ℝ) (r : ℕ) :
    (secondBlocks C t r).eventCost = r • (2 • ∑ j, (C j (t / (r : ℝ) / 2)).eventCost) := by
  simp only [secondBlocks, UnitaryCircuit.iterate_eventCost, secondBlockStep_eventCost]

/-- A separately supplied constant input pool gives the exact repeated native count. -/
public lemma secondBlocks_eventCost_of_constant {n L : ℕ} [NeZero n]
    (C : Fin L → ℝ → NativeCircuit n)
    (P : Fin L → ResourcePool (.quantum AlgorithmGate.model .empty))
    (hP : ∀ j s, (C j s).eventCost = P j) (t : ℝ) (r : ℕ) :
    (secondBlocks C t r).eventCost = r • (2 • ∑ j, P j) := by
  simp only [secondBlocks_eventCost, hP]

end
end QuantumAlg.Trotter
end
