/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.Circuit.Cost
import all QuantumAlg.Primitives.Trotter.Circuit.Cost
import all QuantumAlg.Primitives.Trotter.Circuit.Ordered
import all QuantumAlg.Primitives.Trotter.Circuit.Term
import all QuantumAlg.Components.Pauli.Groups
import all QuantumAlg.Analysis.Trotter.SecondOrder
import all QuantumAlg.Analysis.Trotter.FirstOrder
import all QuantumAlg.Analysis.Trotter.Family
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Symmetric formulas over covered commuting blocks

Coverage preserves the complete Hamiltonian and every native visit. Internal
commutation alone certifies exact block evolution [Lin22, trotter.tex:58-69].
The symmetric error is evaluated on the block Hamiltonians themselves
[CST+21, prefactor.tex:105-114]; distinct blocks need not commute.
-/

section
namespace QuantumAlg.Trotter
noncomputable section

/-- The Hamiltonian family of the covered blocks, in the supplied block order. -/
@[expose] public def groupedFamily {n : ℕ} (H : PauliSum n) (G : H.Grouping)
    (j : Fin (H.groups G).length) : Hamiltonian (Qubits n) :=
  ((H.groups G).get j).toHamiltonian

/-- Coverage alone reconstructs the complete original Hamiltonian. -/
public lemma groupedFamily_sum {n : ℕ} (H : PauliSum n) (G : H.Grouping) :
    Hamiltonian.sum (groupedFamily H G) = H.toHamiltonian := by
  apply Hamiltonian.ext
  change (∑ j : Fin (H.groups G).length,
    (((H.groups G).get j).toHamiltonian : HilbertOperator (Qubits n))) = _
  rw [← List.sum_ofFn]
  have h := List.ofFn_getElem_eq_map (H.groups G)
    (fun K => (K.toHamiltonian : HilbertOperator (Qubits n)))
  simp only [List.get_eq_getElem] at *
  rw [h]
  exact H.sum_groups_toHamiltonian G

/-- Reverse term execution gives each block's ascending ordered product. -/
public def blockCircuit {n : ℕ} [NeZero n] (K : PauliSum n) (τ : ℝ) : NativeCircuit n :=
  ordered (K.terms.reverse.map fun a => termCircuit a τ)

/-- A block circuit is exact under its own internal commutation certificate. -/
public lemma blockCircuit_matrix {n : ℕ} [NeZero n] (K : PauliSum n)
    (h : K.terms.Pairwise fun a b => a.2.Commute b.2) (τ : ℝ) :
    (blockCircuit K τ).binaryOperator = timeEvolution K.toHamiltonian τ := by
  rw [K.timeEvolution_eq_terms_prod h, blockCircuit, ordered_matrix]
  simp only [← List.map_reverse, List.reverse_reverse, List.map_map,
    Function.comp_def, termCircuit_matrix]

private lemma covered_block_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (h : H.GroupsCommute G) (τ : ℝ) (K : PauliSum n) (hK : K ∈ H.groups G) :
    (blockCircuit K τ).binaryOperator = timeEvolution K.toHamiltonian τ := by
  obtain ⟨block, hb, rfl⟩ := List.mem_map.mp hK
  exact blockCircuit_matrix _ ((H.blockCommutes_iff_groupTerms_pairwise block).mp
    (h block hb)) τ

private lemma ordered_ofFn_matrix {n L : ℕ} [NeZero n] (C : Fin L → NativeCircuit n)
    (K : HamiltonianFamily (Qubits n) L) (τ : ℝ)
    (h : ∀ j, (C j).binaryOperator = timeEvolution (K j) τ) :
    (ordered (List.ofFn C)).binaryOperator = firstOrderStep K τ := by
  induction L with
  | zero => rw [firstOrderStep_empty]; exact NativeCircuit.binaryOperator_identity n
  | succ L ih =>
      rw [List.ofFn_succ, firstOrderStep_succ]
      rw [ordered, NativeCircuit.binaryOperator_seq]
      change (ordered (List.ofFn fun j : Fin L => C j.succ)).binaryOperator *
        (C 0).binaryOperator = _
      rw [ih (fun j => C j.succ) (fun j => K j.succ) (fun j => h j.succ), h]

private lemma grouped_pass_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (h : H.GroupsCommute G) (τ : ℝ) :
    (ordered ((H.groups G).map fun K => blockCircuit K τ)).binaryOperator =
      firstOrderStep (groupedFamily H G) τ := by
  have hf := List.ofFn_getElem_eq_map (H.groups G) (fun K => blockCircuit K τ)
  rw [← hf]
  exact ordered_ofFn_matrix _ _ _ fun j =>
    covered_block_matrix H G h τ _ (List.get_mem _ j)

private lemma grouped_reverse_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (h : H.GroupsCommute G) (τ : ℝ) :
    (ordered ((H.groups G).reverse.map fun K => blockCircuit K τ)).binaryOperator =
      finiteFirstOrderTrotterStep (groupedFamily H G) τ := by
  rw [ordered_matrix]
  simp only [← List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def]
  have hm : ((H.groups G).map fun K => (blockCircuit K τ).binaryOperator) =
      ((H.groups G).map fun K => timeEvolution K.toHamiltonian τ) :=
    List.map_congr_left fun K hK => covered_block_matrix H G h τ K hK
  rw [hm]
  unfold finiteFirstOrderTrotterStep groupedFamily
  congr 1
  symm
  exact List.ofFn_getElem_eq_map (H.groups G) (fun K => timeEvolution K.toHamiltonian τ)

/-- Forward and reverse half passes over exact internally commuting blocks. -/
public def secondGroupedStep {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping) (τ : ℝ) :
    NativeCircuit n :=
  (ordered ((H.groups G).map fun K => blockCircuit K (τ / 2))).seq
    (ordered ((H.groups G).reverse.map fun K => blockCircuit K (τ / 2)))

/-- Exactly `r` block-Strang steps, with a total zero-iteration circuit. -/
public def secondGrouped {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping) (t : ℝ) (r : ℕ) :
    NativeCircuit n :=
  UnitaryCircuit.iterate r (secondGroupedStep H G (t / (r : ℝ)))

/-- The actual block circuit realizes the symmetric operator of the grouped family. -/
public lemma secondGroupedStep_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (h : H.GroupsCommute G) (τ : ℝ) :
    (secondGroupedStep H G τ).binaryOperator = secondOrderStep (groupedFamily H G) τ := by
  rw [secondGroupedStep, NativeCircuit.binaryOperator_seq]
  rw [grouped_reverse_matrix H G h, grouped_pass_matrix H G h]
  rfl

/-- Repeated grouped circuit matrix under the internal commutation certificate. -/
public lemma secondGrouped_matrix {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (h : H.GroupsCommute G) (t : ℝ) (r : ℕ) :
    (secondGrouped H G t r).binaryOperator =
      secondOrderStep (groupedFamily H G) (t / (r : ℝ)) ^ r := by
  rw [secondGrouped, NativeCircuit.binaryOperator_iterate]
  rw [secondGroupedStep_matrix H G h]

/-- Error budget evaluated on grouped Hamiltonians, not on the original term family. -/
@[expose] public def secondGroupedError {n : ℕ} (H : PauliSum n) (G : H.Grouping)
    (t : ℝ) (r : ℕ) : ℝ :=
  (t ^ 3 / (12 * (r : ℝ) ^ 2)) * secondOrderCommutatorSum (groupedFamily H G)

/-- Grouped symmetric simulation requires coverage and internal block commutation. -/
@[expose] public def secondGroupedRealization {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (h : H.GroupsCommute G) (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    UnitaryCircuit.ApproxRealization AlgorithmGate.model .empty (nativeLayout n)
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
        (timeEvolution H.toHamiltonian t))
      (secondGroupedError H G t r) :=
  NativeCircuit.approximate (secondGrouped H G t r) _ _ (by
    rw [secondGrouped_matrix H G h, ← groupedFamily_sum H G]
    exact secondOrder_repeated_error_bound (groupedFamily H G) t ht r hr)

/-- Reversing a block's term order does not alter its native pool. -/
public lemma blockCircuit_eventCost {n : ℕ} [NeZero n] (K : PauliSum n) (τ : ℝ) :
    (blockCircuit K τ).eventCost = passPool K := by
  simp only [blockCircuit, ordered_eventCost, List.map_map, Function.comp_def,
    termCircuit_eventCost, List.map_reverse, List.sum_reverse, sum_termPool]

/-- Covered blocks preserve the complete input-only native pool. -/
public lemma grouped_passPool {n : ℕ} (H : PauliSum n) (G : H.Grouping) :
    ((H.groups G).map passPool).sum = passPool H := by
  calc
    _ = ((((H.groups G).map PauliSum.terms).flatten).map termPool).sum := by
      generalize H.groups G = Ks
      induction Ks with
      | nil => simp
      | cons K Ks ih => simp [← sum_termPool, ih]
    _ = (H.terms.map termPool).sum := ((H.grouped_terms_perm G).map termPool).sum_eq
    _ = passPool H := sum_termPool H

/-- Grouping preserves the literal native pool of the repeated symmetric circuit. -/
public lemma secondGrouped_eventCost_eq {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (t : ℝ) (r : ℕ) :
    (secondGrouped H G t r).eventCost = (second H t r).eventCost := by
  simp only [secondGrouped, second, UnitaryCircuit.iterate_eventCost,
    secondStep_eventCost, secondGroupedStep, UnitaryCircuit.seq_eventCost,
    ordered_eventCost, List.map_map, Function.comp_def, blockCircuit_eventCost,
    List.map_reverse, List.sum_reverse, grouped_passPool, two_nsmul]

/-- The same global closed native multiset holds for every covered grouping. -/
public lemma secondGrouped_eventCost {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (t : ℝ) (r : ℕ) :
    (secondGrouped H G t r).eventCost = r • (
      (4 * (weightSum H - activeCount H)) • {.gate .cnot} +
      (2 * activeCount H) • {.gate .singleQubit} +
      (4 * (letterSum H .x + letterSum H .y)) • {.gate .singleQubit} +
      (8 * letterSum H .y) • {.gate .singleQubit} +
      (2 * (H.terms.length - activeCount H)) • {.gate .singleQubit}) := by
  rw [secondGrouped_eventCost_eq, second_eventCost]

/-- Conservative unit-event depth ceiling also holds for empty blocks. -/
public lemma secondGrouped_depth_le {n : ℕ} [NeZero n] (H : PauliSum n) (G : H.Grouping)
    (t : ℝ) (r : ℕ) :
    (secondGrouped H G t r).evaluatedEventDepth (fun _ => 1) ≤
      r * (4 * (weightSum H - activeCount H) + 2 * H.terms.length +
        4 * (letterSum H .x + letterSum H .y) + 8 * letterSum H .y) := by
  have hb := DepthExpr.depthEval_le_costEval
    (fun _ : Resource.Event (.quantum AlgorithmGate.model .empty) => 1)
      (secondGrouped H G t r).eventDepth
  rw [DepthExpr.costEval_eq_weightedCount] at hb
  change (secondGrouped H G t r).evaluatedEventDepth (fun _ => 1) ≤
    ResourcePool.weightedCount (fun _ => 1)
      (secondGrouped H G t r).resourcesFromEventDepth at hb
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost, secondGrouped_eventCost] at hb
  simp only [ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_add] at hb
  simp only [ResourcePool.weightedCount] at hb
  simp only [Multiset.map_singleton, Multiset.sum_singleton, mul_one] at hb
  have ha := activeCount_le_length H
  convert hb using 1
  congr 1
  omega

end
end QuantumAlg.Trotter
end
