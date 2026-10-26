/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.String
public import QuantumAlg.Components.Oracle.TimeEvolution
import all QuantumAlg.Components.Oracle.TimeEvolution
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Indexed groups of Pauli terms

Pauli tensor operators follow [WBA11, h2.arxiv2.tex:310-345]. Blocks retain the
positions of the presented terms, including duplicate strings and zero coefficients. Coverage and
within-block commutation are separate: coverage reconstructs the Hamiltonian,
and commutation gives exact evolution within one block. The exponential uses
the convention of [Lin22, trotter.tex:3]; exact splitting of commuting terms
is illustrated in [Lin22, trotter.tex:58-69].
-/

@[expose] public section

namespace QuantumAlg.PauliSum

variable {n : Nat}

/-- Select original term positions in the supplied order, retaining multiplicity. -/
def groupTerms (H : PauliSum n) (block : List (Fin H.terms.length)) : PauliSum n :=
  ⟨block.map H.terms.get⟩

/-- Every original position occurs exactly once across the blocks. -/
def GroupingValid (H : PauliSum n) (blocks : List (List (Fin H.terms.length))) : Prop :=
  blocks.flatten.Perm (List.finRange H.terms.length)

instance (H : PauliSum n) (blocks : List (List (Fin H.terms.length))) :
    Decidable (H.GroupingValid blocks) :=
  inferInstanceAs (Decidable (blocks.flatten.Perm (List.finRange H.terms.length)))

/-- A caller-supplied grouping certified for positional coverage; empty blocks are allowed. -/
structure Grouping (H : PauliSum n) where
  /-- Ordered blocks of original term positions. -/
  blocks : List (List (Fin H.terms.length))
  /-- The flattened blocks contain every original position exactly once. -/
  valid : H.GroupingValid blocks

/-- The presented Pauli sum selected by each covered block. -/
def groups (H : PauliSum n) (G : H.Grouping) : List (PauliSum n) :=
  G.blocks.map H.groupTerms

/-- Pairwise global Pauli commutation within one index block. -/
def blockCommutes (H : PauliSum n) (block : List (Fin H.terms.length)) : Prop :=
  block.Pairwise fun i j => (H.terms.get i).2.Commute (H.terms.get j).2

instance (H : PauliSum n) (block : List (Fin H.terms.length)) :
    Decidable (H.blockCommutes block) :=
  inferInstanceAs (Decidable (block.Pairwise fun i j =>
    (H.terms.get i).2.Commute (H.terms.get j).2))

/-- Each block commutes internally; no commutation between blocks is required. -/
def GroupsCommute (H : PauliSum n) (G : H.Grouping) : Prop :=
  ∀ block ∈ G.blocks, H.blockCommutes block

instance (H : PauliSum n) (G : H.Grouping) : Decidable (H.GroupsCommute G) :=
  inferInstanceAs (Decidable (∀ block ∈ G.blocks, H.blockCommutes block))

/-- Positional coverage preserves the complete list of terms up to permutation. -/
lemma grouped_terms_perm (H : PauliSum n) (G : H.Grouping) :
    ((H.groups G).map PauliSum.terms).flatten.Perm H.terms := by
  have h := G.valid.map H.terms.get
  simpa only [GroupingValid, groups, groupTerms, List.map_map, Function.comp_def,
    ← List.map_flatten, List.map_get_finRange] using h

private lemma sum_map_flatten {α M : Type*} [AddCommMonoid M]
    (blocks : List (List α)) (f : α → M) :
    (blocks.map fun block => (block.map f).sum).sum = (blocks.flatten.map f).sum := by
  induction blocks with
  | nil => simp
  | cons block blocks ih => simp [ih]

noncomputable section

/-- Coverage alone reconstructs the original Hamiltonian from the group Hamiltonians. -/
lemma sum_groups_toHamiltonian (H : PauliSum n) (G : H.Grouping) :
    ((H.groups G).map fun group =>
      (group.toHamiltonian : HilbertOperator (Qubits n))).sum =
        (H.toHamiltonian : HilbertOperator (Qubits n)) := by
  simp only [coe_toHamiltonian]
  calc
    _ = (((H.groups G).map PauliSum.terms).flatten.map
        fun term => (termHamiltonian term : HilbertOperator (Qubits n))).sum := by
      simpa only [List.map_map, Function.comp_def] using
        sum_map_flatten ((H.groups G).map PauliSum.terms)
          (fun term => (termHamiltonian term : HilbertOperator (Qubits n)))
    _ = _ := ((H.grouped_terms_perm G).map
      (fun term => (termHamiltonian term : HilbertOperator (Qubits n)))).sum_eq

end

/-- The grouping with one block for each presented position. -/
def singletonGrouping (H : PauliSum n) : H.Grouping where
  blocks := (List.finRange H.terms.length).map fun i => [i]
  valid := by
    unfold GroupingValid
    suffices h : ((List.finRange H.terms.length).map fun i => [i]).flatten =
        List.finRange H.terms.length by rw [h]
    generalize List.finRange H.terms.length = indices
    induction indices with
    | nil => rfl
    | cons i indices ih => simpa only [List.map_cons, List.flatten_cons,
        List.singleton_append] using congrArg (List.cons i) ih

/-- Singleton blocks always satisfy the separate internal commutation condition. -/
lemma singletonGrouping_groups_commute (H : PauliSum n) :
    H.GroupsCommute H.singletonGrouping := by
  intro block hblock
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hblock
  simp [blockCommutes]

/-- Internal index commutation is exactly pairwise string commutation in the selected list. -/
lemma blockCommutes_iff_groupTerms_pairwise (H : PauliSum n)
    (block : List (Fin H.terms.length)) :
    H.blockCommutes block ↔
      (H.groupTerms block).terms.Pairwise (fun a b => a.2.Commute b.2) := by
  simp [blockCommutes, groupTerms, List.pairwise_map]

noncomputable section

private lemma termHamiltonian_commute {a b : ℝ × PauliString n}
    (h : a.2.Commute b.2) :
    _root_.Commute (termHamiltonian a : HilbertOperator (Qubits n))
      (termHamiltonian b : HilbertOperator (Qubits n)) := by
  simpa only [coe_termHamiltonian] using
    (((PauliString.commute_iff_op_commute a.2 b.2).mp h).smul_left
      (a.1 : ℂ)).smul_right (b.1 : ℂ)

private lemma timeEvolutionOp_terms (terms : List (ℝ × PauliString n))
    (h : terms.Pairwise fun a b => a.2.Commute b.2) (t : ℝ) :
    timeEvolutionOp
      ((terms.map fun a => (termHamiltonian a : HilbertOperator (Qubits n))).sum) t =
        (terms.map fun a => timeEvolutionOp
          (termHamiltonian a : HilbertOperator (Qubits n)) t).prod := by
  induction terms with
  | nil => simp [timeEvolutionOp]
  | cons a terms ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      have hc : _root_.Commute (termHamiltonian a : HilbertOperator (Qubits n))
          ((terms.map fun b => (termHamiltonian b : HilbertOperator (Qubits n))).sum) := by
        apply _root_.Commute.list_sum_right
        intro B hB
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
        exact termHamiltonian_commute (hhead b hb)
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      change NormedSpace.exp (_ • (_ + _)) = _
      rw [smul_add, Matrix.exp_add_of_commute _ _
        ((hc.smul_left _).smul_right _)]
      exact congrArg (fun U => timeEvolutionOp
        (termHamiltonian a : HilbertOperator (Qubits n)) t * U) (ih htail)

private lemma coe_terms_evolution_prod (terms : List (ℝ × PauliString n)) (t : ℝ) :
    (((terms.map fun a => timeEvolution (termHamiltonian a) t).prod :
        UnitaryOperator (Qubits n)) : HilbertOperator (Qubits n)) =
      (terms.map fun a => timeEvolutionOp
        (termHamiltonian a : HilbertOperator (Qubits n)) t).prod := by
  induction terms with
  | nil => rfl
  | cons a terms ih =>
      change timeEvolutionOp (termHamiltonian a : HilbertOperator (Qubits n)) t * _ =
        timeEvolutionOp (termHamiltonian a : HilbertOperator (Qubits n)) t * _
      exact congrArg (fun U => timeEvolutionOp
        (termHamiltonian a : HilbertOperator (Qubits n)) t * U) ih

/-- Exact ordered evolution for any pairwise commuting presented Pauli sum, for every real time. -/
lemma timeEvolution_eq_terms_prod (H : PauliSum n)
    (h : H.terms.Pairwise fun a b => a.2.Commute b.2) (t : ℝ) :
    timeEvolution H.toHamiltonian t =
      (H.terms.map fun term => timeEvolution (termHamiltonian term) t).prod := by
  apply Subtype.ext
  rw [coe_timeEvolution, coe_terms_evolution_prod, coe_toHamiltonian]
  exact timeEvolutionOp_terms H.terms h t

/-- A single internally commuting block factors exactly, independently of coverage. -/
lemma group_timeEvolution_eq_terms_prod (H : PauliSum n)
    (block : List (Fin H.terms.length)) (h : H.blockCommutes block) (t : ℝ) :
    timeEvolution (H.groupTerms block).toHamiltonian t =
      ((H.groupTerms block).terms.map fun term =>
        timeEvolution (termHamiltonian term) t).prod :=
  (H.groupTerms block).timeEvolution_eq_terms_prod
    ((H.blockCommutes_iff_groupTerms_pairwise block).mp h) t

/-- The grouping commutation certificate supplies exact evolution for any selected block. -/
lemma grouped_timeEvolution_eq_terms_prod (H : PauliSum n) (G : H.Grouping)
    (h : H.GroupsCommute G) (block : List (Fin H.terms.length)) (hblock : block ∈ G.blocks)
    (t : ℝ) :
    timeEvolution (H.groupTerms block).toHamiltonian t =
      ((H.groupTerms block).terms.map fun term =>
        timeEvolution (termHamiltonian term) t).prod :=
  H.group_timeEvolution_eq_terms_prod block (h block hblock) t

end

end QuantumAlg.PauliSum

end
