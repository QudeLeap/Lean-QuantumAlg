/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Grouping
public import QuantumAlg.Primitives.Trotter.Circuit.Blocks
public import QuantumAlg.Primitives.Trotter.Circuit.Grouped
import all QuantumAlg.Components.Pauli.FermiHubbard.Grouping
import all QuantumAlg.Components.Pauli.FermiHubbard.Plaquettes
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Primitives.Trotter.Circuit.Blocks
import all QuantumAlg.Primitives.Trotter.Circuit.Grouped
import all QuantumAlg.Primitives.Trotter.Circuit.Cost
import all QuantumAlg.Primitives.Trotter.Circuit.Term

/-!
# Exact native circuits for the original PLAQ blocks

Each complete bond uses its two commuting Pauli rotations. Opposite bonds
give one exact matching; the two complete matchings give one exact plaquette.
Finally disjoint plaquette operators give an exact colour. Every level uses
actual supplied native circuits and proved matrix equalities, with no inner
product-formula approximation or opaque exponential event.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- Native XX/YY implementation of one complete plaquette bond. -/
@[expose] def bondCircuit {L : ℕ} [NeZero L] (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L)
    (d e : Fin 2) (t : ℝ) : Trotter.NativeCircuit (2 * L ^ 2) :=
  Trotter.blockCircuit (plaquetteBondTerms τ c a d e) t

lemma bondCircuit_matrix {L : ℕ} [NeZero L] (hL : Even L) (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) (d e : Fin 2) (t : ℝ) :
    (bondCircuit τ c a d e t).binaryOperator = timeEvolution (plaquetteBond τ c a d e) t := by
  rw [bondCircuit, Trotter.blockCircuit_matrix _ (plaquetteBondTerms_pairwise hL τ c a d e),
    plaquetteBondTerms, hoppingTerms_toHamiltonian]
  rfl

/-- Execute both complete opposite bonds in one matching. -/
@[expose] def matchingCircuit {L : ℕ} [NeZero L] (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L)
    (d : Fin 2) (t : ℝ) : Trotter.NativeCircuit (2 * L ^ 2) :=
  Trotter.blockPass (fun e : Fin 2 => bondCircuit τ c a d e t)

lemma matchingCircuit_matrix {L : ℕ} [NeZero L] (hL : Even L) (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) (d : Fin 2) (t : ℝ) :
    (matchingCircuit τ c a d t).binaryOperator = timeEvolution (matchingHamiltonian τ c a d) t :=
  Trotter.blockPass_matrix_of_pairwise_commute _ _ t
    (fun e => bondCircuit_matrix hL τ c a d e t) (plaquetteBond_pairwise hL τ c a d)

/-- Execute the two exactly commuting complete matchings of one plaquette. -/
@[expose] def plaquetteCircuit {L : ℕ} [NeZero L] (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L)
    (t : ℝ) : Trotter.NativeCircuit (2 * L ^ 2) :=
  Trotter.blockPass (fun d : Fin 2 => matchingCircuit τ c a d t)

lemma plaquetteCircuit_matrix {L : ℕ} [NeZero L] (hL : Even L) (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) (t : ℝ) :
    (plaquetteCircuit τ c a t).binaryOperator = timeEvolution (plaquetteHamiltonian τ c a) t :=
  Trotter.blockPass_matrix_of_pairwise_commute _ _ t
    (fun d => matchingCircuit_matrix hL τ c a d t) (matchingHamiltonian_pairwise hL τ c a)

/-- Execute every complete spin-labelled plaquette of one colour. -/
@[expose] def colourCircuit (L : ℕ) [NeZero L] (τ : ℝ) (c : Fin 2) (t : ℝ) :
    Trotter.NativeCircuit (2 * L ^ 2) :=
  Trotter.blockPass (fun j => plaquetteCircuit τ c (plaquetteAt L j) t)

lemma colourCircuit_matrix {L : ℕ} [NeZero L] (hL : Even L) (τ : ℝ) (c : Fin 2) (t : ℝ) :
    (colourCircuit L τ c t).binaryOperator = timeEvolution (colourHamiltonian L τ c) t :=
  Trotter.blockPass_matrix_of_pairwise_commute _ _ t
    (fun j => plaquetteCircuit_matrix hL τ c (plaquetteAt L j) t)
    (plaquetteHamiltonian_pairwise hL τ c)

/-- Concrete exact factories for the three original outer blocks I, P, G. -/
@[expose] def plaqCircuits (L : ℕ) [NeZero L] (τ u μ : ℝ) (j : Fin 3) (t : ℝ) :
    Trotter.NativeCircuit (2 * L ^ 2) :=
  ![Trotter.blockCircuit (onsite L u μ) t, colourCircuit L τ 0 t, colourCircuit L τ 1 t] j

lemma plaqCircuits_matrix {L : ℕ} [NeZero L] (hL : Even L) (τ u μ : ℝ) (j : Fin 3) (t : ℝ) :
    (plaqCircuits L τ u μ j t).binaryOperator = timeEvolution (plaqFamily L τ u μ j) t := by
  fin_cases j
  · change (Trotter.blockCircuit (onsite L u μ) t).binaryOperator =
      timeEvolution (onsiteHamiltonian L u μ) t
    rw [Trotter.blockCircuit_matrix _ (onsite_terms_pairwise L u μ), onsite_toHamiltonian]
  · exact colourCircuit_matrix hL τ 0 t
  · exact colourCircuit_matrix hL τ 1 t

lemma matchingCircuit_eventCost {L : ℕ} [NeZero L] (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L)
    (d : Fin 2) (t : ℝ) :
    (matchingCircuit τ c a d t).eventCost = Trotter.passPool (matchingTerms τ c a d) := by
  simp only [matchingCircuit, Trotter.blockPass_eventCost, bondCircuit,
    Trotter.blockCircuit_eventCost, ← Trotter.sum_termPool,
    matchingTerms, PauliSum.ofFamily_sum_terms]

lemma plaquetteCircuit_eventCost {L : ℕ} [NeZero L] (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L)
    (t : ℝ) :
    (plaquetteCircuit τ c a t).eventCost = Trotter.passPool (plaquetteTerms τ c a) := by
  simp only [plaquetteCircuit, Trotter.blockPass_eventCost, matchingCircuit_eventCost,
    ← Trotter.sum_termPool, plaquetteTerms, PauliSum.ofFamily_sum_terms]

lemma colourCircuit_eventCost (L : ℕ) [NeZero L] (τ : ℝ) (c : Fin 2) (t : ℝ) :
    (colourCircuit L τ c t).eventCost = Trotter.passPool (colourTerms L τ c) := by
  simp only [colourCircuit, Trotter.blockPass_eventCost, plaquetteCircuit_eventCost,
    ← Trotter.sum_termPool, colourTerms, PauliSum.ofFamily_sum_terms]

lemma plaqCircuits_eventCost (L : ℕ) [NeZero L] (τ u μ : ℝ) (j : Fin 3) (t : ℝ) :
    (plaqCircuits L τ u μ j t).eventCost = Trotter.passPool (plaqGroups L τ u μ j) := by
  fin_cases j
  · exact Trotter.blockCircuit_eventCost _ t
  · exact colourCircuit_eventCost L τ 0 t
  · exact colourCircuit_eventCost L τ 1 t

/-- Actual exact-block execution preserves all terms of the original full model. -/
lemma plaqGroups_passPool {L : ℕ} (hL : Even L) (τ u μ : ℝ) :
    (∑ j : Fin 3, Trotter.passPool (plaqGroups L τ u μ j)) =
      Trotter.passPool (pauliSum L τ u μ) := by
  have hc := colourTerms_sum_terms hL τ Trotter.termPool
  simp only [Fin.sum_univ_two, Trotter.sum_termPool] at hc
  simp only [plaqGroups, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  rw [hc]
  simp only [← Trotter.sum_termPool, pauliSum, PauliSum.pauliSum_terms_add,
    List.map_append, List.sum_append]

end
end QuantumAlg.FermiHubbard
