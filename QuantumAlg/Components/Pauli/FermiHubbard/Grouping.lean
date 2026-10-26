/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Commutation
public import QuantumAlg.Components.Pauli.FermiHubbard.Diagonal
import all QuantumAlg.Components.Pauli.FermiHubbard.Plaquettes
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Core.Base.Hamiltonian

/-!
# The original I, P, G outer grouping

The outer order is on-site interaction, colour zero, colour one. Each colour
is a sum of commuting complete plaquette operators. The Pauli lists of the
colours do not themselves satisfy the stronger termwise commutation property.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- Original on-site, pink and gold Pauli presentations in outer product order. -/
@[expose] def plaqGroups (L : ℕ) (τ u μ : ℝ) : Fin 3 → PauliSum (2 * L ^ 2) :=
  ![onsite L u μ, colourTerms L τ 0, colourTerms L τ 1]

/-- Complete I, P, G Hamiltonians; these three operators need not commute. -/
@[expose] def plaqFamily (L : ℕ) (τ u μ : ℝ) : Fin 3 → Hamiltonian (Qubits (2 * L ^ 2)) :=
  ![onsiteHamiltonian L u μ, colourHamiltonian L τ 0, colourHamiltonian L τ 1]

lemma plaqGroups_toHamiltonian (L : ℕ) (τ u μ : ℝ) (j : Fin 3) :
    (plaqGroups L τ u μ j).toHamiltonian = plaqFamily L τ u μ j := by
  fin_cases j <;> simp [plaqGroups, plaqFamily, onsite_toHamiltonian,
    colourTerms_toHamiltonian]

/-- All three groups sum to the full model, including the chemical shift. -/
lemma plaqFamily_sum {L : ℕ} (hL : Even L) (τ u μ : ℝ) :
    Hamiltonian.sum (plaqFamily L τ u μ) = hamiltonian L τ u μ := by
  have hc := congrArg (fun H : Hamiltonian (Qubits (2 * L ^ 2)) =>
    (H : HilbertOperator (Qubits (2 * L ^ 2)))) (colourHamiltonian_sum hL τ)
  simp only [Hamiltonian.coe_sum, Fin.sum_univ_two] at hc
  apply Hamiltonian.ext
  simp only [plaqFamily, Hamiltonian.coe_sum, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, hamiltonian, Hamiltonian.coe_add]
  rw [hc]

/-- Internal certificates of the original groups: diagonal on-site entries and
complete, disjoint plaquettes in each colour. This is not raw-colour Pauli commutation. -/
lemma groups_commute {L : ℕ} (hL : Even L) (τ u μ : ℝ) :
    (onsite L u μ).terms.Pairwise (fun a b => a.2.Commute b.2) ∧
      ∀ c : Fin 2, ∀ i j : Fin (2 * (L / 2) ^ 2),
        Commute (plaquetteHamiltonian τ c (plaquetteAt L i) :
          HilbertOperator (Qubits (2 * L ^ 2)))
          (plaquetteHamiltonian τ c (plaquetteAt L j) :
            HilbertOperator (Qubits (2 * L ^ 2))) := by
  exact ⟨onsite_terms_pairwise L u μ, fun c => plaquetteHamiltonian_pairwise hL τ c⟩

end
end QuantumAlg.FermiHubbard
