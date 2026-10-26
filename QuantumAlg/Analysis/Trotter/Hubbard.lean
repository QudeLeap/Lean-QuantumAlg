/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.Trotter.ThreeBlocks
public import QuantumAlg.Analysis.Trotter.LocalBounds
public import QuantumAlg.Components.Pauli.FermiHubbard.Local.Colours
public import QuantumAlg.Components.Pauli.FermiHubbard.Grouping
public import QuantumAlg.Components.Pauli.FermiHubbard.ChemicalShift
import all QuantumAlg.Components.Pauli.FermiHubbard.Grouping
import all QuantumAlg.Components.Pauli.FermiHubbard.ChemicalShift
import all QuantumAlg.Components.Pauli.FermiHubbard.Plaquettes
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import all QuantumAlg.Core.Base.Hamiltonian

/-!
# Extensive Hubbard PLAQ commutator bounds

The original I, P, G blocks use the weighted nested-commutator sum
[CST+21, prefactor.tex:105-114]. Number conservation removes the chemical
shift from this sum. Four-neighbor Majorana derivatives bound the two
interaction contributions, while complete matching cancellation bounds both
color contributions. The earlier norm-only estimate is retained separately.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- Exact coefficient norm of either colour on an even periodic lattice. -/
lemma colourTerms_oneNorm {L : ℕ} (hL : Even L) (τ : ℝ) (c : Fin 2) :
    (colourTerms L τ c).oneNorm = 2 * ((L ^ 2 : ℕ) : ℝ) * |τ| := by
  rw [colourTerms, PauliSum.ofFamily_oneNorm]
  simp only [plaquetteTerms, matchingTerms, PauliSum.ofFamily_oneNorm,
    plaquetteBondTerms, hoppingTerms_oneNorm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have he : (L : ℝ) = ((L / 2 : ℕ) : ℝ) * 2 := by
    exact_mod_cast (SquareTorus.even_twice_half hL).symm
  rw [he]
  ring

lemma colourHamiltonian_opNorm_le {L : ℕ} (hL : Even L) (τ : ℝ) (c : Fin 2) :
    (colourHamiltonian L τ c).opNorm ≤ 2 * ((L ^ 2 : ℕ) : ℝ) * |τ| := by
  rw [← colourTerms_toHamiltonian, ← colourTerms_oneNorm hL τ c]
  exact PauliSum.opNorm_toHamiltonian_le_oneNorm (colourTerms L τ c)

/-- Coarse bound on the weighted sum S; the evolution error has the additional factor 1/12. -/
@[expose] def coarseCommutatorBound (L : ℕ) (τ u : ℝ) : ℝ :=
  (L : ℝ) ^ 6 * (16 * |u| * |τ| ^ 2 + |u| ^ 2 * |τ| / 2 + 48 * |τ| ^ 3)

lemma coarseCommutatorBound_nonneg (L : ℕ) (τ u : ℝ) :
    0 ≤ coarseCommutatorBound L τ u := by
  unfold coarseCommutatorBound
  positivity

/-- A chemical-potential-independent bound for the actual original PLAQ family. -/
lemma secondOrderCommutatorSum_le_coarseBound {L : ℕ} (hL : Even L) (τ u μ : ℝ) :
    Trotter.secondOrderCommutatorSum (plaqFamily L τ u μ) ≤
      coarseCommutatorBound L τ u := by
  have hI := chemicalShift_commute L u μ (interactionHamiltonian L u)
    (totalNumber_commute_interaction L u)
  have hC (c : Fin 2) := chemicalShift_commute L u μ (colourHamiltonian L τ c)
    (totalNumber_commute_colourHamiltonian hL τ c)
  have h := Trotter.secondOrderCommutatorSum_three_centralShift_le
    (interactionHamiltonian L u) (chemicalShift L u μ)
    (colourHamiltonian L τ 0) (colourHamiltonian L τ 1) hI (hC 0) (hC 1)
    (((L ^ 2 : ℕ) : ℝ) * |u| / 4) (2 * ((L ^ 2 : ℕ) : ℝ) * |τ|)
    (by positivity) (by positivity) (interactionHamiltonian_opNorm_le L u)
    (colourHamiltonian_opNorm_le hL τ 0) (colourHamiltonian_opNorm_le hL τ 1)
  rw [plaqFamily, onsiteHamiltonian_centered]
  simp only [coarseCommutatorBound, Nat.cast_pow] at h ⊢
  convert h using 1 <;> first | rfl | ring

/-- The extensive coefficient multiplying `t³/r²` in the repeated-step error. -/
@[expose] def localErrorCoefficient (L : ℕ) (τ u : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * ((16 / 3 : ℝ) * |u| * |τ| ^ 2 +
    (1 / 6 : ℝ) * |u| ^ 2 * |τ| + |τ| ^ 3)

/-- The weighted commutator sum has twelve times the error coefficient. -/
@[expose] def commutatorBound (L : ℕ) (τ u : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (64 * |u| * |τ| ^ 2 + 2 * |u| ^ 2 * |τ| + 12 * |τ| ^ 3)

lemma commutatorBound_nonneg (L : ℕ) (τ u : ℝ) : 0 ≤ commutatorBound L τ u := by
  unfold commutatorBound
  positivity

lemma localErrorCoefficient_nonneg (L : ℕ) (τ u : ℝ) :
    0 ≤ localErrorCoefficient L τ u := by
  unfold localErrorCoefficient
  positivity

lemma commutatorBound_eq_twelve_localErrorCoefficient (L : ℕ) (τ u : ℝ) :
    commutatorBound L τ u = 12 * localErrorCoefficient L τ u := by
  unfold commutatorBound localErrorCoefficient
  ring

/-- An explicit local bound for the original full I/P/G family on the physical torus. -/
public theorem secondOrderCommutatorSum_le_W {L : ℕ} (hL : Even L) (hsize : 4 ≤ L)
    (τ u μ : ℝ) :
    Trotter.secondOrderCommutatorSum (plaqFamily L τ u μ) ≤ commutatorBound L τ u := by
  have hI := chemicalShift_commute L u μ (interactionHamiltonian L u)
    (totalNumber_commute_interaction L u)
  have hC (c : Fin 2) := chemicalShift_commute L u μ (colourHamiltonian L τ c)
    (totalNumber_commute_colourHamiltonian hL τ c)
  have hkinetic :
      (colourHamiltonian L τ 0 : HilbertOperator (Qubits (2 * L ^ 2))) +
        (colourHamiltonian L τ 1 : HilbertOperator (Qubits (2 * L ^ 2))) =
      (kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))) := by
    have h := congrArg (fun H : Hamiltonian (Qubits (2 * L ^ 2)) =>
      (H : HilbertOperator (Qubits (2 * L ^ 2)))) (colourHamiltonian_sum hL τ)
    simpa only [Hamiltonian.coe_sum, Fin.sum_univ_two] using h
  have hKI := kinetic_interaction_second_bound (by omega : 2 ≤ L) τ u
  have hIK := interaction_kinetic_second_bound (by omega : 2 ≤ L) τ u
  have hGP := colour_nested_opNorm_le hL τ 0 1
  have hPG := colour_nested_opNorm_le hL τ 1 0
  have hcentral := Trotter.secondOrderCommutatorSum_three_centralShift
    (interactionHamiltonian L u) (chemicalShift L u μ)
    (colourHamiltonian L τ 0) (colourHamiltonian L τ 1) hI (hC 0) (hC 1)
  change Trotter.secondOrderCommutatorSum
    ![Hamiltonian.add (interactionHamiltonian L u) (chemicalShift L u μ),
      colourHamiltonian L τ 0, colourHamiltonian L τ 1] =
    Trotter.secondOrderCommutatorSum
      ![interactionHamiltonian L u, colourHamiltonian L τ 0,
        colourHamiltonian L τ 1] at hcentral
  rw [plaqFamily, onsiteHamiltonian_centered]
  rw [hcentral, Trotter.secondOrderCommutatorSum_three, hkinetic]
  unfold commutatorBound
  nlinarith only [hKI, hIK, hGP, hPG]

/-- Exact `8×8`, `u=4` coefficient for unit-magnitude hopping. -/
lemma localErrorCoefficient_eight_four (τ : ℝ) (hτ : |τ| = 1) :
    localErrorCoefficient 8 τ 4 = 1600 := by
  norm_num [localErrorCoefficient, hτ]

/-- Exact `8×8`, `u=8` coefficient for unit-magnitude hopping. -/
lemma localErrorCoefficient_eight_eight (τ : ℝ) (hτ : |τ| = 1) :
    localErrorCoefficient 8 τ 8 = (10432 / 3 : ℝ) := by
  norm_num [localErrorCoefficient, hτ]

lemma trotterSecondError_bound_eq_local (L : ℕ) (τ u t : ℝ) (r : ℕ) :
    (t ^ 3 / (12 * (r : ℝ) ^ 2)) * commutatorBound L τ u =
      (t ^ 3 / (r : ℝ) ^ 2) * localErrorCoefficient L τ u := by
  rw [commutatorBound_eq_twelve_localErrorCoefficient]
  by_cases hr : r = 0
  · subst r
    simp
  · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    field_simp

/-- Repeated-step error of the original three-block family. -/
@[expose] def trotterSecondError (L : ℕ) (τ u μ t : ℝ) (r : ℕ) : ℝ :=
  (t ^ 3 / (12 * (r : ℝ) ^ 2)) * Trotter.secondOrderCommutatorSum (plaqFamily L τ u μ)

/-- The displayed W bound controls the same grouped error, with no shift dependence. -/
lemma trotterSecondError_le {L : ℕ} (hL : Even L) (hsize : 4 ≤ L) (τ u μ t : ℝ)
    (ht : 0 ≤ t) (r : ℕ) :
    trotterSecondError L τ u μ t r ≤ (t ^ 3 / (12 * (r : ℝ) ^ 2)) *
      commutatorBound L τ u := by
  exact mul_le_mul_of_nonneg_left (secondOrderCommutatorSum_le_W hL hsize τ u μ)
    (by positivity)

end
end QuantumAlg.FermiHubbard
