/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Diagonal
import all QuantumAlg.Components.Pauli.FermiHubbard.Diagonal
import all QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.JordanWigner.Bilinears
import all QuantumAlg.Components.Pauli.JordanWigner.Ladders
import all QuantumAlg.Core.Base.Hamiltonian

/-!
# The conserved chemical shift

The full on-site operator is the shifted ZZ interaction plus
(u/2−μ)N_total − u L² I/4. The conserved term is kept in the simulated
Hamiltonian; commutator estimates alone can remove it.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- The centered interaction, with one ZZ entry per physical site. -/
@[expose] def interactionTerms (L : ℕ) (u : ℝ) : PauliSum (2 * L ^ 2) :=
  PauliSum.ofFamily (fun j : Fin (L ^ 2) => ⟨[(u / 4, onsiteZZ (siteAt L j))]⟩)

/-- The centered interaction observable. -/
@[expose] def interactionHamiltonian (L : ℕ) (u : ℝ) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  (interactionTerms L u).toHamiltonian

/-- A conserved number contribution and a scalar identity shift. -/
@[expose] def chemicalShift (L : ℕ) (u μ : ℝ) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  Hamiltonian.add
    ((Hamiltonian.instSMulReal (R := Qubits (2 * L ^ 2))).smul (u / 2 - μ)
      (JordanWigner.totalNumber (2 * L ^ 2)))
    (PauliSum.termHamiltonian (-((L ^ 2 : ℕ) : ℝ) * u / 4, identityString L))

lemma chemicalShift_coe (L : ℕ) (u μ : ℝ) :
    (chemicalShift L u μ : HilbertOperator (Qubits (2 * L ^ 2))) =
      ((u / 2 - μ : ℝ) : ℂ) • (JordanWigner.totalNumber (2 * L ^ 2) :
        HilbertOperator (Qubits (2 * L ^ 2))) +
      ((-((L ^ 2 : ℕ) : ℝ) * u / 4 : ℝ) : ℂ) • 1 := by
  simp only [chemicalShift, Hamiltonian.coe_add, PauliSum.coe_termHamiltonian,
    identityString_op, Submonoid.coe_one]
  rfl

/-- Number conservation suffices for commutation with the complete chemical shift. -/
lemma chemicalShift_commute (L : ℕ) (u μ : ℝ)
    (A : Hamiltonian (Qubits (2 * L ^ 2)))
    (hA : Commute (JordanWigner.totalNumber (2 * L ^ 2) :
      HilbertOperator (Qubits (2 * L ^ 2))) (A : HilbertOperator (Qubits (2 * L ^ 2)))) :
    Commute (chemicalShift L u μ : HilbertOperator (Qubits (2 * L ^ 2)))
      (A : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [chemicalShift_coe]
  exact (hA.smul_left _).add_left ((Commute.one_left _).smul_left _)

/-- The spin/site reindexing is complete for the independent number operator. -/
lemma totalNumber_eq_site_sum (L : ℕ) :
    (JordanWigner.totalNumber (2 * L ^ 2) : HilbertOperator (Qubits (2 * L ^ 2))) =
      ∑ p : Site L, ((JordanWigner.number (mode 0 p) :
        HilbertOperator (Qubits (2 * L ^ 2))) +
        (JordanWigner.number (mode 1 p) : HilbertOperator (Qubits (2 * L ^ 2)))) := by
  have h := Equiv.sum_comp (modeEquiv L)
    (fun j => (JordanWigner.number j : HilbertOperator (Qubits (2 * L ^ 2))))
  simpa only [JordanWigner.totalNumber, Hamiltonian.coe_sum, Fintype.sum_prod_type,
    Fin.sum_univ_two, ← Finset.sum_add_distrib, mode] using h.symm

private lemma siteHamiltonian_centered {L : ℕ} (u μ : ℝ) (p : Site L) :
    (siteHamiltonian u μ p : HilbertOperator (Qubits (2 * L ^ 2))) =
      (PauliSum.termHamiltonian (u / 4, onsiteZZ p) : HilbertOperator (Qubits (2 * L ^ 2))) +
      ((u / 2 - μ : ℝ) : ℂ) • ((JordanWigner.number (mode 0 p) :
        HilbertOperator (Qubits (2 * L ^ 2))) +
        (JordanWigner.number (mode 1 p) : HilbertOperator (Qubits (2 * L ^ 2)))) -
      ((u / 4 : ℝ) : ℂ) • 1 := by
  rw [← siteTerms_toHamiltonian, PauliSum.coe_toHamiltonian]
  simp only [siteTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    PauliSum.coe_termHamiltonian, identityString_op, Submonoid.coe_one, JordanWigner.number]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- Centering the interaction changes the full observable by a conserved shift. -/
lemma onsiteHamiltonian_centered (L : ℕ) (u μ : ℝ) :
    onsiteHamiltonian L u μ =
      Hamiltonian.add (interactionHamiltonian L u) (chemicalShift L u μ) := by
  apply Hamiltonian.ext
  have hi : (interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))) =
      ∑ p : Site L, (PauliSum.termHamiltonian (u / 4, onsiteZZ p) :
        HilbertOperator (Qubits (2 * L ^ 2))) := by
    simp only [interactionHamiltonian, interactionTerms, PauliSum.ofFamily_toHamiltonian,
      Hamiltonian.coe_sum, PauliSum.coe_toHamiltonian, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact sum_siteAt (L := L) (fun p =>
      (PauliSum.termHamiltonian (u / 4, onsiteZZ p) : HilbertOperator (Qubits (2 * L ^ 2))))
  simp only [onsiteHamiltonian, Hamiltonian.coe_sum, siteHamiltonian_centered,
    Hamiltonian.coe_add, chemicalShift_coe, hi, totalNumber_eq_site_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_add]
  rw [← smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Nat.cast_pow, Complex.ofReal_pow]
  ring

lemma interactionTerms_oneNorm (L : ℕ) (u : ℝ) :
    (interactionTerms L u).oneNorm = ((L ^ 2 : ℕ) : ℝ) * |u| / 4 := by
  rw [interactionTerms, PauliSum.ofFamily_oneNorm]
  simp [PauliSum.oneNorm, abs_div]
  ring

lemma interactionHamiltonian_opNorm_le (L : ℕ) (u : ℝ) :
    (interactionHamiltonian L u).opNorm ≤ ((L ^ 2 : ℕ) : ℝ) * |u| / 4 := by
  rw [← interactionTerms_oneNorm]
  exact PauliSum.opNorm_toHamiltonian_le_oneNorm (interactionTerms L u)

/-- Total number commutes with every centered on-site ZZ interaction. -/
lemma totalNumber_commute_interaction (L : ℕ) (u : ℝ) :
    Commute (JordanWigner.totalNumber (2 * L ^ 2) : HilbertOperator (Qubits (2 * L ^ 2)))
      (interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))) := by
  simp only [interactionHamiltonian, interactionTerms, PauliSum.ofFamily_toHamiltonian,
    Hamiltonian.coe_sum, PauliSum.coe_toHamiltonian, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  apply Commute.sum_right
  intro j _
  rw [PauliSum.coe_termHamiltonian, onsiteZZ_op]
  have h := (JordanWigner.totalNumber_commute_modeZ (mode 0 (siteAt L j))).mul_right
    (JordanWigner.totalNumber_commute_modeZ (mode 1 (siteAt L j)))
  change _ * (_ • _) = (_ • _) * _
  rw [mul_smul_comm, smul_mul_assoc, h.eq]

end
end QuantumAlg.FermiHubbard
