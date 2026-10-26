/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.JordanWigner.Hopping
import all QuantumAlg.Core.Base.Hamiltonian

/-!
# Periodic Fermi–Hubbard Hamiltonian

The model has one positive horizontal and vertical bond per site and spin,
with hopping coefficient −τ and the full on-site chemical potential. The
Jordan–Wigner correspondence is [WBA11, h2.arxiv2.tex:921-922]. A simple
periodic square lattice requires L ≥ 3; the PLAQ decomposition additionally
uses even L ≥ 4. Outside this domain the list remains a total convention:
L=0 has no terms, L=1 uses the self-string convention, and L=2 repeats each
undirected nearest-neighbour bond. Physical claims below state their domain.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- The two endpoint flavors of one hopping bond, with the negative sign. -/
@[expose] def hoppingTerms {n : ℕ} (τ : ℝ) (p q : Fin n) : PauliSum n :=
  ⟨[(-τ / 2, JordanWigner.hoppingString p q .x),
    (-τ / 2, JordanWigner.hoppingString p q .y)]⟩

/-- A signed complete fermionic hopping bond. -/
@[expose] def bondHamiltonian {n : ℕ} (τ : ℝ) (p q : Fin n) : Hamiltonian (Qubits n) :=
  (Hamiltonian.instSMulReal (R := Qubits n)).smul (-τ) (JordanWigner.hopping p q)

lemma hoppingTerms_toHamiltonian {n : ℕ} (τ : ℝ) (p q : Fin n) :
    (hoppingTerms τ p q).toHamiltonian = bondHamiltonian τ p q := by
  apply Hamiltonian.ext
  rw [PauliSum.coe_toHamiltonian]
  simp only [hoppingTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    PauliSum.coe_termHamiltonian, add_zero, bondHamiltonian, JordanWigner.hopping]
  change _ = ((-τ : ℝ) : ℂ) • ((1 / 2 : ℂ) •
    (((JordanWigner.hoppingString p q .x).op : HilbertOperator (Qubits n)) +
      ((JordanWigner.hoppingString p q .y).op : HilbertOperator (Qubits n))))
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

/-- For distinct modes the Pauli bond has the independent ladder interpretation. -/
lemma bondHamiltonian_eq_fermions {n : ℕ} (τ : ℝ) (p q : Fin n) (hpq : p ≠ q) :
    (bondHamiltonian τ p q : HilbertOperator (Qubits n)) =
      (-τ : ℂ) • (JordanWigner.creation p * JordanWigner.annihilation q +
        JordanWigner.creation q * JordanWigner.annihilation p) := by
  change ((-τ : ℝ) : ℂ) • (JordanWigner.hopping p q : HilbertOperator (Qubits n)) = _
  rw [JordanWigner.hopping_eq_ladders p q hpq, Complex.ofReal_neg]

lemma hoppingTerms_oneNorm {n : ℕ} (τ : ℝ) (p q : Fin n) :
    (hoppingTerms τ p q).oneNorm = |τ| := by
  simp [PauliSum.oneNorm, hoppingTerms, abs_div]

/-- The two outgoing positive-direction bonds at one spin and site. -/
@[expose] def siteHoppingTerms {L : ℕ} (τ : ℝ) (spin : Fin 2) (p : Site L) :
    PauliSum (2 * L ^ 2) :=
  hoppingTerms τ (mode spin p) (mode spin (SquareTorus.right p)) +
    hoppingTerms τ (mode spin p) (mode spin (SquareTorus.down p))

/-- All kinetic terms, ordered by spin and then row-snake site position. -/
@[expose] def kineticTerms (L : ℕ) (τ : ℝ) : PauliSum (2 * L ^ 2) :=
  PauliSum.ofFamily (fun spin : Fin 2 => PauliSum.ofFamily
    (fun j : Fin (L ^ 2) => siteHoppingTerms τ spin (siteAt L j)))

/-- Independent sum of the complete positive-direction fermionic bonds. -/
@[expose] def kineticHamiltonian (L : ℕ) (τ : ℝ) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  Hamiltonian.sum (fun spin : Fin 2 => Hamiltonian.sum (fun p : Site L =>
    Hamiltonian.add
      (bondHamiltonian τ (mode spin p) (mode spin (SquareTorus.right p)))
      (bondHamiltonian τ (mode spin p) (mode spin (SquareTorus.down p)))))

lemma kineticTerms_toHamiltonian (L : ℕ) (τ : ℝ) :
    (kineticTerms L τ).toHamiltonian = kineticHamiltonian L τ := by
  apply Hamiltonian.ext
  simp only [kineticTerms, PauliSum.ofFamily_toHamiltonian, Hamiltonian.coe_sum,
    siteHoppingTerms, PauliSum.toHamiltonian_add, hoppingTerms_toHamiltonian,
    Hamiltonian.coe_add, kineticHamiltonian]
  apply Finset.sum_congr rfl
  intro spin _
  exact sum_siteAt (L := L) (fun p =>
    (bondHamiltonian τ (mode spin p) (mode spin (SquareTorus.right p)) :
      HilbertOperator (Qubits (2 * L ^ 2))) +
    (bondHamiltonian τ (mode spin p) (mode spin (SquareTorus.down p)) :
      HilbertOperator (Qubits (2 * L ^ 2))))

/-- The full ordered Pauli presentation, retaining all identity and zero entries. -/
@[expose] def pauliSum (L : ℕ) (τ u μ : ℝ) : PauliSum (2 * L ^ 2) :=
  onsite L u μ + kineticTerms L τ

/-- The physical Hubbard observable, including −μ times total occupation. -/
@[expose] def hamiltonian (L : ℕ) (τ u μ : ℝ) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  Hamiltonian.add (onsiteHamiltonian L u μ) (kineticHamiltonian L τ)

/-- The explicit Pauli presentation equals the independently defined model. -/
lemma pauliSum_toHamiltonian (L : ℕ) (τ u μ : ℝ) :
    (pauliSum L τ u μ).toHamiltonian = hamiltonian L τ u μ := by
  rw [pauliSum, PauliSum.toHamiltonian_add, onsite_toHamiltonian,
    kineticTerms_toHamiltonian]
  rfl

/-- Periodic horizontal bonds connect distinct modes throughout the physical domain. -/
lemma horizontal_modes_ne {L : ℕ} (hL : 2 ≤ L) (s : Fin 2) (p : Site L) :
    mode s p ≠ mode s (SquareTorus.right p) :=
  mode_ne_of_site_ne s (SquareTorus.right_ne_self hL p).symm

/-- Periodic vertical bonds connect distinct modes throughout the physical domain. -/
lemma vertical_modes_ne {L : ℕ} (hL : 2 ≤ L) (s : Fin 2) (p : Site L) :
    mode s p ≠ mode s (SquareTorus.down p) :=
  mode_ne_of_site_ne s (SquareTorus.down_ne_self hL p).symm

end
end QuantumAlg.FermiHubbard
