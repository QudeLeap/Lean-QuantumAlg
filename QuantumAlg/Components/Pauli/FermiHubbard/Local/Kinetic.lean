/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Pauli.FermiHubbard.Model
public import QuantumAlg.Components.Pauli.JordanWigner.Permutations
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.JordanWigner.Permutations
import all QuantumAlg.Components.Pauli.JordanWigner.LocalAlgebra
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import all QuantumAlg.Util.Lattice.SquareTorus.Edges
import Mathlib.Tactic

/-!
# Four-neighbor kinetic action

Every kinetic commutator with one Majorana contains exactly the four nearest
neighbors, with repetitions retained at small periodic sizes. The operator
is the original signed, spin-preserving hopping sum of
[WBA11, h2.arxiv2.tex:921-922].
-/

@[expose] public section

namespace QuantumAlg.FermiHubbard

open JordanWigner

noncomputable section

/-- Lift a site permutation through the fixed spin-separated encoding. -/
def modePermutation {L : ℕ} (e : Equiv.Perm (Site L)) :
    Equiv.Perm (Fin (2 * L ^ 2)) :=
  (modeEquiv L).symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) e).trans (modeEquiv L))

@[simp] lemma modePermutation_mode {L : ℕ} (e : Equiv.Perm (Site L))
    (s : Fin 2) (p : Site L) :
    modePermutation e (mode s p) = mode s (e p) := by
  simp [modePermutation, mode]

/-- Positive horizontal translation of the physical torus. -/
def horizontalTranslation (L : ℕ) : Equiv.Perm (Site L) :=
  Equiv.prodCongr (Equiv.refl _) (SquareTorus.nextEquiv L)

/-- Positive vertical translation of the physical torus. -/
def verticalTranslation (L : ℕ) : Equiv.Perm (Site L) :=
  Equiv.prodCongr (SquareTorus.nextEquiv L) (Equiv.refl _)

@[simp] lemma horizontalTranslation_apply {L : ℕ} (p : Site L) :
    horizontalTranslation L p = SquareTorus.right p := rfl

@[simp] lemma verticalTranslation_apply {L : ℕ} (p : Site L) :
    verticalTranslation L p = SquareTorus.down p := rfl

lemma modePermutation_ne_of_site_ne {L : ℕ} (e : Equiv.Perm (Site L))
    (he : ∀ p, p ≠ e p) (j : Fin (2 * L ^ 2)) :
    j ≠ modePermutation e j := by
  obtain ⟨⟨s, p⟩, rfl⟩ := (modeEquiv L).surjective j
  change mode s p ≠ modePermutation e (mode s p)
  rw [modePermutation_mode]
  exact mode_ne_of_site_ne s (he p)

lemma sum_site_hopping_eq_permutation {L : ℕ} (e : Equiv.Perm (Site L)) :
    (∑ s : Fin 2, ∑ p : Site L,
      (hopping (mode s p) (mode s (e p)) :
        HilbertOperator (Qubits (2 * L ^ 2)))) =
      permutationHopping (modePermutation e) := by
  rw [permutationHopping, ← (modeEquiv L).sum_comp
    (fun j => (hopping j (modePermutation e j) :
      HilbertOperator (Qubits (2 * L ^ 2))))]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  change (hopping (mode s p) (mode s (e p)) :
    HilbertOperator (Qubits (2 * L ^ 2))) =
      hopping (mode s p) (modePermutation e (mode s p))
  rw [modePermutation_mode]

/-- The two directed translation sums are exactly the original kinetic observable. -/
lemma kineticHamiltonian_eq_translations (L : ℕ) (τ : ℝ) :
    (kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))) =
      (-τ : ℂ) •
        (permutationHopping (modePermutation (horizontalTranslation L)) +
          permutationHopping (modePermutation (verticalTranslation L))) := by
  have hb (p q : Fin (2 * L ^ 2)) :
      (bondHamiltonian τ p q : HilbertOperator (Qubits (2 * L ^ 2))) =
        (-τ : ℂ) • (hopping p q : HilbertOperator (Qubits (2 * L ^ 2))) := by
    change (((-τ : ℝ) : ℂ) • (hopping p q : HilbertOperator (Qubits (2 * L ^ 2)))) = _
    rw [Complex.ofReal_neg]
  simp only [kineticHamiltonian, Hamiltonian.coe_sum, Hamiltonian.coe_add, hb,
    Finset.sum_add_distrib, ← Finset.smul_sum, ← smul_add]
  rw [← sum_site_hopping_eq_permutation (horizontalTranslation L),
    ← sum_site_hopping_eq_permutation (verticalTranslation L)]
  rfl

/-- The four oriented neighboring modes in a fixed order. -/
def kineticNeighbor {L : ℕ} (j : Fin (2 * L ^ 2)) : Fin 4 → Fin (2 * L ^ 2) :=
  ![modePermutation (horizontalTranslation L) j,
    (modePermutation (horizontalTranslation L)).symm j,
    modePermutation (verticalTranslation L) j,
    (modePermutation (verticalTranslation L)).symm j]

/-- Exact four-neighbor adjoint action; no Jordan–Wigner string-length factor occurs. -/
lemma kinetic_lie_majoranaAt {L : ℕ} (hL : 2 ≤ L) (τ : ℝ)
    (j : Fin (2 * L ^ 2)) (a : Fin 2) :
    ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
      (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆ =
      ((-τ : ℂ) * hoppingMajoranaPhase a) •
        ∑ d : Fin 4, (majoranaAt (kineticNeighbor j d, a.rev) :
          HilbertOperator (Qubits (2 * L ^ 2))) := by
  have hh := modePermutation_ne_of_site_ne (horizontalTranslation L)
    (fun p => (SquareTorus.right_ne_self hL p).symm)
  have hv := modePermutation_ne_of_site_ne (verticalTranslation L)
    (fun p => (SquareTorus.down_ne_self hL p).symm)
  rw [kineticHamiltonian_eq_translations]
  have hlin (A B C : HilbertOperator (Qubits (2 * L ^ 2))) (c : ℂ) :
      ⁅c • (A + B), C⁆ = c • (⁅A, C⁆ + ⁅B, C⁆) := by
    simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_add,
      smul_sub]
    abel
  rw [hlin, permutationHopping_lie_majoranaAt _ hh,
    permutationHopping_lie_majoranaAt _ hv, ← smul_add, smul_smul]
  congr 1
  simp [kineticNeighbor, Fin.sum_univ_succ]
  abel

end

end QuantumAlg.FermiHubbard
