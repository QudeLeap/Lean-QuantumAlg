/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Pauli.JordanWigner.LocalAlgebra
public import QuantumAlg.Components.Pauli.JordanWigner.Bilinears
public import QuantumAlg.Core.Base.Gate.OperatorNorm
public import Mathlib.Algebra.Lie.OfAssociative
import all QuantumAlg.Components.Pauli.JordanWigner.LocalAlgebra
import all QuantumAlg.Components.Pauli.JordanWigner.Bilinears
import all QuantumAlg.Components.Pauli.JordanWigner.Hopping
import Mathlib.Tactic

/-!
# Hopping along permutations

The algebra retains both orientations of a complete bond. Involutive
permutations describe perfect matchings; coordinate translations describe
periodic hopping. The identities follow from the CAR used in
[WBA11, h2.arxiv2.tex:329-346].
-/

@[expose] public section

namespace QuantumAlg.JordanWigner

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Oriented number-conserving hopping along a permutation of the modes. -/
def permutationBilinear {n : ℕ} (e : Equiv.Perm (Fin n)) : HilbertOperator (Qubits n) :=
  ∑ p, bilinear p (e p)

/-- A complete hopping bond at every starting mode. -/
def permutationHopping {n : ℕ} (e : Equiv.Perm (Fin n)) : HilbertOperator (Qubits n) :=
  ∑ p, (hopping p (e p) : HilbertOperator (Qubits n))

lemma permutationHopping_lie_majoranaAt {n : ℕ} (e : Equiv.Perm (Fin n))
    (he : ∀ p, p ≠ e p) (r : Fin n) (a : Fin 2) :
    ⁅permutationHopping e, (majoranaAt (r, a) : HilbertOperator (Qubits n))⁆ =
      hoppingMajoranaPhase a •
        ((majoranaAt (e r, a.rev) : HilbertOperator (Qubits n)) +
          (majoranaAt (e.symm r, a.rev) : HilbertOperator (Qubits n))) := by
  classical
  change (∑ p, (hopping p (e p) : HilbertOperator (Qubits n))) * _ -
    _ * (∑ p, (hopping p (e p) : HilbertOperator (Qubits n))) = _
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  change (∑ p, ⁅(hopping p (e p) : HilbertOperator (Qubits n)),
    (majoranaAt (r, a) : HilbertOperator (Qubits n))⁆) = _
  simp_rw [hopping_lie_majoranaAt _ _ (he _) r a]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  simp only [← Equiv.eq_symm_apply]
  simp

lemma permutationHopping_eq_bilinears {n : ℕ} (e : Equiv.Perm (Fin n))
    (he : ∀ p, p ≠ e p) :
    permutationHopping e = permutationBilinear e + permutationBilinear e.symm := by
  classical
  simp only [permutationHopping, hopping_eq_ladders _ _ (he _),
    Finset.sum_add_distrib, permutationBilinear, bilinear]
  congr 1
  simpa using (Equiv.sum_comp e (fun p => creation p * annihilation (e.symm p)))

/-- Composition of mode permutations induces the bilinear commutator algebra. -/
lemma permutationBilinear_lie {n : ℕ} (e f : Equiv.Perm (Fin n)) :
    ⁅permutationBilinear e, permutationBilinear f⁆ =
      permutationBilinear (e.trans f) - permutationBilinear (f.trans e) := by
  classical
  unfold permutationBilinear
  rw [sum_lie_sum]
  simp only [Ring.lie_def, bilinear_commutator]
  simp only [Finset.sum_sub_distrib]
  have h₁ (p : Fin n) :
      (∑ q : Fin n, if e p = q then bilinear p (f q) else 0) =
        bilinear p (f (e p)) := by simp [eq_comm]
  have h₂ (p : Fin n) :
      (∑ q : Fin n, if f q = p then bilinear q (e p) else 0) =
        bilinear (f.symm p) (e p) := by
    simp only [← Equiv.eq_symm_apply]
    simp
  simp only [h₁, h₂, Equiv.trans_apply]
  congr 1
  simpa using (Equiv.sum_comp f (fun p => bilinear (f.symm p) (e p))).symm

/-- A complete hopping bond has norm at most one, from its two Pauli flavors. -/
lemma hopping_opNorm_le_one {n : ℕ} (p q : Fin n) :
    HilbertOperator.opNorm (hopping p q : HilbertOperator (Qubits n)) ≤ 1 := by
  change HilbertOperator.opNorm ((1 / 2 : ℂ) •
    (((hoppingString p q .x).op : HilbertOperator (Qubits n)) +
      ((hoppingString p q .y).op : HilbertOperator (Qubits n)))) ≤ 1
  rw [HilbertOperator.opNorm_smul]
  have h := HilbertOperator.opNorm_add_le
    ((hoppingString p q .x).op : HilbertOperator (Qubits n))
    ((hoppingString p q .y).op : HilbertOperator (Qubits n))
  rw [HilbertOperator.opNorm_unitary (R := Qubits n),
    HilbertOperator.opNorm_unitary (R := Qubits n)] at h
  norm_num at ⊢
  linarith

/-- Counting each edge of a perfect matching twice gives the factor one-half. -/
lemma permutationBilinear_opNorm_le {n : ℕ} (e : Equiv.Perm (Fin n))
    (he : ∀ p, p ≠ e p) (hinv : e.symm = e) :
    HilbertOperator.opNorm (permutationBilinear e) ≤ (n : ℝ) / 2 := by
  have heq := permutationHopping_eq_bilinears e he
  rw [hinv] at heq
  have heq' : permutationBilinear e = (1 / 2 : ℂ) • permutationHopping e := by
    rw [heq]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  rw [heq', HilbertOperator.opNorm_smul]
  have h := HilbertOperator.opNorm_sum_le
    (fun p : Fin n => (hopping p (e p) : HilbertOperator (Qubits n)))
  have hs : (∑ p : Fin n, HilbertOperator.opNorm
      (hopping p (e p) : HilbertOperator (Qubits n))) ≤ n := by
    calc
      _ ≤ ∑ _p : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun p _ => hopping_opNorm_le_one p (e p))
      _ = _ := by simp
  change ‖(1 / 2 : ℂ)‖ * HilbertOperator.opNorm
    (∑ p : Fin n, (hopping p (e p) : HilbertOperator (Qubits n))) ≤ _
  norm_num
  linarith

end

end QuantumAlg.JordanWigner
