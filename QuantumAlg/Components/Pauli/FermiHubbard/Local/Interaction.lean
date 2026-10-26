/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Pauli.FermiHubbard.ChemicalShift
public import QuantumAlg.Components.Pauli.JordanWigner.LocalAlgebra
import all QuantumAlg.Components.Pauli.FermiHubbard.ChemicalShift
import all QuantumAlg.Components.Pauli.FermiHubbard.Diagonal
import all QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.JordanWigner.LocalAlgebra
import all QuantumAlg.Components.Pauli.JordanWigner.Majoranas
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.String
import Mathlib.Tactic

/-!
# The centered interaction acts locally on Majoranas

The interaction convention is the centered ZZ expression of
[Cam22, main.tex:92]. Only the interaction at the Majorana's physical site
contributes to the commutator. The chemical shift remains in the full model
and is removed separately by the conserved-shift identity.
-/

@[expose] public section

namespace QuantumAlg.FermiHubbard

open JordanWigner

noncomputable section

lemma interactionHamiltonian_coe (L : ℕ) (u : ℝ) :
    (interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))) =
      (u / 4 : ℂ) • ∑ p : Site L,
        ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) := by
  simp only [interactionHamiltonian, interactionTerms, PauliSum.ofFamily_toHamiltonian,
    Hamiltonian.coe_sum, PauliSum.coe_toHamiltonian, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, PauliSum.coe_termHamiltonian,
    Complex.ofReal_div, Complex.ofReal_ofNat, ← Finset.smul_sum]
  congr 1
  exact sum_siteAt (fun p : Site L => ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))))

lemma onsiteZZ_op_square {L : ℕ} (p : Site L) :
    ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) * (onsiteZZ p).op = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp (onsiteZZ p).op.property
  rw [Matrix.star_eq_conjTranspose, (onsiteZZ p).op_isHermitian] at h
  exact h

lemma onsiteZZ_majoranaAt_commute {L : ℕ} (p q : Site L) (hpq : p ≠ q)
    (s a : Fin 2) :
    Commute ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2)))
      (majoranaAt (mode s q, a) : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [onsiteZZ_op]
  apply Commute.mul_left
  · exact modeZ_majoranaAt_commute _ _
      (by intro h; exact hpq ((mode_eq_iff _ _ _ _).mp h).2) a
  · exact modeZ_majoranaAt_commute _ _
      (by intro h; exact hpq ((mode_eq_iff _ _ _ _).mp h).2) a

lemma onsiteZZ_majoranaAt_anticommute {L : ℕ} (p : Site L) (s a : Fin 2) :
    ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) *
        majoranaAt (mode s p, a) =
      -((majoranaAt (mode s p, a) : HilbertOperator (Qubits (2 * L ^ 2))) *
        (onsiteZZ p).op) := by
  rw [onsiteZZ_op]
  fin_cases s
  · have h₀ := modeZ_majoranaAt_anticommute (mode 0 p) a
    have h₁ := modeZ_majoranaAt_commute (mode 1 p) (mode 0 p)
      (mode_ne_of_spin_ne (by decide) p p) a
    change (((modeZ (mode 0 p)).op : HilbertOperator (Qubits (2 * L ^ 2))) *
      (modeZ (mode 1 p)).op) * majoranaAt (mode 0 p, a) =
      -((majoranaAt (mode 0 p, a) : HilbertOperator (Qubits (2 * L ^ 2))) *
        ((modeZ (mode 0 p)).op * (modeZ (mode 1 p)).op))
    rw [mul_assoc, h₁.eq, ← mul_assoc, h₀]
    simp only [neg_mul, mul_assoc]
  · have h₀ := modeZ_majoranaAt_commute (mode 0 p) (mode 1 p)
      (mode_ne_of_spin_ne (by decide) p p) a
    have h₁ := modeZ_majoranaAt_anticommute (mode 1 p) a
    change (((modeZ (mode 0 p)).op : HilbertOperator (Qubits (2 * L ^ 2))) *
      (modeZ (mode 1 p)).op) * majoranaAt (mode 1 p, a) =
      -((majoranaAt (mode 1 p, a) : HilbertOperator (Qubits (2 * L ^ 2))) *
        ((modeZ (mode 0 p)).op * (modeZ (mode 1 p)).op))
    rw [mul_assoc, h₁, mul_neg, ← mul_assoc, h₀.eq]
    simp only [mul_assoc]

lemma onsiteZZ_pair_commute {L : ℕ} (p q : Site L) :
    Commute ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2)))
      ((onsiteZZ q).op : HilbertOperator (Qubits (2 * L ^ 2))) := by
  apply (PauliString.commute_iff_op_commute _ _).mp
  have hpoint (j : Fin (2 * L ^ 2)) :
      ¬PauliLetter.anticommutes (onsiteZZ p j) (onsiteZZ q j) := by
    simp only [onsiteZZ_apply]
    split_ifs <;> decide
  simp [PauliString.Commute, PauliString.anticommutingCount, hpoint]

lemma interactionHamiltonian_commute_onsiteZZ {L : ℕ} (u : ℝ) (p : Site L) :
    Commute (interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2)))
      ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [interactionHamiltonian_coe]
  apply Commute.smul_left
  exact Commute.sum_left _ _ _ (fun q _ => onsiteZZ_pair_commute q p)

/-- Exactly one centered on-site interaction acts on a Majorana. -/
lemma interaction_lie_majoranaAt {L : ℕ} (u : ℝ) (p : Site L) (s a : Fin 2) :
    ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      (majoranaAt (mode s p, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆ =
      (u / 2 : ℂ) •
        (((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) *
          majoranaAt (mode s p, a)) := by
  classical
  rw [interactionHamiltonian_coe]
  simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single p]
  · have h := onsiteZZ_majoranaAt_anticommute p s a
    have h' := congrArg Neg.neg h.symm
    simp only [neg_neg] at h'
    rw [h', sub_neg_eq_add, smul_add]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · intro q _ hqp
    exact sub_eq_zero.mpr (onsiteZZ_majoranaAt_commute q p hqp s a).eq
  · simp

/-- Applying the centered interaction twice gives the scalar square locally. -/
lemma interaction_lie_twice_majoranaAt {L : ℕ} (u : ℝ) (p : Site L) (s a : Fin 2) :
    ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (mode s p, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ =
      ((u / 2 : ℂ) ^ 2) •
        (majoranaAt (mode s p, a) : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [interaction_lie_majoranaAt]
  have hcomm := (interactionHamiltonian_commute_onsiteZZ u p).eq
  have hprod :
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) *
          majoranaAt (mode s p, a)⁆ =
      ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) *
        ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
          (majoranaAt (mode s p, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆ := by
    simp only [Ring.lie_def, mul_sub]
    rw [← mul_assoc, hcomm, mul_assoc, mul_assoc]
  have hscalar (A B : HilbertOperator (Qubits (2 * L ^ 2))) (c : ℂ) :
      ⁅A, c • B⁆ = c • ⁅A, B⁆ := by
    simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [hscalar, hprod, interaction_lie_majoranaAt, mul_smul_comm,
    smul_smul, ← mul_assoc, onsiteZZ_op_square, one_mul]
  congr 1
  ring

/-- The interaction Pauli is the product of its four local Majoranas, up to sign. -/
lemma onsiteZZ_eq_majoranas {L : ℕ} (p : Site L) :
    ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2))) =
      -(((majoranaAt (mode 0 p, 0) : HilbertOperator (Qubits (2 * L ^ 2))) *
          majoranaAt (mode 0 p, 1)) *
        ((majoranaAt (mode 1 p, 0) : HilbertOperator (Qubits (2 * L ^ 2))) *
          majoranaAt (mode 1 p, 1))) := by
  simp only [majoranaAt, Fin.isValue, one_ne_zero, ↓reduceIte]
  rw [majorana_xy_product, majorana_xy_product, smul_mul_assoc, mul_smul_comm,
    smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg, onsiteZZ_op]

end

end QuantumAlg.FermiHubbard
