/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.Commutant

/-!
# Concrete doubled Clifford basis twirl

This leaf projects one normalized Pauli tensor through the doubled Clifford
twirl and derives its exact one-third Casimir value.
-/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

theorem trace_qubitSwap : Matrix.trace qubitSwap = 2 := by
  have hfixed : ({x : Fin 2 × Fin 2 | x = (x.2, x.1)} : Finset _).card = 2 := by
    decide
  simp [Matrix.trace, qubitSwap, hfixed]

theorem su2_casimir_hsInner_one :
    hsInner su2HermBasis.casimir (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 0 := by
  have hfixed : ({x : Fin 2 × Fin 2 | x = (x.2, x.1)} : Finset _).card = 2 := by
    decide
  simp [hsInner, su2_casimir_eq_swap_sub, qubitSwap, Matrix.trace,
    Matrix.conjTranspose_apply, hfixed]
  norm_num

theorem su2_casimir_hsInner_qubitSwap :
    hsInner su2HermBasis.casimir qubitSwap = 3 := by
  simp [hsInner, su2_casimir_eq_swap_sub, qubitSwap, Matrix.trace,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- The doubled Clifford twirl of one normalized Pauli tensor is one third Casimir. This is the
concrete single-qubit realization of the carrier and one-dimensional Casimir projections in
[RBS+23, `Arxiv_Final.tex:1253-1285`]. The finite-design input is consumed through
`qubitClifford_isDoubledCommutantComplete`. -/
theorem qubitClifford_twirl_basis_zero :
    twirl2 qubitClifford (su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0) =
      (1 / 3 : ℂ) • su2HermBasis.casimir := by
  let X := su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0
  let T := twirl2 qubitClifford X
  have hnormal : T = T (1, 0) (1, 0) • 1 +
      (T (0, 0) (0, 0) - T (1, 0) (1, 0)) • qubitSwap :=
    TwirlInternal.qubitClifford_commutant_normal_form T fun g =>
      twirl2_commute qubitClifford qubitClifford_mul qubitClifford_unitary X g
  have htrace : Matrix.trace T = 0 := by
    change Matrix.trace (twirl2 qubitClifford X) = 0
    rw [twirl2_trace qubitClifford qubitClifford_unitary X]
    change Matrix.trace ((rt2inv • pauliX) ⊗ₖ (rt2inv • pauliX)) = 0
    rw [Matrix.trace_kronecker]
    simp [pauliX, Matrix.trace_fin_two]
  have hproj : hsInner su2HermBasis.casimir T = 1 := by
    have h := twirl2_proj_orth qubitClifford qubitClifford_mul qubitClifford_unitary
      su2HermBasis qubitClifford_casimir_commute (su2HermBasis.B su2i0)
    rw [su2HermBasis.casimir_hsInner_kron (su2HermBasis.herm su2i0),
      su2HermBasis.gPurity_basis_elem] at h
    exact h.symm
  rw [hnormal, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, trace_qubitSwap] at htrace
  norm_num at htrace
  rw [hnormal, hsInner_add_right, hsInner_smul_right, hsInner_smul_right,
    su2_casimir_hsInner_one, su2_casimir_hsInner_qubitSwap] at hproj
  norm_num at hproj
  have hbeta : T (0, 0) (0, 0) - T (1, 0) (1, 0) = (1 / 3 : ℂ) := by
    linear_combination (1 / 3 : ℂ) * hproj
  have halpha : T (1, 0) (1, 0) = (-1 / 6 : ℂ) := by
    linear_combination (1 / 4 : ℂ) * htrace - (1 / 2 : ℂ) * hbeta
  change T = (1 / 3 : ℂ) • su2HermBasis.casimir
  rw [hnormal, su2_casimir_eq_swap_sub, hbeta, halpha]
  module

theorem qubitClifford_twirl_basis_zero_mem_gTensorG :
    twirl2 qubitClifford (su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0) ∈
      gTensorG su2HermBasis := by
  rw [qubitClifford_twirl_basis_zero]
  exact (gTensorG su2HermBasis).smul_mem _ (casimir_mem_gTensorG su2HermBasis)

end QuantumAlg.QubitTwoDesign

end
