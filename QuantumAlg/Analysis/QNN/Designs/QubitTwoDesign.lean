/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.QNN.Algebras.SimpleDLA
public import QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.FirstMoment
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.BasisTwirl
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.Commutant
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.FirstMoment
import all QuantumAlg.Analysis.QNN.Interface.DoubledTwirl
import all QuantumAlg.Analysis.QNN.Algebras.SimpleDLA
import Mathlib.Algebra.Quaternion

/-!
# Single-qubit Clifford two-design

This public owner contains the doubled-twirl endpoint, its nondegenerate and
mixed-state witnesses, and the central-double-cover cardinality results. The
strict binary-octahedral and commutant construction lives in the Core leaf.
-/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

/-- The concrete single-qubit Clifford second moment for the normalized first Pauli basis element.
The `48` strict lifts reduce to `24` projective gates, their doubled twirl is derived independently
from finite-group commutation, trace preservation, Casimir fixing, and doubled-commutant
completeness, and the result instantiates Ragone's second-moment carrier/Casimir projection
[RBS+23, `Arxiv_Final.tex:1253-1285`; Web15, `Cliffords_are_a_3-design.tex:616-619`]. -/
public noncomputable def main : RagoneSecondMoment su2HermBasis
    (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) :=
  RagoneSecondMoment.ofTwoDesign su2HermBasis qubitClifford qubitClifford_mul
    qubitClifford_unitary (su2HermBasis.herm su2i0) (su2HermBasis.herm su2i0)
    su2HermBasis_schur qubitClifford_casimir_commute qubitClifford_isDoubledCommutantComplete
    qubitClifford_twirl_basis_zero_mem_gTensorG

/-- **Fully unconditional `su(2)` barren-plateau second moment.** Assembling the `SimpleSU`
reduction on the genuine second moment `main`, the `su(2)` loss second moment equals `1/3` — where
the finite twirl input is discharged by `qubitClifford_isDoubledCommutantComplete`, the Schur
identity is discharged by `su2HermBasis_schur` (H2), and there is **no** deferred hypothesis and
**no** hand-set `consistencyWitness`. The first-moment lemmas above identify the same expression
with centered loss
variance for traceless observables. -/
theorem main_variance_eq_third : (main.variance : ℂ) = 1 / 3 := by
  rw [SimpleSU.main main
      (su2HermBasis.herm su2i0) (su2HermBasis.herm su2i0) (d := 2) rfl
      su2HermBasis_dim_pos, su2HermBasis.gPurity_basis_elem su2i0]
  norm_num

theorem su2BasisZero_trace_eq_zero : (su2HermBasis.B su2i0).trace = 0 := by
  change Matrix.trace (rt2inv • pauliX) = 0
  rw [Matrix.trace_smul]
  simp [pauliX, Matrix.trace_fin_two]

theorem main_centeredLoss_eq_uncenteredLoss :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ *
            ∑ h, cliffordLoss (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) g) ^ 2 :=
  cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) su2BasisZero_trace_eq_zero

/-- A nondegenerate single-qubit `su(2)` Hermitian witness operator: a strict contraction of the
first normalized Pauli basis element. -/
noncomputable def su2NondegenerateRho : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • su2HermBasis.B su2i0

/-- A nondegenerate single-qubit `su(2)` witness observable, scaled differently from
`su2NondegenerateRho`. -/
noncomputable def su2NondegenerateO : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 3 : ℂ) • su2HermBasis.B su2i0

theorem su2NondegenerateRho_isHermitian : su2NondegenerateRhoᴴ = su2NondegenerateRho := by
  simp [su2NondegenerateRho, Matrix.conjTranspose_smul, su2HermBasis.herm su2i0]

theorem su2NondegenerateO_isHermitian : su2NondegenerateOᴴ = su2NondegenerateO := by
  simp [su2NondegenerateO, Matrix.conjTranspose_smul, su2HermBasis.herm su2i0]

private theorem su2_gPurity_smul_basis_zero (c : ℂ) :
    su2HermBasis.gPurity (c • su2HermBasis.B su2i0) = (Complex.normSq c : ℂ) := by
  rw [DLAHermBasis.gPurity]
  have hterm :
      ∀ j, (Complex.normSq (hsInner (su2HermBasis.B j) (c • su2HermBasis.B su2i0)) : ℂ)
        = if j = su2i0 then (Complex.normSq c : ℂ) else 0 := by
    intro j
    rw [hsInner_smul_right, su2HermBasis.ortho j su2i0]
    split <;> simp
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq']
  simp

theorem su2NondegenerateRho_gPurity :
    su2HermBasis.gPurity su2NondegenerateRho = (1 / 4 : ℂ) := by
  rw [su2NondegenerateRho, su2_gPurity_smul_basis_zero]
  norm_num [Complex.normSq_ratCast]

theorem su2NondegenerateO_gPurity :
    su2HermBasis.gPurity su2NondegenerateO = (1 / 9 : ℂ) := by
  rw [su2NondegenerateO, su2_gPurity_smul_basis_zero]
  norm_num [Complex.normSq_ratCast]

theorem su2NondegenerateRho_ne_O : su2NondegenerateRho ≠ su2NondegenerateO := by
  intro h
  have hp : su2HermBasis.gPurity su2NondegenerateRho =
      su2HermBasis.gPurity su2NondegenerateO := by rw [h]
  rw [su2NondegenerateRho_gPurity, su2NondegenerateO_gPurity] at hp
  norm_num at hp

private theorem su2NondegenerateO_kron :
    su2NondegenerateO ⊗ₖ su2NondegenerateO =
      (1 / 9 : ℂ) • (su2HermBasis.B su2i0 ⊗ₖ su2HermBasis.B su2i0) := by
  rw [su2NondegenerateO, Matrix.smul_kronecker, Matrix.kronecker_smul]
  module

theorem su2NondegenerateO_twirl_mem_gTensorG :
    twirl2 qubitClifford (su2NondegenerateO ⊗ₖ su2NondegenerateO) ∈
      gTensorG su2HermBasis := by
  rw [su2NondegenerateO_kron, QuantumAlg.twirl2_smul]
  exact (gTensorG su2HermBasis).smul_mem _ qubitClifford_twirl_basis_zero_mem_gTensorG

/-- The single-qubit Clifford doubled-commutant-complete second moment for the nondegenerate scaled
`su(2)` Hermitian-operator witness pair. -/
noncomputable def su2NondegenerateSecondMoment :
    RagoneSecondMoment su2HermBasis su2NondegenerateRho su2NondegenerateO :=
  RagoneSecondMoment.ofTwoDesign su2HermBasis qubitClifford qubitClifford_mul
    qubitClifford_unitary su2NondegenerateRho_isHermitian su2NondegenerateO_isHermitian
    su2HermBasis_schur qubitClifford_casimir_commute qubitClifford_isDoubledCommutantComplete
    su2NondegenerateO_twirl_mem_gTensorG

theorem su2NondegenerateSecondMoment_variance_eq_gPurity :
    (su2NondegenerateSecondMoment.variance : ℂ) =
      su2HermBasis.gPurity su2NondegenerateRho *
        su2HermBasis.gPurity su2NondegenerateO / (3 : ℂ) := by
  rw [RagoneSecondMoment.variance_eq_gPurity su2NondegenerateSecondMoment
      su2NondegenerateRho_isHermitian su2NondegenerateO_isHermitian su2HermBasis_dim_pos,
    su2HermBasis_dim_eq]
  norm_num

theorem su2NondegenerateSecondMoment_variance_eq :
    (su2NondegenerateSecondMoment.variance : ℂ) = (1 / 108 : ℂ) := by
  rw [su2NondegenerateSecondMoment_variance_eq_gPurity, su2NondegenerateRho_gPurity,
    su2NondegenerateO_gPurity]
  norm_num

/-- A concrete nondegenerate `su(2)` Hermitian-operator witness through the Clifford doubled
twirl: `ρ ≠ O`, both `g`-purities are strict contractions, and the Ragone variance law evaluates
to `P_g(ρ) P_g(O) / 3 = 1/108`, not the degenerate `1/3` value. -/
theorem su2_variance_nondegenerate_witness :
    ∃ ρ O : Matrix (Fin 2) (Fin 2) ℂ, ∃ M : RagoneSecondMoment su2HermBasis ρ O,
      ρᴴ = ρ ∧ Oᴴ = O ∧ ρ ≠ O ∧
        su2HermBasis.gPurity ρ = (1 / 4 : ℂ) ∧
        su2HermBasis.gPurity O = (1 / 9 : ℂ) ∧
        0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1 ∧
        0 < (1 / 9 : ℝ) ∧ (1 / 9 : ℝ) < 1 ∧
        (M.variance : ℂ) = su2HermBasis.gPurity ρ * su2HermBasis.gPurity O / (3 : ℂ) ∧
        (M.variance : ℂ) = (1 / 108 : ℂ) ∧
        (M.variance : ℂ) ≠ (1 / 3 : ℂ) := by
  refine ⟨su2NondegenerateRho, su2NondegenerateO, su2NondegenerateSecondMoment, ?_⟩
  exact ⟨su2NondegenerateRho_isHermitian, su2NondegenerateO_isHermitian,
    su2NondegenerateRho_ne_O, su2NondegenerateRho_gPurity, su2NondegenerateO_gPurity,
    by norm_num, by norm_num, by norm_num, by norm_num,
    su2NondegenerateSecondMoment_variance_eq_gPurity,
    su2NondegenerateSecondMoment_variance_eq,
    by rw [su2NondegenerateSecondMoment_variance_eq]; norm_num⟩

theorem su2NondegenerateO_trace_eq_zero : su2NondegenerateO.trace = 0 := by
  rw [su2NondegenerateO, Matrix.trace_smul, su2BasisZero_trace_eq_zero]
  simp

theorem su2NondegenerateSecondMoment_centeredLoss_eq_uncenteredLoss :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2NondegenerateRho su2NondegenerateO g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ *
            ∑ h, cliffordLoss su2NondegenerateRho su2NondegenerateO h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2NondegenerateRho su2NondegenerateO g) ^ 2 :=
  cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    su2NondegenerateRho su2NondegenerateO su2NondegenerateO_trace_eq_zero

/-! ### A genuine mixed-state witness -/

/-- A genuine mixed single-qubit density operator with the same `su(2)` projection as
`su2NondegenerateRho`: `ρ = 1/2 · I + 1/2 · B₀`. -/
noncomputable def su2MixedStateRho : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 / 2 : ℂ) • su2HermBasis.B su2i0

theorem su2MixedStateRho_isHermitian : su2MixedStateRhoᴴ = su2MixedStateRho := by
  simp [su2MixedStateRho, Matrix.conjTranspose_smul, su2HermBasis.herm su2i0]

theorem su2MixedStateRho_trace : su2MixedStateRho.trace = 1 := by
  rw [su2MixedStateRho, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, su2BasisZero_trace_eq_zero]
  norm_num

theorem su2MixedStateRho_eq_matrix :
    su2MixedStateRho =
      !![(1 / 2 : ℂ), (1 / 2 : ℂ) * rt2inv;
         (1 / 2 : ℂ) * rt2inv, (1 / 2 : ℂ)] := by
  change (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 / 2 : ℂ) • (rt2inv • pauliX) =
    !![(1 / 2 : ℂ), (1 / 2 : ℂ) * rt2inv;
       (1 / 2 : ℂ) * rt2inv, (1 / 2 : ℂ)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]

theorem su2MixedStateRho_posSemidef : Matrix.PosSemidef su2MixedStateRho := by
  rw [su2MixedStateRho_eq_matrix]
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![rt2inv, (1 / 2 : ℂ); 0, (1 / 2 : ℂ)]
  have hchol :
      !![(1 / 2 : ℂ), (1 / 2 : ℂ) * rt2inv;
         (1 / 2 : ℂ) * rt2inv, (1 / 2 : ℂ)] = Aᴴ * A := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, one_div, Fin.zero_eta, Fin.isValue,
        of_apply, cons_val', cons_val_zero, cons_val_fin_one]
      rw [rt2inv_conj, rt2inv_mul_self]
      norm_num
    · simp only [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, one_div, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, of_apply, cons_val', cons_val_one, cons_val_fin_one,
        cons_val_zero, star_zero]
      rw [rt2inv_conj]
      ring
    · simp [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
      norm_num [starRingEnd_apply]
    · simp [A, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
      norm_num [starRingEnd_apply]
  rw [hchol]
  exact Matrix.posSemidef_conjTranspose_mul_self A

private theorem su2_gPurity_add_scalar_basis_zero (c d : ℂ) :
    su2HermBasis.gPurity (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        d • su2HermBasis.B su2i0) = (Complex.normSq d : ℂ) := by
  rw [DLAHermBasis.gPurity]
  have hterm :
      ∀ j, (Complex.normSq
          (hsInner (su2HermBasis.B j)
            (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) + d • su2HermBasis.B su2i0)) : ℂ)
        = if j = su2i0 then (Complex.normSq d : ℂ) else 0 := by
    intro j
    rw [hsInner_add_right, hsInner_smul_right, hsInner_smul_right,
      su2HermBasis.ortho j su2i0]
    have hone : hsInner (su2HermBasis.B j) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
      fin_cases j
      · change hsInner (rt2inv • pauliX) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0
        simp [hsInner, pauliX, Matrix.trace_fin_two]
      · change hsInner (rt2inv • pauliY) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0
        simp [hsInner, pauliY, Matrix.trace_fin_two]
      · change hsInner (rt2inv • pauliZ) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0
        simp [hsInner, pauliZ, Matrix.trace_fin_two]
    rw [hone]
    by_cases hj : j = su2i0 <;> simp [hj]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq']
  simp

theorem su2MixedStateRho_gPurity :
    su2HermBasis.gPurity su2MixedStateRho = (1 / 4 : ℂ) := by
  rw [su2MixedStateRho, su2_gPurity_add_scalar_basis_zero]
  norm_num [Complex.normSq_ratCast]

/-- The Clifford second-moment witness for `su2MixedStateRho` and `su2NondegenerateO`. -/
noncomputable def su2MixedStateSecondMoment :
    RagoneSecondMoment su2HermBasis su2MixedStateRho su2NondegenerateO :=
  RagoneSecondMoment.ofTwoDesign su2HermBasis qubitClifford qubitClifford_mul
    qubitClifford_unitary su2MixedStateRho_isHermitian su2NondegenerateO_isHermitian
    su2HermBasis_schur qubitClifford_casimir_commute qubitClifford_isDoubledCommutantComplete
    su2NondegenerateO_twirl_mem_gTensorG

theorem su2MixedStateSecondMoment_variance_eq_gPurity :
    (su2MixedStateSecondMoment.variance : ℂ) =
      su2HermBasis.gPurity su2MixedStateRho *
        su2HermBasis.gPurity su2NondegenerateO / (3 : ℂ) := by
  rw [RagoneSecondMoment.variance_eq_gPurity su2MixedStateSecondMoment
      su2MixedStateRho_isHermitian su2NondegenerateO_isHermitian su2HermBasis_dim_pos,
    su2HermBasis_dim_eq]
  norm_num

theorem su2MixedStateSecondMoment_variance_eq_uncenteredLoss :
    (su2MixedStateSecondMoment.variance : ℂ) =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g) ^ 2 := by
  rw [su2MixedStateSecondMoment.var_eq]
  change hsInner (su2MixedStateRho ⊗ₖ su2MixedStateRho)
      (twirl2 qubitClifford (su2NondegenerateO ⊗ₖ su2NondegenerateO)) =
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
      ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g) ^ 2
  exact twirl2_hsInner_eq_loss_secondMoment qubitClifford
    su2MixedStateRho su2NondegenerateO su2MixedStateRho_isHermitian

theorem su2MixedStateSecondMoment_variance_eq :
    (su2MixedStateSecondMoment.variance : ℂ) = (1 / 108 : ℂ) := by
  rw [su2MixedStateSecondMoment_variance_eq_gPurity, su2MixedStateRho_gPurity,
    su2NondegenerateO_gPurity]
  norm_num

theorem su2MixedStateSecondMoment_centeredLoss_eq_uncenteredLoss :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g -
          ((Fintype.card BinaryOctahedral : ℂ)⁻¹ *
            ∑ h, cliffordLoss su2MixedStateRho su2NondegenerateO h)) ^ 2 =
      (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
        ∑ g, (cliffordLoss su2MixedStateRho su2NondegenerateO g) ^ 2 :=
  cliffordLoss_centered_eq_uncentered_of_trace_eq_zero
    su2MixedStateRho su2NondegenerateO su2NondegenerateO_trace_eq_zero

theorem su2MixedStateRho_ne_O : su2MixedStateRho ≠ su2NondegenerateO := by
  intro h
  have htr := congrArg Matrix.trace h
  rw [su2MixedStateRho_trace, su2NondegenerateO_trace_eq_zero] at htr
  norm_num at htr

/-- A concrete nondegenerate `su(2)` witness through the genuine Clifford doubled twirl whose
state slot is a genuine density matrix. -/
public theorem su2_variance_mixed_state_witness :
    ∃ ρ O : Matrix (Fin 2) (Fin 2) ℂ, ∃ M : RagoneSecondMoment su2HermBasis ρ O,
      ρᴴ = ρ ∧ Oᴴ = O ∧ ρ.trace = 1 ∧ Matrix.PosSemidef ρ ∧ ρ ≠ O ∧
        su2HermBasis.gPurity ρ = (1 / 4 : ℂ) ∧
        su2HermBasis.gPurity O = (1 / 9 : ℂ) ∧
        (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
          ∑ g, (cliffordLoss ρ O g -
            ((Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ h, cliffordLoss ρ O h)) ^ 2 =
          (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, (cliffordLoss ρ O g) ^ 2 ∧
        (M.variance : ℂ) =
          (Fintype.card BinaryOctahedral : ℂ)⁻¹ * ∑ g, (cliffordLoss ρ O g) ^ 2 ∧
        (M.variance : ℂ) = su2HermBasis.gPurity ρ * su2HermBasis.gPurity O / (3 : ℂ) ∧
        (M.variance : ℂ) = (1 / 108 : ℂ) ∧
        (M.variance : ℂ) ≠ (1 / 3 : ℂ) := by
  refine ⟨su2MixedStateRho, su2NondegenerateO, su2MixedStateSecondMoment, ?_⟩
  exact ⟨su2MixedStateRho_isHermitian, su2NondegenerateO_isHermitian,
    su2MixedStateRho_trace, su2MixedStateRho_posSemidef, su2MixedStateRho_ne_O,
    su2MixedStateRho_gPurity, su2NondegenerateO_gPurity,
    su2MixedStateSecondMoment_centeredLoss_eq_uncenteredLoss,
    su2MixedStateSecondMoment_variance_eq_uncenteredLoss,
    su2MixedStateSecondMoment_variance_eq_gPurity,
    su2MixedStateSecondMoment_variance_eq,
    by rw [su2MixedStateSecondMoment_variance_eq]; norm_num⟩

/-! ## The central double cover -/

/-- The nontrivial scalar element in the strict lift. -/
def binaryOctahedralNegOne : BinaryOctahedral := .axis true 0

@[simp]
theorem binaryOctahedralQuaternion_negOne :
    binaryOctahedralQuaternion binaryOctahedralNegOne = -1 := by
  change (-1 : SqrtTwoRat) • (⟨1, 0, 0, 0⟩ : ExactQuaternion) = -1
  rw [QuaternionAlgebra.smul_mk]
  apply QuaternionAlgebra.ext <;>
    norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive center testing over numerator pairs needs this local reduction budget.
/-- The integer numerators commuting with all numerators are exactly the two scalar lifts. -/
private theorem octNumerator_center :
    ∀ a, (∀ b, octNumerator a * octNumerator b = octNumerator b * octNumerator a) →
      a = 1 ∨ a = binaryOctahedralNegOne := by decide

private theorem binaryOctahedral_exact_center (a : BinaryOctahedral)
    (h : ∀ b, binaryOctahedralQuaternion b * binaryOctahedralQuaternion a =
      binaryOctahedralQuaternion a * binaryOctahedralQuaternion b) :
    a = 1 ∨ a = binaryOctahedralNegOne := by
  apply octNumerator_center a
  intro b
  apply octToExact_injective
  rw [map_mul, map_mul, octToExact_octNumerator, octToExact_octNumerator]
  have hcomm : binaryOctahedralQuaternion a * binaryOctahedralQuaternion b =
      binaryOctahedralQuaternion b * binaryOctahedralQuaternion a := (h b).symm
  -- (a+a)(b+b) = (b+b)(a+a) given a*b = b*a
  linear_combination (norm := noncomm_ring) (4 : ExactQuaternion) * hcomm

theorem binaryOctahedral_mem_center_iff (a : BinaryOctahedral) :
    a ∈ Subgroup.center BinaryOctahedral ↔
      a = 1 ∨ a = binaryOctahedralNegOne := by
  constructor
  · intro ha
    apply binaryOctahedral_exact_center a
    intro b
    rw [← binaryOctahedralQuaternion_mul, ← binaryOctahedralQuaternion_mul]
    exact congrArg binaryOctahedralQuaternion (Submonoid.mem_center_iff.mp ha b)
  · rintro (rfl | rfl)
    · exact (Subgroup.center BinaryOctahedral).one_mem
    · change binaryOctahedralNegOne ∈ Set.center BinaryOctahedral
      rw [Semigroup.mem_center_iff]
      intro b
      apply binaryOctahedralQuaternion_injective
      simp only [binaryOctahedralQuaternion_mul, binaryOctahedralQuaternion_negOne]
      exact (Quaternion.coe_commutes (-1 : SqrtTwoRat)
        (binaryOctahedralQuaternion b)).symm

private theorem binaryOctahedralNegOne_ne_one : binaryOctahedralNegOne ≠ (1 : BinaryOctahedral) :=
  by decide

/-- The center consists exactly of the two scalar lifts. -/
def binaryOctahedralCenterEquivBool : Subgroup.center BinaryOctahedral ≃ Bool where
  toFun z := z.1 ≠ 1
  invFun
    | false => ⟨1, (Subgroup.center BinaryOctahedral).one_mem⟩
    | true => ⟨binaryOctahedralNegOne,
        binaryOctahedral_mem_center_iff binaryOctahedralNegOne |>.mpr (Or.inr rfl)⟩
  left_inv z := by
    rcases binaryOctahedral_mem_center_iff z.1 |>.mp z.2 with h | h
    · apply Subtype.ext
      simp [h]
    · apply Subtype.ext
      simp [h, binaryOctahedralNegOne_ne_one]
  right_inv b := by
    cases b <;> simp [binaryOctahedralNegOne_ne_one]

/-- The strict binary-octahedral lift has a center of order two. -/
theorem binaryOctahedral_center_card :
    Fintype.card (Subgroup.center BinaryOctahedral) = 2 := by
  rw [Fintype.card_congr binaryOctahedralCenterEquivBool]
  decide

/-- Quotienting the strict lift by its scalar center gives the `24` projective Clifford gates. -/
theorem projectiveQubitClifford_card :
    Fintype.card (BinaryOctahedral ⧸ Subgroup.center BinaryOctahedral) = 24 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center BinaryOctahedral)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    binaryOctahedral_card, binaryOctahedral_center_card] at h
  omega
end QuantumAlg.QubitTwoDesign

end
