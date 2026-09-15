/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Group

/-!
# Strict SU(2) realization of the binary octahedral group

This leaf embeds the exact binary-octahedral model into complex single-qubit
matrices and proves the strict lift is faithful, multiplicative, and unitary.
-/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

theorem realQuaternion_mul (p q : ExactQuaternion) :
    realQuaternion (p * q) = realQuaternion p * realQuaternion q := by
  apply QuaternionAlgebra.ext
  · rw [Quaternion.re_mul (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, Quaternion.re_mul, map_sub, map_mul]
  · rw [Quaternion.imI_mul (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, Quaternion.imI_mul, map_add, map_sub, map_mul]
  · rw [Quaternion.imJ_mul (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, Quaternion.imJ_mul, map_add, map_sub, map_mul]
  · rw [Quaternion.imK_mul (a := realQuaternion p) (b := realQuaternion q)]
    simp [realQuaternion, Quaternion.imK_mul, map_add, map_sub, map_mul]

theorem realQuaternion_normSq (q : ExactQuaternion) :
    Quaternion.normSq (realQuaternion q) = sqrtTwoEval (Quaternion.normSq q) := by
  rw [Quaternion.normSq_def' (a := realQuaternion q), Quaternion.normSq_def' (a := q)]
  simp only [realQuaternion, map_pow, map_add]

/-- The standard faithful embedding of real Hamilton quaternions in complex `2 × 2` matrices. -/
noncomputable def quaternionMatrix (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + (q.imI : ℂ) * Complex.I,
      (q.imJ : ℂ) + (q.imK : ℂ) * Complex.I;
     -(q.imJ : ℂ) + (q.imK : ℂ) * Complex.I,
      (q.re : ℂ) - (q.imI : ℂ) * Complex.I]

theorem quaternionMatrix_mul (p q : Quaternion ℝ) :
    quaternionMatrix (p * q) = quaternionMatrix p * quaternionMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring

theorem quaternionMatrix_det (q : Quaternion ℝ) :
    Matrix.det (quaternionMatrix q) = Quaternion.normSq q := by
  simp [quaternionMatrix, Matrix.det_fin_two, Quaternion.normSq_def']
  ring_nf
  simp [Complex.I_sq]
  ring

theorem quaternionMatrix_star_mul (q : Quaternion ℝ) :
    (quaternionMatrix q)ᴴ * quaternionMatrix q =
      ((Quaternion.normSq q : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.smul_apply, Quaternion.normSq_def'] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem quaternionMatrix_injective : Function.Injective quaternionMatrix := by
  intro p q h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  apply QuaternionAlgebra.ext
  · simpa [quaternionMatrix] using congrArg Complex.re h00
  · simpa [quaternionMatrix] using congrArg Complex.im h00
  · simpa [quaternionMatrix] using congrArg Complex.re h01
  · simpa [quaternionMatrix] using congrArg Complex.im h01

/-- The strict single-qubit Clifford lift as complex matrices. -/
noncomputable def qubitClifford (g : BinaryOctahedral) : Matrix (Fin 2) (Fin 2) ℂ :=
  quaternionMatrix (realQuaternion (binaryOctahedralQuaternion g))

theorem qubitClifford_mul (a b : BinaryOctahedral) :
    qubitClifford (a * b) = qubitClifford a * qubitClifford b := by
  change quaternionMatrix (realQuaternion (binaryOctahedralQuaternion (a * b))) =
    quaternionMatrix (realQuaternion (binaryOctahedralQuaternion a)) *
      quaternionMatrix (realQuaternion (binaryOctahedralQuaternion b))
  rw [binaryOctahedralQuaternion_mul, realQuaternion_mul, quaternionMatrix_mul]

/-- Every strict lift has determinant one. -/
theorem qubitClifford_det (g : BinaryOctahedral) : Matrix.det (qubitClifford g) = 1 := by
  rw [qubitClifford, quaternionMatrix_det, realQuaternion_normSq,
    binaryOctahedralQuaternion_normSq, map_one]
  norm_num

/-- Every strict lift is unitary. -/
theorem qubitClifford_unitary (g : BinaryOctahedral) :
    (qubitClifford g)ᴴ * qubitClifford g = 1 := by
  have hnorm : Quaternion.normSq
      (realQuaternion (binaryOctahedralQuaternion g)) = 1 := by
    rw [realQuaternion_normSq, binaryOctahedralQuaternion_normSq, map_one]
  rw [qubitClifford, quaternionMatrix_star_mul, hnorm]
  simp

/-- The `48` strict matrices remain pairwise distinct. -/
theorem qubitClifford_injective : Function.Injective qubitClifford :=
  quaternionMatrix_injective.comp
    (realQuaternion_injective.comp binaryOctahedralQuaternion_injective)

end QuantumAlg.QubitTwoDesign

end
