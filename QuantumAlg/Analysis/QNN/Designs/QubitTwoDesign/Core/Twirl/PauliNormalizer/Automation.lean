/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module


import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic

/-! # Internal finite Pauli-normalizer proof automation -/

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

/-- Prove an axis-element Pauli conjugation identity by finite matrix expansion. -/
macro "pauliAxisConjFinish" : tactic =>
  `(tactic|
    (ext i j <;> fin_cases i <;> fin_cases j <;>
      simp_all only [qubitClifford, binaryOctahedralQuaternion, signed] <;>
      simp_all only [realQuaternion] <;>
      simp_all only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
        Quaternion.imK_smul] <;>
      simp_all [quaternionBasis, sqrtTwoEval_apply, quaternionMatrix, pauliX, pauliY,
        pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
      try ring_nf <;>
      simp [Complex.I_sq, starRingEnd_apply, complex_sqrt_two_sq,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
      ring_nf <;>
      norm_num))

/-- Select the matching signed Pauli image for an axis element and prove its equality. -/
macro "pauliAxisMemFinish" : tactic =>
  `(tactic|
    (simp only [signedRawPauliSet, Set.mem_ofPred_eq]
     first
     | left; pauliAxisConjFinish; done
     | right; left; pauliAxisConjFinish; done
     | right; right; left; pauliAxisConjFinish; done
     | right; right; right; left; pauliAxisConjFinish; done
     | right; right; right; right; left; pauliAxisConjFinish; done
     | right; right; right; right; right; pauliAxisConjFinish; done))

/-- Prove a half-coordinate-element Pauli conjugation identity by matrix expansion. -/
macro "pauliHalfConjFinish" : tactic =>
  `(tactic|
    (ext i j <;> fin_cases i <;> fin_cases j <;>
      simp_all only [qubitClifford, binaryOctahedralQuaternion, halfCoefficient, signed] <;>
      simp_all only [realQuaternion] <;>
      simp_all [sqrtTwoEval_apply, quaternionMatrix, pauliX, pauliY, pauliZ,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
      try ring_nf <;>
      simp [Complex.I_sq, starRingEnd_apply, complex_sqrt_two_sq,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
      ring_nf <;>
      norm_num))

/-- Select and verify the signed Pauli image of a half-coordinate element. -/
macro "pauliHalfMemFinish" : tactic =>
  `(tactic|
    (simp only [signedRawPauliSet, Set.mem_ofPred_eq]
     first
     | left; pauliHalfConjFinish; done
     | right; left; pauliHalfConjFinish; done
     | right; right; left; pauliHalfConjFinish; done
     | right; right; right; left; pauliHalfConjFinish; done
     | right; right; right; right; left; pauliHalfConjFinish; done
     | right; right; right; right; right; pauliHalfConjFinish; done))

/-- Prove an edge-element Pauli conjugation identity using its two quaternion coordinates. -/
macro "pauliEdgeConjFinish" : tactic =>
  `(tactic|
    (ext i j <;> fin_cases i <;> fin_cases j <;>
      simp_all only [qubitClifford, binaryOctahedralQuaternion, sqrtTwoHalf, signed] <;>
      simp_all only [realQuaternion] <;>
      simp_all only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
        Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul,
        Quaternion.imJ_smul, Quaternion.imK_smul] <;>
      simp_all [coordinatePair, quaternionBasis, sqrtTwoEval_apply, quaternionMatrix,
        pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two] <;>
      try ring_nf <;>
      simp [Complex.I_sq, starRingEnd_apply, complex_sqrt_two_sq,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
      ring_nf <;>
      norm_num))

/-- Select and verify the signed Pauli image of an edge element. -/
macro "pauliEdgeMemFinish" : tactic =>
  `(tactic|
    (simp only [signedRawPauliSet, Set.mem_ofPred_eq]
     first
     | left; pauliEdgeConjFinish; done
     | right; left; pauliEdgeConjFinish; done
     | right; right; left; pauliEdgeConjFinish; done
     | right; right; right; left; pauliEdgeConjFinish; done
     | right; right; right; right; left; pauliEdgeConjFinish; done
     | right; right; right; right; right; pauliEdgeConjFinish; done))

end QuantumAlg.QubitTwoDesign.PauliNormalizer
