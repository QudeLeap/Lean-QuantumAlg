/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic

/-! # Pauli-Z normalization for half-coordinate Clifford codes -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer.Z

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

local macro "pauliConjFinish" : tactic =>
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

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-Z conjugation over the sixteen half-coordinate codes needs this local budget.
lemma half (negative : Fin 4 → Bool) :
    qubitClifford (.half negative) * pauliZ * (qubitClifford (.half negative))ᴴ ∈
      signedRawPauliSet := by
  by_cases h0 : negative 0 <;> by_cases h1 : negative 1 <;>
    by_cases h2 : negative 2 <;> by_cases h3 : negative 3 <;>
      simp only [signedRawPauliSet, Set.mem_ofPred_eq]
  · right; right; left; pauliConjFinish
  · right; left; pauliConjFinish
  · left; pauliConjFinish
  · right; right; right; left; pauliConjFinish
  · right; left; pauliConjFinish
  · right; right; right; left; pauliConjFinish
  · right; right; left; pauliConjFinish
  · left; pauliConjFinish
  · left; pauliConjFinish
  · right; right; left; pauliConjFinish
  · right; right; right; left; pauliConjFinish
  · right; left; pauliConjFinish
  · right; right; right; left; pauliConjFinish
  · left; pauliConjFinish
  · right; left; pauliConjFinish
  · right; right; left; pauliConjFinish

end QuantumAlg.QubitTwoDesign.PauliNormalizer.Z

end
