/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic

/-! # Pauli-Z normalization for edge Clifford codes -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer.Z

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

local macro "pauliConjFinish" : tactic =>
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

local macro "pauliMemFinish" : tactic =>
  `(tactic|
    (simp only [signedRawPauliSet, Set.mem_ofPred_eq]
     first
     | left; pauliConjFinish; done
     | right; left; pauliConjFinish; done
     | right; right; left; pauliConjFinish; done
     | right; right; right; left; pauliConjFinish; done
     | right; right; right; right; left; pauliConjFinish; done
     | right; right; right; right; right; pauliConjFinish; done))

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-Z conjugation over the twenty-four edge codes needs this local budget.
lemma edge (pair : Fin 6) (negativeLeft negativeRight : Bool) :
    qubitClifford (.edge pair negativeLeft negativeRight) * pauliZ *
        (qubitClifford (.edge pair negativeLeft negativeRight))ᴴ ∈ signedRawPauliSet := by
  fin_cases pair <;> cases negativeLeft <;> cases negativeRight <;> pauliMemFinish

end QuantumAlg.QubitTwoDesign.PauliNormalizer.Z

end
