/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.Realization

/-! # Raw Pauli-normalizer definitions -/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

/-- The signed raw, unnormalized one-qubit Pauli set `{±X, ±Y, ±Z}`. -/
def signedRawPauliSet : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {P | P = pauliX ∨ P = -pauliX ∨ P = pauliY ∨ P = -pauliY ∨
    P = pauliZ ∨ P = -pauliZ}

lemma signedRawPauliSet_neg_mem {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : P ∈ signedRawPauliSet) : -P ∈ signedRawPauliSet := by
  change P = pauliX ∨ P = -pauliX ∨ P = pauliY ∨ P = -pauliY ∨
    P = pauliZ ∨ P = -pauliZ at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [signedRawPauliSet]

namespace PauliNormalizer

lemma complex_sqrt_two_sq : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end PauliNormalizer
end QuantumAlg.QubitTwoDesign

end
