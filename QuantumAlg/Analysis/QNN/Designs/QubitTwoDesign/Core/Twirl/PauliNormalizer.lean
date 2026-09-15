/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.X
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Y
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Z

/-!
# Raw Pauli normalization by the strict Clifford lift

The three raw Pauli-axis calculations live in independent elaboration units;
this module combines them into the normalizer theorem used by the
QubitTwoDesign interface.
-/

section

namespace QuantumAlg.QubitTwoDesign

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

/-- The strict single-qubit Clifford lift normalizes the signed raw Pauli axes. -/
theorem qubitClifford_conj_pauli_mem (g : BinaryOctahedral)
    {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ signedRawPauliSet) :
    qubitClifford g * P * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  change P = pauliX ∨ P = -pauliX ∨ P = pauliY ∨ P = -pauliY ∨
    P = pauliZ ∨ P = -pauliZ at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · exact PauliNormalizer.conjPauliXMem g
  · simpa [mul_neg, neg_mul, Matrix.mul_assoc] using
      signedRawPauliSet_neg_mem (PauliNormalizer.conjPauliXMem g)
  · exact PauliNormalizer.conjPauliYMem g
  · simpa [mul_neg, neg_mul, Matrix.mul_assoc] using
      signedRawPauliSet_neg_mem (PauliNormalizer.conjPauliYMem g)
  · exact PauliNormalizer.conjPauliZMem g
  · simpa [mul_neg, neg_mul, Matrix.mul_assoc] using
      signedRawPauliSet_neg_mem (PauliNormalizer.conjPauliZMem g)

end QuantumAlg.QubitTwoDesign

end
