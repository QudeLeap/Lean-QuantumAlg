/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Automation

/-! # Pauli-X normalization for half-coordinate Clifford codes -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer.X

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-X conjugation over the sixteen half-coordinate codes needs this local budget.
lemma half (negative : Fin 4 → Bool) :
    qubitClifford (.half negative) * pauliX * (qubitClifford (.half negative))ᴴ ∈
      signedRawPauliSet := by
  by_cases h0 : negative 0 <;> by_cases h1 : negative 1 <;>
    by_cases h2 : negative 2 <;> by_cases h3 : negative 3 <;>
      simp only [signedRawPauliSet, Set.mem_ofPred_eq]
  · right; right; right; right; left; pauliHalfConjFinish
  · right; right; right; left; pauliHalfConjFinish
  · right; right; right; left; pauliHalfConjFinish
  · right; right; right; right; right; pauliHalfConjFinish
  · right; right; left; pauliHalfConjFinish
  · right; right; right; right; left; pauliHalfConjFinish
  · right; right; right; right; right; pauliHalfConjFinish
  · right; right; left; pauliHalfConjFinish
  · right; right; left; pauliHalfConjFinish
  · right; right; right; right; right; pauliHalfConjFinish
  · right; right; right; right; left; pauliHalfConjFinish
  · right; right; left; pauliHalfConjFinish
  · right; right; right; right; right; pauliHalfConjFinish
  · right; right; right; left; pauliHalfConjFinish
  · right; right; right; left; pauliHalfConjFinish
  · right; right; right; right; left; pauliHalfConjFinish

end QuantumAlg.QubitTwoDesign.PauliNormalizer.X

end
