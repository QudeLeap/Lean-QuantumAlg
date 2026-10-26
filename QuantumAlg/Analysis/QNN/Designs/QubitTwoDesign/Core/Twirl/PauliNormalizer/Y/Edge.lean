/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Automation

/-! # Pauli-Y normalization for edge Clifford codes -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer.Y

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-Y conjugation over the twenty-four edge codes needs this local budget.
lemma edge (pair : Fin 6) (negativeLeft negativeRight : Bool) :
    qubitClifford (.edge pair negativeLeft negativeRight) * pauliY *
        (qubitClifford (.edge pair negativeLeft negativeRight))ᴴ ∈ signedRawPauliSet := by
  fin_cases pair <;> cases negativeLeft <;> cases negativeRight <;>
    simp only [signedRawPauliSet, Set.mem_ofPred_eq]
  · left; pauliEdgeConjFinish
  · right; left; pauliEdgeConjFinish
  · right; left; pauliEdgeConjFinish
  · left; pauliEdgeConjFinish
  · right; right; left; pauliEdgeConjFinish
  · right; right; left; pauliEdgeConjFinish
  · right; right; left; pauliEdgeConjFinish
  · right; right; left; pauliEdgeConjFinish
  · right; right; right; right; right; pauliEdgeConjFinish
  · right; right; right; right; left; pauliEdgeConjFinish
  · right; right; right; right; left; pauliEdgeConjFinish
  · right; right; right; right; right; pauliEdgeConjFinish
  · right; right; right; right; left; pauliEdgeConjFinish
  · right; right; right; right; right; pauliEdgeConjFinish
  · right; right; right; right; right; pauliEdgeConjFinish
  · right; right; right; right; left; pauliEdgeConjFinish
  · right; right; right; left; pauliEdgeConjFinish
  · right; right; right; left; pauliEdgeConjFinish
  · right; right; right; left; pauliEdgeConjFinish
  · right; right; right; left; pauliEdgeConjFinish
  · left; pauliEdgeConjFinish
  · right; left; pauliEdgeConjFinish
  · right; left; pauliEdgeConjFinish
  · left; pauliEdgeConjFinish

end QuantumAlg.QubitTwoDesign.PauliNormalizer.Y

end
