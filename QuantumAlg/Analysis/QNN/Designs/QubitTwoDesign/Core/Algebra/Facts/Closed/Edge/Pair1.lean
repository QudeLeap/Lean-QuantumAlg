/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair1.Signs00
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair1.Signs01
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair1.Signs10
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair1.Signs11

/-! # Edge-pair 1 binary-octahedral numerator closure -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Edge

/-- Multiplication by edge-pair 1 numerators stays in the doubled numerator set. -/
lemma pair1 :
    ∀ negativeLeft negativeRight b, ∃ c,
      octNumerator (.edge (1 : Fin 6) negativeLeft negativeRight) * octNumerator b =
        octNumerator c + octNumerator c := by
  intro negativeLeft negativeRight b
  cases negativeLeft <;> cases negativeRight
  · exact Pair1.signs00 b
  · exact Pair1.signs01 b
  · exact Pair1.signs10 b
  · exact Pair1.signs11 b

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Edge

end
