/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair0
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair1
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair2
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair3
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair4
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge.Pair5

/-! # Edge-left binary-octahedral numerator closure -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed

/-- Multiplication by an edge-family numerator stays in the doubled numerator set. -/
theorem edge :
    ∀ pair negativeLeft negativeRight b, ∃ c,
      octNumerator (.edge pair negativeLeft negativeRight) * octNumerator b =
        octNumerator c + octNumerator c := by
  intro pair negativeLeft negativeRight b
  fin_cases pair
  · exact Edge.pair0 negativeLeft negativeRight b
  · exact Edge.pair1 negativeLeft negativeRight b
  · exact Edge.pair2 negativeLeft negativeRight b
  · exact Edge.pair3 negativeLeft negativeRight b
  · exact Edge.pair4 negativeLeft negativeRight b
  · exact Edge.pair5 negativeLeft negativeRight b

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed

end
