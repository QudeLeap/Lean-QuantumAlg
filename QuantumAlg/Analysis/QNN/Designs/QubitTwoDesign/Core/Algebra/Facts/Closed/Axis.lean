/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Axis.Coordinate0
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Axis.Coordinate1
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Axis.Coordinate2
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Axis.Coordinate3

/-! # Axis-left binary-octahedral numerator closure -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed

/-- Multiplication by an axis-family numerator stays in the doubled numerator set. -/
theorem axis :
    ∀ negative coordinate b, ∃ c,
      octNumerator (.axis negative coordinate) * octNumerator b =
        octNumerator c + octNumerator c := by
  intro negative coordinate b
  fin_cases coordinate
  · exact Axis.coordinate0 negative b
  · exact Axis.coordinate1 negative b
  · exact Axis.coordinate2 negative b
  · exact Axis.coordinate3 negative b

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed

end
