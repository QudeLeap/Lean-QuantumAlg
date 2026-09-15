/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Axis
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Half
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Edge

/-!
# Binary-octahedral numerator multiplicative closure

Kernel reduction proves multiplicative closure of the exact integer numerator codes.
-/

section

namespace QuantumAlg.QubitTwoDesign

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive multiplication over pairs of numerator codes needs this local budget.
/-- Multiplicative closure of the numerators: `(2a)(2b) = (2·ab) + (2·ab)`. -/
theorem octNumerator_closed :
    ∀ a b, ∃ c, octNumerator a * octNumerator b = octNumerator c + octNumerator c := by
  intro a b
  cases a with
  | axis negative coordinate => exact OctNumeratorClosed.axis negative coordinate b
  | half negative => exact OctNumeratorClosed.half negative b
  | edge pair negativeLeft negativeRight =>
      exact OctNumeratorClosed.edge pair negativeLeft negativeRight b

end QuantumAlg.QubitTwoDesign

end
