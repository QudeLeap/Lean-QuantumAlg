/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic

/-! # Edge-pair 2 binary-octahedral numerator closure -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Edge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction over the four sign choices and 48 right factors needs this local budget.
/-- Multiplication by edge-pair 2 numerators stays in the doubled numerator set. -/
theorem pair2 :
    ∀ negativeLeft negativeRight b, ∃ c,
      octNumerator (.edge (2 : Fin 6) negativeLeft negativeRight) * octNumerator b =
        octNumerator c + octNumerator c := by decide

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Edge

end
