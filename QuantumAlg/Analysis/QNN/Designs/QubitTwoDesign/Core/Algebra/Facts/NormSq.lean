/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic

/-!
# Binary-octahedral numerator norm

Kernel reduction proves that every exact integer numerator has squared norm four.
-/

section

namespace QuantumAlg.QubitTwoDesign

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive norm reduction over the `48` numerator codes needs this local budget.
/-- Every integer numerator has squared norm `4` (the unit quaternion scaled by `2`). -/
theorem octNumerator_normSq : ∀ a, Quaternion.normSq (octNumerator a) = 4 := by decide

end QuantumAlg.QubitTwoDesign

end
