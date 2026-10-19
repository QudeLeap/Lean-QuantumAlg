/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic

/-!
# Binary-octahedral numerator star closure

Kernel reduction proves star closure of the exact integer numerator codes.
-/

section

namespace QuantumAlg.QubitTwoDesign

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive star lookup over the numerator codes needs this local budget.
/-- Star closure of the numerators. -/
lemma octNumerator_star_closed : ∀ a, ∃ b, octNumerator b = star (octNumerator a) := by decide

end QuantumAlg.QubitTwoDesign

end
