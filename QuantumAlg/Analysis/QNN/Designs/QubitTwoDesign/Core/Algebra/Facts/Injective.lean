/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic

/-!
# Binary-octahedral numerator injectivity

Kernel comparison proves that the 48 exact integer numerator codes are pairwise distinct.
-/

section

namespace QuantumAlg.QubitTwoDesign

-- M-13 canary, measured 2026-07-09 with
-- `/usr/bin/time -p lake build QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign`:
-- Lake reported `Built ... (186s)`; `/usr/bin/time` reported `real 188.89`.
-- A subsequent full `lake build` on the same file reported `QubitTwoDesign (274s)`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel comparison of all `48` numerator codes needs this local budget.
/-- The `48` integer numerators are pairwise distinct. -/
theorem octNumerator_injective : Function.Injective octNumerator := by decide

end QuantumAlg.QubitTwoDesign

end
