/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic

/-! # Edge-pair 5 numerator closure with signs `11` -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Edge.Pair5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction checks all 48 possible right factors in this fixed-sign shard.
/-- The fixed-sign `11` edge-pair 5 numerator stays closed under right multiplication. -/
theorem signs11 :
    ∀ b, ∃ c,
      octNumerator (.edge (5 : Fin 6) true true) * octNumerator b =
        octNumerator c + octNumerator c := by decide

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Edge.Pair5

end
