/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic

/-! # Coordinate-2 axis numerator closure -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Axis

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction covers two signs and 48 right factors in this bounded shard.
/-- Multiplication by coordinate-2 axis numerators stays in the doubled numerator set. -/
theorem coordinate2 :
    ∀ negative b, ∃ c,
      octNumerator (.axis negative (2 : Fin 4)) * octNumerator b =
        octNumerator c + octNumerator c := by decide

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Axis

end
