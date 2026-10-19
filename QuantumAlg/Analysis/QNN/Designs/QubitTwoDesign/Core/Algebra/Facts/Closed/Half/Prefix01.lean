/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Basic

/-! # `01`-prefix half numerator closure -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Half

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction covers four suffix signs and 48 right factors in this bounded shard.
/-- Half numerators with a `01` sign prefix stay in the doubled numerator set. -/
lemma prefix01 :
    ∀ negative2 negative3 b, ∃ c,
      octNumerator (.half ![false, true, negative2, negative3]) * octNumerator b =
        octNumerator c + octNumerator c := by decide

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed.Half

end
