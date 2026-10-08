/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Native.Born
import all QuantumAlg.Algorithms.OrderFinding.Native.Born
import all QuantumAlg.Core.Measure.Distribution

/-!
# Source phase distribution from the accepted native word

This Born law applies the actual native source matrix to the all-zero input
and measures the phase prefix. It is the mathematical target for the runtime
Z-cell and packing proof; no success bound or runtime equality is asserted
by the definition itself.
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

/-- Terminal phase PMF of the actual declared-query native source word. -/
public def sourceOutcomePMF {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    PMF (TerminalZMeasure.Outcome t) :=
  (measurement t width).outcomePMF (evolvedState access)

end

end QuantumAlg.OrderFinding.Native
