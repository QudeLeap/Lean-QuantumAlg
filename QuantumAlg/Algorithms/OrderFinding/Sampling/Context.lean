/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Original empty order-finding input

The empty-input endpoint specializes the single Framed sampler.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

/-- The original empty input to the exact-order sample. -/
@[reducible] public def pre : RuntimeCtx .quantum := RuntimeCtx.empty

private lemma pre_quantumWires_eq : pre.quantumWires = [] := rfl

public lemma pre_quantumWires : pre.quantumWires = [] := pre_quantumWires_eq

end

end QuantumAlg.OrderFinding.Sampling
