/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Resources

/-!
# Empty-input native sampling resources

The empty-input endpoint specializes the single Framed sampler.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

open QuantumAlg.Execution

/-- Actual native counts specialize the common sampler's independent budget. -/
theorem code_events {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) :
    (code A).resourcePool path = eventBudget N x t n :=
  Framed.code_events pre pre_quantumWires A path

/-- Actual unit depth specializes the same common code and path. -/
theorem code_depth {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) : (code A).depth (fun _ => 1) path = depthBudget t :=
  Framed.code_depth pre pre_quantumWires A path

/-- Exactly one original modular-exponentiation query occurs on every path. -/
theorem code_modExpCount {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) :
    ResourcePool.count (modExpEvent N x t n) ((code A).resourcePool path) = 1 :=
  Framed.code_modExpCount pre pre_quantumWires A path

end

end QuantumAlg.OrderFinding.Sampling
