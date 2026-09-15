/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.Construction
public import QuantumAlg.Components.Gates
import all QuantumAlg.Algorithms.OrderFinding.General.Endpoint
import all QuantumAlg.Algorithms.OrderFinding.General.Counts

/-!
# Public exact source-query and gate counts after native general recovery

The complete execution's actual classical recovery adds no quantum event.
These exact multiplicities apply to every actual path of that same run.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

/-- Every complete actual path uses one original modular-exponentiation query. -/
public theorem algorithm_modExpCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (path : (algorithm hinput A).run.code.Path) :
    ResourcePool.count (modExpEvent N x t width)
      ((algorithm hinput A).run.code.resourcePool path) = 1 :=
  NativeEndpoint.code_modExpCount hinput A path

/-- The actual complete algorithm retains all three original exact quantum-gate counts. -/
public theorem algorithm_quantumGateCounts {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (path : (algorithm hinput A).run.code.Path) :
    ResourcePool.count (.gate (.builtin "hadamard"))
        ((algorithm hinput A).run.code.resourcePool path) = 2 * t ∧
      ResourcePool.count (.gate qftControlledPhaseLabel)
        ((algorithm hinput A).run.code.resourcePool path) = t * (t - 1) / 2 ∧
      ResourcePool.count (.gate (.builtin "swap"))
        ((algorithm hinput A).run.code.resourcePool path) = t / 2 :=
  NativeEndpoint.code_quantumGateCounts hinput A path

end

end QuantumAlg.OrderFinding.ShorSourceJoint
