/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.Construction
public import QuantumAlg.Components.Gates
import all QuantumAlg.Algorithms.OrderFinding.Exact.Endpoint
import all QuantumAlg.Algorithms.OrderFinding.Exact.Counts

/-!
# Public exact counts of the complete decoded order sample

These equalities concern each actual path of the complete algorithm. The real
classical decoder contributes its own fixed-width shifts and selected increments;
the original source-query and quantum-gate multiplicities remain exact.
-/

namespace QuantumAlg.OrderFinding

noncomputable section

/-- Every actual complete execution makes exactly one original modular-exponentiation query. -/
public theorem algorithm_modExpCount {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (algorithm A).run.code.Path) :
    ResourcePool.count (modExpEvent N x t n) ((algorithm A).run.code.resourcePool path) = 1 :=
  Exact.code_modExpCount A path

/-- Actual decoding preserves the original exact Hadamard, controlled-phase and SWAP counts. -/
public theorem algorithm_quantumGateCounts {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (algorithm A).run.code.Path) :
    ResourcePool.count (.gate (.builtin "hadamard"))
      ((algorithm A).run.code.resourcePool path) = 2 * t ∧
      ResourcePool.count (.gate qftControlledPhaseLabel)
        ((algorithm A).run.code.resourcePool path) = t * (t - 1) / 2 ∧
      ResourcePool.count (.gate (.builtin "swap"))
        ((algorithm A).run.code.resourcePool path) = t / 2 :=
  Exact.code_quantumGateCounts A path

/-- The actual complete algorithm performs one fixed-width left shift per measured phase bit. -/
public theorem algorithm_shiftCount {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (algorithm A).run.code.Path) :
    ResourcePool.count (.classicalOperation (.wordUnary .shiftLeft t))
      ((algorithm A).run.code.resourcePool path) = t :=
  Exact.code_shiftCount A path

end

end QuantumAlg.OrderFinding
