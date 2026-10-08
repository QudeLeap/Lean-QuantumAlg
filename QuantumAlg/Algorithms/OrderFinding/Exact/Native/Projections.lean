/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Specification
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Specification
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Independent native exact-dyadic space coordinates

The source sampler retains each measured bit and its packed word. The real
decoder adds one unsigned word of the same width. The original phase and
target systems remain live and all storage is freshly allocated.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

/-- Complete resident classical storage has exactly three phase-width words. -/
public theorem exactOrderFinding_problem_resident_classical {N x t width r : Nat}
    (access : ModExpOracleAccess N x t width) :
    (problem access r).resources.resident .classicalBits = 3 * t := by
  simp [problem, spaceBudget, Sampling.Native.spaceBudget, SpacePool.ofShape]
  omega

/-- The empty input makes every retained classical bit auxiliary. -/
public theorem exactOrderFinding_problem_auxiliary_classical {N x t width r : Nat}
    (access : ModExpOracleAccess N x t width) :
    (problem access r).resources.auxiliary .classicalBits = 3 * t := by
  simp [problem, spaceBudget, Sampling.Native.spaceBudget, SpacePool.ofShape]
  omega

/-- Resident and auxiliary quantum counts agree on every physical dimension. -/
public theorem exactOrderFinding_problem_quantum_systems {N x t width r : Nat}
    (access : ModExpOracleAccess N x t width) (dimension : ℕ+) :
    (problem access r).resources.resident (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then t + width else 0) ∧
    (problem access r).resources.auxiliary (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then t + width else 0) := by
  constructor <;>
    simp [problem, spaceBudget, Sampling.Native.spaceBudget, SpacePool.ofShape]

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
