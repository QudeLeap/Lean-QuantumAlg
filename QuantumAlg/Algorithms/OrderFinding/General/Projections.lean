/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.Space
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Public numerical coordinates of the independent general order-finding budget

These are exact formulas for the declared limits. They do not assert that
every actual path reaches its allowed peak. The borrowed base contributes to
resident classical storage and is excluded from auxiliary classical storage.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

/-- Resident classical capacity includes the borrowed base and the recovery scratch peak. -/
public theorem problem_resident_classical {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width) :
    (problem hinput A).resources.resident .classicalBits =
      12 * t + 3 * width + 15 + max (t + 1) (8 * width + 2) := by
  simp [problem, NativeEndpoint.spaceBudget, NativeEndpoint.recoveryBits,
    ClassicalRoutines.OrderRecovery.Native.extraClassicalBits,
    Sampling.spaceBudget, pre, SpacePool.ofShape]
  omega

/-- Auxiliary classical capacity excludes exactly the caller's original borrowed base. -/
public theorem problem_auxiliary_classical {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width) :
    (problem hinput A).resources.auxiliary .classicalBits =
      12 * t + 2 * width + 15 + max (t + 1) (8 * width + 2) := by
  simp [problem, NativeEndpoint.spaceBudget, NativeEndpoint.recoveryBits,
    ClassicalRoutines.OrderRecovery.Native.extraClassicalBits,
    Sampling.spaceBudget, pre, SpacePool.ofShape]
  omega

/-- The independent resident quantum budget is exactly the original phase and target registers. -/
public theorem problem_resident_quantum {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (dimension : ℕ+) :
    (problem hinput A).resources.resident (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then t + width else 0 := by
  simp [problem, NativeEndpoint.spaceBudget, Sampling.spaceBudget, pre, SpacePool.ofShape]

/-- All quantum systems are prepared internally and count equally toward the auxiliary budget. -/
public theorem problem_auxiliary_quantum {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (dimension : ℕ+) :
    (problem hinput A).resources.auxiliary (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then t + width else 0 := by
  simp [problem, NativeEndpoint.spaceBudget, Sampling.spaceBudget, pre, SpacePool.ofShape]

/-- The original positive phase width has this explicit unit-event depth allowance. -/
public theorem problem_depth {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (positive : 0 < t) :
    (problem hinput A).depth = .quantum (fun _ => 1)
      (6 * t + 12 + t * (t - 1) / 2 + t / 2 +
        2 * (t + 1) * (2 * width + 16 + 6 * (t + 1))) := by
  have arithmetic : NativeEndpoint.depthBudget t width =
      6 * t + 12 + t * (t - 1) / 2 + t / 2 +
        2 * (t + 1) * (2 * width + 16 + 6 * (t + 1)) := by
    unfold NativeEndpoint.depthBudget Sampling.depthBudget Sampling.unitaryDepth
      ClassicalRoutines.OrderRecovery.Native.unitDepthBound
    simp only [Nat.ne_of_gt positive, if_false]
    omega
  change DepthBudget.quantum (fun _ => 1) (NativeEndpoint.depthBudget t width) = _
  rw [arithmetic]

end

end QuantumAlg.OrderFinding.ShorSourceJoint
