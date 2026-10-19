/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Specification
public import QuantumAlg.Util.Order.Finding
public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Specification
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Space
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Public coordinates of the independent native general-order budget

The original borrowed base is resident and is excluded from auxiliary space.
These are coordinates of the independent problem budget, rather than claims
that every execution path attains the limit.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

/-- Resident classical capacity includes the borrowed base and recovery scratch. -/
public lemma generalOrderFinding_problem_resident_classical {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat) :
    (problem spec x t).resources.resident .classicalBits =
      12 * t + 3 * width + 15 + max (t + 1) (8 * width + 2) := by
  simp [problem, spaceBudget, recoveryBits, Sampling.Native.spaceBudget, pre,
    ClassicalRoutines.OrderRecovery.Native.extraClassicalBits, SpacePool.ofShape]
  omega

/-- Auxiliary classical capacity omits the caller's borrowed base. -/
public lemma generalOrderFinding_problem_auxiliary_classical {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat) :
    (problem spec x t).resources.auxiliary .classicalBits =
      12 * t + 2 * width + 15 + max (t + 1) (8 * width + 2) := by
  simp [problem, spaceBudget, recoveryBits, Sampling.Native.spaceBudget, pre,
    ClassicalRoutines.OrderRecovery.Native.extraClassicalBits, SpacePool.ofShape]
  omega

/-- The only resident quantum systems are the owned phase and target registers. -/
public lemma generalOrderFinding_problem_resident_quantum {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat)
    (dimension : ℕ+) :
    (problem spec x t).resources.resident (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then t + width else 0 := by
  simp [problem, spaceBudget, Sampling.Native.spaceBudget, pre, SpacePool.ofShape]

/-- All sample quantum systems are fresh and charged as auxiliary systems. -/
public lemma generalOrderFinding_problem_auxiliary_quantum {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat)
    (dimension : ℕ+) :
    (problem spec x t).resources.auxiliary (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then t + width else 0 := by
  simp [problem, spaceBudget, Sampling.Native.spaceBudget, pre, SpacePool.ofShape]

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
