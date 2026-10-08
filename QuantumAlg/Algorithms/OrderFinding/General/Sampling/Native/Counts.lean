/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Elementary coordinates of the borrowed-base source sample

Each count observes the same complete execution that retains the original
canonical residue. The declared modular-exponentiation query remains a
separate source coordinate rather than an invented native gate expansion.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling

noncomputable section

open QuantumAlg.Execution

/-- The phase Hadamards and expanded inverse QFT use this many one-qubit gates. -/
public theorem singleQubitCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate .singleQubit) ((code access).resourcePool path) =
      2 * t + 3 * t.choose 2 := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Controlled phases and expanded SWAPs use this many physical CNOT gates. -/
public theorem cnotCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate .cnot) ((code access).resourcePool path) =
      2 * t.choose 2 + 3 * (t / 2) := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- No native Toffoli is present outside the sealed modular-exponentiation call. -/
public theorem toffoliCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate .toffoli) ((code access).resourcePool path) = 0 := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Every phase qubit has one actual Z write to a retained result cell. -/
public theorem measurementCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.measurement (2 : ℕ+)) ((code access).resourcePool path) = t := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- One selected finite-word operation packs the stored phase bits. -/
public theorem packCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.classicalOperation (.nominalEncoding (.packFiniteBits t)))
      ((code access).resourcePool path) = 1 := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling
