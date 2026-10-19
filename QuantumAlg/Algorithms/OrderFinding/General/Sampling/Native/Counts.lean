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
public lemma singleQubitCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate .singleQubit) ((code t width).resourcePool path) =
      2 * t + 3 * t.choose 2 := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Controlled phases and expanded SWAPs use this many physical CNOT gates. -/
public lemma cnotCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate .cnot) ((code t width).resourcePool path) =
      2 * t.choose 2 + 3 * (t / 2) := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- No native Toffoli is present outside the sealed modular-exponentiation call. -/
public lemma toffoliCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate .toffoli) ((code t width).resourcePool path) = 0 := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Every phase qubit has one actual Z write to a retained result cell. -/
public lemma measurementCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.measurement (2 : ℕ+)) ((code t width).resourcePool path) = t := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- One selected finite-word operation packs the stored phase bits. -/
public lemma packCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.classicalOperation (.nominalEncoding (.packFiniteBits t)))
      ((code t width).resourcePool path) = 1 := by
  rw [events]
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling
