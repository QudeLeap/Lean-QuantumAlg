/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Algorithms.OrderFinding.Construction
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Independent order-finding sampling resource limits

These formulas state the original one-query phase sampling cost before any
exact-grid or continued-fraction recovery. They include actual zero preparation,
sequential Z writes, and bit packing, independently of an implementation.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

/-- One basis preparation for all original phase and target systems. -/
def basisPreparationEvent (t n : Nat) : Resource.Event .quantum :=
  .preparation
    { family := "builtin", name := "computational-basis"
      parameters := (t + n) :: (List.replicate (t + n) 2 ++ List.replicate (t + n) 0) }

/-- Original Hadamards, one modular-exponentiation query, and the inverse-QFT gates. -/
def unitaryEventBudget (N x t n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton WalshHadamard.hadamardEvent t +
    (ResourcePool.singleton (modExpEvent N x t n) +
      (t • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        t.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
          (t / 2) • ResourcePool.singleton (.gate (.builtin "swap"))))

/-- Complete sample events, including every retained-cell measurement and packing. -/
def eventBudget (N x t n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (basisPreparationEvent t n) + unitaryEventBudget N x t n +
    (t • ResourcePool.singleton
      (.measurement { family := "builtin", name := "z", parameters := [2] }) +
      ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packFiniteBits t))))

/-- Parallel initial Hadamards precede the query and the sequential inverse QFT. -/
def unitaryDepth (t : Nat) : Nat :=
  (if t = 0 then 0 else 1) + (1 + (t + t * (t - 1) / 2 + t / 2))

/-- Zero-width sampling still charges preparation, the source query and packing. -/
def depthBudget (t : Nat) : Nat := 1 + unitaryDepth t + t + 1

/-- Independent full capacity: t+n qubits and both actual t-bit result representations. -/
def spaceBudget (t n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then t + n else 0

end

end QuantumAlg.OrderFinding.Sampling
