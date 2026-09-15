/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Independent limits for the exact decoded order sample

The original sample is followed by at most one actual shift and one selected
increment for each measured bit. All sampled systems and both source classical
representations remain live beside the added unsigned result word.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

/-- Original sampling events and the independent decoder's two fixed-width coordinates. -/
def eventBudget (N x t n : Nat) : ResourcePool .quantum :=
  Sampling.eventBudget N x t n + ClassicalRoutines.TerminalDecode.envelope t

/-- Independent unit-event upper bound includes every possible selected increment. -/
def depthBudget (t : Nat) : Nat := Sampling.depthBudget t + 2 * t

/-- The source, raw binary results, packed bits and decoded word all remain present. -/
def spaceBudget (t n : Nat) : SpacePool .quantum
  | .classicalBits => 3 * t
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then t + n else 0

end

end QuantumAlg.OrderFinding.Exact
