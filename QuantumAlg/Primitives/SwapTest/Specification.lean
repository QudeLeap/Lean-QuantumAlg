/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.SwapTest.Execution
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Primitives.SwapTest.Execution
import all QuantumAlg.Primitives.SwapTest.Basic
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Primitives.HadamardTest.Basic

/-!
# Independent elementary SWAP-test problem

The exact source probability is unchanged. Its closed native ledger is stated
independently from the candidate execution [BCWdW01, main.tex:287-329].
-/

namespace QuantumAlg.SwapTest

noncomputable section

/-- The original overlap formula for the actual stored one outcome. -/
public def probabilityOne {width : Nat} (left right : NormalizedVector (Qubits width)) : Real :=
  (1 - ‖inner ℂ left right‖ ^ 2) / 2

/-- The supplied physical input has the two original normalized states as its local product. -/
public def inputPromise {width : Nat} (left right : NormalizedVector (Qubits width))
    (state : DensityOperator (pre width).register) : Prop :=
  HadamardTest.inputPromise (left.tensor right) state

lemma probabilityOne_nonneg {width : Nat} (left right : NormalizedVector (Qubits width)) :
    0 ≤ probabilityOne left right := by
  have source := hadamardTest_probQubit0_one (U := swapRegistersOp width)
    (left.tensor right)
  rw [re_inner_swapRegisters] at source
  change 0 ≤ (1 - ‖inner ℂ left right‖ ^ 2) / 2
  exact source ▸ NormalizedVector.probQubit0_nonneg _ _

lemma probabilityOne_le_one {width : Nat} (left right : NormalizedVector (Qubits width)) :
    probabilityOne left right ≤ 1 := by
  dsimp only [probabilityOne]
  nlinarith [sq_nonneg ‖inner ℂ left right‖]

/-- The original exact outcome probability, certified as a probability lower bound. -/
public def successLB {width : Nat} (left right : NormalizedVector (Qubits width)) :
    ProbabilityLowerBound where
  value := ENNReal.ofReal (probabilityOne left right)
  le_one := ENNReal.ofReal_le_one.mpr (probabilityOne_le_one left right)

/-- Independent complete budget: one prepared control, two H, 2n CNOT, n Toffoli, and one Z. -/
public def eventBudget (width : Nat) : ResourcePool model :=
  ResourcePool.singleton (model := model) (.preparation (2 : ℕ+)) +
    (ResourcePool.singleton (model := model) (.gate .singleQubit) 2 +
      (ResourcePool.singleton (model := model) (.gate .cnot) (2 * width) +
        ResourcePool.singleton (model := model) (.gate .toffoli) width)) +
      ResourcePool.singleton (model := model) (.measurement (2 : ℕ+))

/-- All original owned systems, the prepared control, and the retained result remain live. -/
public def spaceBudget (width : Nat) : SpacePool .quantum := HadamardTest.spaceBudget (width +
    width)

end

end QuantumAlg.SwapTest
