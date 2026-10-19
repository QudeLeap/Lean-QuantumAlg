/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Execution
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Base.Marginal
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Independent Hadamard-test problem

The promised local input is the supplied normalized vector in its actual
physical coordinates. The success probability is the source's explicit real
overlap formula. The resource ledger is an independent closed expression;
no bound is projected from the implementation [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

/-- The original source input, with no promise about the external reference. -/
public def inputPromise {width : Nat} (input : NormalizedVector (Qubits width))
    (state : DensityOperator (pre width).register) : Prop :=
  ∀ row column, state.matrix row column =
    input.vec (inputBasisEquiv width row) * star (input.vec (inputBasisEquiv width column))

/-- The explicit probability of the actual zero outcome in the registered source. -/
public def probabilityZero {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : Real :=
  (1 + (inner ℂ input.vec (unitary.applyVec input.vec)).re) / 2

lemma probabilityZero_nonneg {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : 0 ≤ probabilityZero unitary input := by
  rw [probabilityZero, ← hadamardTest_probQubit0_zero (U := unitary) input]
  exact NormalizedVector.probQubit0_nonneg _ _

lemma probabilityZero_le_one {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : probabilityZero unitary input ≤ 1 := by
  have nonnegative := NormalizedVector.probQubit0_nonneg
    ((hadamardTest unitary).apply (NormalizedVector.ket0.tensor input)) 1
  rw [hadamardTest_probQubit0_one] at nonnegative
  dsimp only [probabilityZero]
  linarith

/-- The original exact outcome probability, certified as a probability lower bound. -/
public def successLB {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : ProbabilityLowerBound where
  value := ENNReal.ofReal (probabilityZero unitary input)
  le_one := ENNReal.ofReal_le_one.mpr (probabilityZero_le_one unitary input)

/-- One prepared control, two literal Hadamards, one controlled query, and one actual Z write. -/
public def eventBudget (width : Nat) :
    ResourcePool (model width) :=
  ResourcePool.singleton (model := model width) (.preparation (2 : ℕ+)) +
    (2 • ResourcePool.singleton (model := model width)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
      ResourcePool.singleton (model := model width)
        (.oracle UnitarySource.Coordinate.controlled)) +
    ResourcePool.singleton (model := model width) (.measurement (2 : ℕ+))

/-- All owned quantum systems and the one actual binary result remain resident. -/
public def spaceBudget (width : Nat) : SpacePool .quantum
  | .classicalBits => 1
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then 1 + width else 0

end

end QuantumAlg.HadamardTest
