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
def inputPromise {width : Nat} (input : NormalizedVector (Qubits width))
    (state : DensityOperator (pre width).register) : Prop :=
  ∀ row column, state.matrix row column =
    input.vec (inputBasisEquiv width row) * star (input.vec (inputBasisEquiv width column))

/-- The explicit probability of the actual zero outcome in the registered source. -/
public def probabilityZero {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : Real :=
  (1 + (inner ℂ input.vec (unitary.applyVec input.vec)).re) / 2

theorem probabilityZero_nonneg {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : 0 ≤ probabilityZero unitary input := by
  rw [probabilityZero, ← hadamardTest_probQubit0_zero (U := unitary) input]
  exact NormalizedVector.probQubit0_nonneg _ _

theorem probabilityZero_le_one {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : probabilityZero unitary input ≤ 1 := by
  have nonnegative := NormalizedVector.probQubit0_nonneg
    ((hadamardTest unitary).apply (NormalizedVector.ket0.tensor input)) 1
  rw [hadamardTest_probQubit0_one] at nonnegative
  dsimp only [probabilityZero]
  linarith

def successLB {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) : ProbabilityLowerBound where
  value := ENNReal.ofReal (probabilityZero unitary input)
  le_one := ENNReal.ofReal_le_one.mpr (probabilityZero_le_one unitary input)

/-- One prepared control, two literal Hadamards, one controlled query, and one actual Z write. -/
def eventBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.ofList
    [.preparation { family := "builtin", name := "computational-basis", parameters := [1, 2, 0] },
      .gate (.builtin "hadamard"), UnitarySource.controlledEvent width,
      .gate (.builtin "hadamard"),
      .measurement { family := "builtin", name := "z", parameters := [2] }]

/-- All owned quantum systems and the one actual binary result remain resident. -/
def spaceBudget (width : Nat) : SpacePool .quantum
  | .classicalBits => 1
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then 1 + width else 0

/-- Native Hadamard test on the original normalized input.

**Input.** A supplied normalized $n$-qubit vector and controlled access to its
source unitary. The original word is owned because the test may change it.
Every normalized external extension of the promised local state is allowed.
**Output.** The actual binary Z outcome in a finite classical cell, together
with the entire original word and the internally prepared control qubit.
**Resource budget.** One control preparation, two Hadamards, one controlled
source query and one Z measurement; unit-event depth at most five. Resident
and owned auxiliary capacities are $n+1$ qubits and one classical bit. Exactly
one quantum system is newly allocated.
**Success.** The stored zero outcome has probability
$(1+\operatorname{Re}\langle\psi|U|\psi\rangle)/2$. All borrowed observations
and the external reference are restored jointly; measured quantum systems
remain live without an additional state promise.
**Source.** The controlled-unitary construction and real-overlap outcome in
[AJL06, qf2.tex:625-645]. The explicit native ledger follows that same circuit.
-/
public def problem {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (input : NormalizedVector (Qubits width)) :
    Problem .quantum (pre width) (post width) (.finite 2) where
  valid := fun state => inputPromise input state.quantumMarginal
  accepts := fun _initial result => result = .finite 0
  successLB := successLB unitary input
  states := []
  resources :=
    { events := eventBudget width
      resident := spaceBudget width
      auxiliary := spaceBudget width }
  depth := .quantum (fun _event => 1) 5

end

end QuantumAlg.HadamardTest
