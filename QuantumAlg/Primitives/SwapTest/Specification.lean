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
independently from the candidate execution [BCWdW01, main.tex:287-328].
-/

namespace QuantumAlg.SwapTest

noncomputable section

/-- The original overlap formula for the actual stored one outcome. -/
public def probabilityOne {width : Nat} (left right : NormalizedVector (Qubits width)) : Real :=
  (1 - ‖inner ℂ left right‖ ^ 2) / 2

def inputPromise {width : Nat} (left right : NormalizedVector (Qubits width))
    (state : DensityOperator (pre width).register) : Prop :=
  HadamardTest.inputPromise (left.tensor right) state

theorem probabilityOne_nonneg {width : Nat} (left right : NormalizedVector (Qubits width)) :
    0 ≤ probabilityOne left right := by
  have source := hadamardTest_probQubit0_one (U := swapRegistersOp width)
    (left.tensor right)
  rw [re_inner_swapRegisters] at source
  change 0 ≤ (1 - ‖inner ℂ left right‖ ^ 2) / 2
  exact source ▸ NormalizedVector.probQubit0_nonneg _ _

theorem probabilityOne_le_one {width : Nat} (left right : NormalizedVector (Qubits width)) :
    probabilityOne left right ≤ 1 := by
  dsimp only [probabilityOne]
  nlinarith [sq_nonneg ‖inner ℂ left right‖]

def successLB {width : Nat} (left right : NormalizedVector (Qubits width)) :
    ProbabilityLowerBound where
  value := ENNReal.ofReal (probabilityOne left right)
  le_one := ENNReal.ofReal_le_one.mpr (probabilityOne_le_one left right)

/-- Closed elementary event budget: one prepared control, two H, 3n Toffoli, and one Z. -/
def eventBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.ofList
    ([.preparation { family := "builtin", name := "computational-basis", parameters := [1, 2, 0] },
      .gate (.builtin "hadamard")] ++
      List.replicate (3 * width) (.gate (.builtin "toffoli")) ++
      [.gate (.builtin "hadamard"),
        .measurement { family := "builtin", name := "z", parameters := [2] }])

/-- All original owned systems, the prepared control, and the retained result remain live. -/
def spaceBudget (width : Nat) : SpacePool .quantum := HadamardTest.spaceBudget (width + width)

/-- Elementary measured SWAP test on the original pair of normalized inputs.

**Input.** Two normalized $n$-qubit vectors in the two owned supplied registers.
Every reference extension with this promised local product state is allowed.
**Output.** The actual binary Z result, both complete original words, and the
internally prepared control. The measured quantum systems remain live.
**Resource budget.** One control preparation, two Hadamards, $3n$ actual Toffoli
gates and one Z measurement. Unit-duration depth is at most $3n+4$. Resident
and owned auxiliary space are each at most $2n+1$ qubits and one classical bit.
Exactly one qubit is newly allocated; no additional work register is needed.
**Success.** The stored one outcome has exact probability
$(1-|\langle\psi|\phi\rangle|^2)/2$. All borrowed/reference correlations
are restored. The owned input words may change.
**Source.** The measured controlled-swap construction and its exact probability
[BCWdW01, main.tex:287-328]. The elementary native counts follow the explicit
three-Toffoli implementation of each controlled bit exchange.
-/
public def problem {width : Nat} (left right : NormalizedVector (Qubits width)) :
    Problem .quantum (pre width) (post width) (.finite 2) where
  valid := fun state => inputPromise left right state.quantumMarginal
  accepts := fun _initial result => result = .finite 1
  successLB := successLB left right
  states := []
  resources :=
    { events := eventBudget width
      resident := spaceBudget width
      auxiliary := spaceBudget width }
  depth := .quantum (fun _event => 1) (3 * width + 4)

end

end QuantumAlg.SwapTest
