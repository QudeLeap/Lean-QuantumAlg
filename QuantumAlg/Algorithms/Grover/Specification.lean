/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.Grover.Construction
public import QuantumAlg.Algorithms.Grover.Context
public import QuantumAlg.Algorithms.Grover.Storage
public import QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Elementary.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources

/-!
# The independent complete Grover search problem

The marked predicate, positive-width domain and exact trigonometric success
probability remain the original search contract [dW19, qcnotes.tex:2760-2852].
All budgets are explicit parameter formulas. The measurement cells, packed
result and prepared quantum systems all remain live in the output context.
-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- Source probability determined solely by the width, marked count and iteration count. -/
public def exactSuccessProbability (n t k : Nat) : ENNReal :=
  ENNReal.ofReal
    (Real.sin (((2 : Real) * k + 1) *
      Real.arcsin (Real.sqrt ((t : Real) / ((2 ^ n : Nat) : Real)))) ^ 2)

/-- The independently specified exact probability is a legal lower bound. -/
def successLB (n t k : Nat) : ProbabilityLowerBound where
  value := exactSuccessProbability n t k
  le_one := by
    unfold exactSuccessProbability
    apply ENNReal.ofReal_le_one.mpr
    exact (sq_le_one_iff_abs_le_one _).mpr (Real.abs_sin_le_one _)

/-- Independent native unitary multiplicities in the selected classical execution context. -/
def unitaryBudget {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ResourcePool (model marked) :=
  n • ResourcePool.singleton (model := model marked) (.gate .singleQubit) +
    k • (ResourcePool.singleton (model := model marked) (.oracle .ordinary) +
      ((n • ResourcePool.singleton (model := model marked) (.gate .singleQubit) +
        ZeroReflection.elementaryEventPool (Elementary.oracles marked) n BitWord.model .empty) +
          n • ResourcePool.singleton (model := model marked) (.gate .singleQubit)))

/-- Explicit native unitary, per-system preparation, measurement and packing multiplicities. -/
def eventBudget {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ResourcePool (model marked) :=
  totalQubits n k • ResourcePool.singleton (model := model marked) (.preparation (2 : ℕ+)) +
    unitaryBudget marked k +
    (n • ResourcePool.singleton (model := model marked) (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model marked)
        (.classicalOperation (.nominalEncoding (.packFiniteBits n))))

/-- All search and selected work systems and both result representations remain live. -/
def spaceBudget (n k : Nat) : SpacePool .quantum
  | .classicalBits => 2 * n
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then totalQubits n k else 0

/-- Actual preparation, elementary unitary with parallel H layers, source Z writes and packing. -/
def depthBudget (n k : Nat) : Nat := 1 + Elementary.unitaryDepth n k + n + 1

/-- The returned bits encode an index selected by the same predicate used by the phase oracle. -/
def accepts {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (_initial : Execution.Store pre) (result : CShape.Value (.bits n)) : Prop :=
  match result with
  | .bits outcome => marked (TerminalZMeasure.fullRegisterIndex outcome) = true

/-- Independent complete Grover search contract.

**Input.** A positive width n, a predicate on all 2^n indices with exactly
t > 0 marked indices, and any iteration count k. The borrowed runtime input
is a unit cell with no quantum systems; arbitrary normalized external-reference
extensions are admitted. The search register is prepared internally.
**Output.** The actual n-bit search index is accepted precisely when the
predicate marks its canonical big-endian decoding. Every prepared search and
work system, n finite measurement cells, the packed result and borrowed unit
remain in complete Output after measurement. Only the search wires are measured.
**Resource budget.** One zero preparation per actual qubit,
k phase queries, n+2nk Hadamards outside the reflections, the independently
specified elementary S0 events, n binary Z measurements and one packing operation.
For n=1,2,3 a reflection uses respectively 1,5,10 elementary gates and no work.
For n>=4 it uses 2n+3 single-qubit gates and L(n-1) Toffoli gates,
where L(3)=4, L(4)=10 and L(m)=8(m-3) for m>=5. The total elementary gate count is
n+k(2n+S0Count(n)). A single additional work system is needed only when k>0 and
n>=4; resident and auxiliary capacities both count it and the 2n retained
classical bits. Parallel H layers have unit duration when nonempty; each S0
sequence has duration S0Count(n). The exact complete unit-event depth is
1+delta(n)+k(1+2delta(n)+S0Count(n))+n+1, with delta(n)=1 for positive width.
**Success.** The actual marked-result probability is exactly
sin((2k+1) arcsin(sqrt(t/2^n))) squared. The borrowed input and its full external
reference are restored jointly, independently of the output state promise.
**Source.** The starting state, two reflections and exact marked-event
probability in [dW19, qcnotes.tex:2760-2852]. The native execution additionally
charges its actual basis preparation, Z writes, retained cells and packing.
-/
public def problem {n t : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    Problem (model marked) pre (post n k) (.bits n) where
  valid := fun _ => 0 < n ∧ markedCount marked = t ∧ 0 < t
  initialization := fun _ => True
  accepts := accepts marked
  successLB := successLB n t k
  states := []
  resources :=
    { events := eventBudget marked k, resident := spaceBudget n k, auxiliary := spaceBudget n k }
  depth :=
    { duration := fun _ => 1
      limit := depthBudget n k
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.GroverSearch
