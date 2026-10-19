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
public def successLB (n t k : Nat) : ProbabilityLowerBound where
  value := exactSuccessProbability n t k
  le_one := by
    unfold exactSuccessProbability
    apply ENNReal.ofReal_le_one.mpr
    exact (sq_le_one_iff_abs_le_one _).mpr (Real.abs_sin_le_one _)

/-- Independent native unitary multiplicities in the selected classical execution context. -/
public def unitaryBudget (n : Nat) (k : Nat) :
    ResourcePool (model n) :=
  n • ResourcePool.singleton (model := model n) (.gate .singleQubit) +
    k • (ResourcePool.singleton (model := model n) (.oracle .ordinary) +
      ((n • ResourcePool.singleton (model := model n) (.gate .singleQubit) +
        ZeroReflection.elementaryEventPool (Elementary.oracles n) n BitWord.model .empty) +
          n • ResourcePool.singleton (model := model n) (.gate .singleQubit)))

/-- Explicit native unitary, per-system preparation, measurement and packing multiplicities. -/
public def eventBudget (n : Nat) (k : Nat) :
    ResourcePool (model n) :=
  totalQubits n k • ResourcePool.singleton (model := model n) (.preparation (2 : ℕ+)) +
    unitaryBudget n k +
    (n • ResourcePool.singleton (model := model n) (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model n)
        (.classicalOperation (.nominalEncoding (.packFiniteBits n))))

/-- All search and selected work systems and both result representations remain live. -/
public def spaceBudget (n k : Nat) : SpacePool .quantum
  | .classicalBits => 2 * n
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then totalQubits n k else 0

/-- Actual preparation, elementary unitary with parallel H layers, source Z writes and packing. -/
public def depthBudget (n k : Nat) : Nat := 1 + Elementary.unitaryDepth n k + n + 1

/-- The returned bits encode an index selected by the same predicate used by the phase oracle. -/
public def accepts {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (_initial : Execution.Store pre) (result : CShape.Value (.bits n)) : Prop :=
  match result with
  | .bits outcome => marked (TerminalZMeasure.fullRegisterIndex outcome) = true

end

end QuantumAlg.GroverSearch
