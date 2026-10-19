/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.AmplitudeEstimation.Basic
public import QuantumAlg.Algorithms.AmplitudeEstimation.Context
public import QuantumAlg.Algorithms.AmplitudeEstimation.Storage
public import QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources

/-!
# Independent native amplitude-estimation specification

The source model, interior-probability promise, selected width, and additive
error event retain the original source domain. Budgets below are explicit
parameter formulas, independent of the circuit and all its projections.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

/-- The original legal confidence lower bound. -/
public def successLB (η : Real) (nonnegative : 0 ≤ η) : ProbabilityLowerBound where
  value := ENNReal.ofReal (1 - η)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    linarith

/-- Independent query and elementary-reflection multiplicities for one actual source step. -/
public def stepBudget (n : Nat) : ResourcePool (model n) :=
  ResourcePool.singleton (model := model n) (.oracle .controlledGoodReflection) +
    ResourcePool.singleton (model := model n) (.oracle .inversePreparation) +
    ZeroReflection.controlledElementaryEventPool
      (Elementary.oracles n) n BitWord.model .empty +
    ResourcePool.singleton (model := model n) (.oracle .preparation)

/-- Expanded inverse-Fourier multiplicities preserve the literal selected native coordinates. -/
public def readoutBudget (n : Nat) (t : Nat) :
    ResourcePool (model n) :=
  (t + 3 * t.choose 2) • ResourcePool.singleton (model := model n) (.gate .singleQubit) +
    (2 * t.choose 2 + 3 * (t / 2)) •
      ResourcePool.singleton (model := model n) (.gate .cnot)

/-- Independent native unitary budget in the caller's classical execution context. -/
public def unitaryBudget (n : Nat) (t : Nat) :
    ResourcePool (model n) :=
  ResourcePool.singleton (model := model n) (.oracle .preparation) +
    (t • ResourcePool.singleton (model := model n) (.gate .singleQubit) +
      ((2 ^ t - 1) • stepBudget n + readoutBudget n t))

/-- Independent native unitary, per-system preparation, actual Z writes and bit packing. -/
public def eventBudget (n : Nat) (t : Nat) :
    ResourcePool (model n) :=
  (t + (Elementary.helperWidth t n + n)) •
      ResourcePool.singleton (model := model n) (.preparation (2 : ℕ+)) +
    unitaryBudget n t +
    (t • ResourcePool.singleton (model := model n) (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model n)
        (.classicalOperation (.nominalEncoding (.packFiniteBits t))))

/-- All phase and source systems survive, together with both t-bit classical representations. -/
public def spaceBudget (t n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension =>
      if (2 : ℕ+) = dimension then t + (Elementary.helperWidth t n + n) else 0

/-- The explicit structural unit-event depth includes preparation and every sequential Z write. -/
public def depthBudget (t n : Nat) : Nat := 1 + Elementary.unitaryDepth t n + t + 1

/-- The actual packed phase bits are accepted by the original additive-error predicate. -/
public def accepts {n : Nat} (E : GeneralAmplitudeEstimationInput n) (eps : Real) {t : Nat}
    (_initial : Execution.Store pre) (result : CShape.Value (.bits t)) : Prop :=
  match result with
  | .bits outcome => SuccessfulOutcome E eps outcome

end

end QuantumAlg.AmplitudeEstimation
