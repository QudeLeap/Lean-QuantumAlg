/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.QPE.Basic
public import QuantumAlg.Algorithms.QPE.Context
public import QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.WindowProbability
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Independent native borrowed-eigenstate QPE specification

The original positive-width domain and source eigenstate are unchanged.
Validity constrains the actual local density matrix, so every allowed
extension by an external reference remains in scope. Complete-output storage
and all event budgets below are explicit formulas independent of the run.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

/-- The original pure eigenstate in the supplied physical source coordinates. -/
public def inputPromise {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (state : DensityOperator (pre t n).register) : Prop :=
  ∀ row column, state.matrix row column =
    P.eigenstate (inputBasisEquiv t n row) * star (P.eigenstate (inputBasisEquiv t n column))

/-- The original circular phase-window lower bound, independent of the source unitary. -/
public def successLB : ProbabilityLowerBound where
  value := ENNReal.ofReal (4 / Real.pi ^ 2)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    apply (div_le_one (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [Real.pi_gt_three]

/-- Independent literal native gate, granted query, preparation, Z-read and packing limits. -/
public def eventBudget (n : Nat) (t : Nat) : ResourcePool (model n) :=
  t • ResourcePool.singleton (model := model n) (.preparation (2 : ℕ+)) +
    ((2 * t + 3 * t.choose 2) • ResourcePool.singleton (model := model n)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
      (2 * t.choose 2 + 3 * (t / 2)) • ResourcePool.singleton (model := model n)
        (.gate AlgorithmGate.Coordinate.cnot) +
      (2 ^ t - 1) • ResourcePool.singleton (model := model n)
        (.oracle UnitarySource.Coordinate.controlled)) +
    (t • ResourcePool.singleton (model := model n) (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model n)
        (.classicalOperation (Resource.ClassicalOpLabel.nominalEncoding (.packFiniteBits t))))

/-- Every source and phase system remains resident, along with both classical representations. -/
public def residentBudget (t n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then t + n else 0

/-- The supplied borrowed source is excluded from owned auxiliary storage. -/
public def auxiliaryBudget (t : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then t else 0

/-- Parallel preparation, the complete native word, sequential Z reads and packing depth. -/
public def depthBudget (t : Nat) : Nat :=
  (if t = 0 then 0 else 1) +
    (((if t = 0 then 0 else 1) + (2 ^ t - 1)) +
      (t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3))) + t + 1

/-- Accept the actual stored phase bits exactly in the original circular precision window. -/
public def accepts {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (_initial : Execution.Store (pre t n)) (result : CShape.Value (.bits t)) : Prop :=
  match result with
  | .bits outcome => SuccessfulOutcome P t outcome

end

end QuantumAlg.QuantumPhaseEstimation
