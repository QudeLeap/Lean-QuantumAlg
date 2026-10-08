/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Schedule

/-!
# Original retry calibration selects the actual complete Shor cycle plan

The original rational failure target selects a positive count. Its first cycle
contains initialization; every subsequent cycle is the complete actual reused
round. No supplied count, source law, prepared bank or resource witness enters
the public calibrated computation.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
  (model : NumberTheory.Factoring.SemiprimeFactorModel N)

/-- A positive symbolic count fixes the full initialized cycle plan on the original context. -/
def countPlan (count : Nat) (positive : 0 < count)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CyclePlan (executionModel (Probability.Input.ofSemiprimeModel model)) base
      (context base noQuantum N count) (.option (.unsignedWord (modulusBits N))) := by
  cases count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ further => exact positivePlan base noQuantum model further duration unitQueries

/-- The same original positive-count code carries its complete physically admissible schedule. -/
def countSchedule (count : Nat) (positive : 0 < count)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (countPlan base noQuantum model count positive duration unitQueries)
      (code base noQuantum N (Probability.Input.ofSemiprimeModel model) count) := by
  cases count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ further => exact positiveSchedule base noQuantum model further duration unitQueries

/-- The real first initialized cycle admits every original normalized caller. -/
theorem countPlan_admitted (count : Nat) (positive : 0 < count)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    {Reference : Register}
    (original : OracleInput
      (executionModel (Probability.Input.ofSemiprimeModel model)).classicalOracles base Reference) :
    (countPlan base noQuantum model count positive duration unitQueries).Admits original := by
  cases count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ further => exact ⟨True.intro, True.intro⟩

/-- The maximum complete-cycle allowance is independent of the positive requested count. -/
theorem count_maximumCycleDepth_le (count : Nat) (positive : 0 < count)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (code base noQuantum N (Probability.Input.ofSemiprimeModel model) count).Path) :
    (countSchedule base noQuantum model count positive duration unitQueries).maximumCycleDepth
      duration path ≤ ResourcePool.weightedCount duration
        (Initialized.firstEnvelope (Probability.Input.ofSemiprimeModel model)) := by
  cases count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ further =>
      exact positive_maximumCycleDepth_le
        base noQuantum model further duration unitQueries path

/-- Original success and the prescribed complete initialized cycles form one specification. -/
def calibratedCycleProblem (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CycleProblem (executionModel (Probability.Input.ofSemiprimeModel model)) base
      (context base noQuantum N (retryCount N budget))
      (.option (.unsignedWord (modulusBits N))) where
  outcome := problem base noQuantum model budget wellFormed duration unitQueries
  plan := countPlan base noQuantum model (retryCount N budget) (retryCount_pos N budget)
    duration unitQueries

/-- One actual budget-selected run supplies correctness, full cycles and real caller admission. -/
def calibratedCycleCertificate (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.CycleSolves (algorithm base noQuantum model budget)
      (calibratedCycleProblem base noQuantum model budget wellFormed duration unitQueries) where
  correctness := shorDeclared_machine_solves base noQuantum model budget wellFormed
    duration unitQueries
  schedule := countSchedule base noQuantum model (retryCount N budget) (retryCount_pos N budget)
    duration unitQueries
  entry := fun _ original _ => countPlan_admitted base noQuantum model
    (retryCount N budget) (retryCount_pos N budget) duration unitQueries original

/-- Calibrated maximum depth includes initialization and one complete actual attempt. -/
theorem calibrated_maximumCycleDepth_le (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (algorithm base noQuantum model budget).run.code.Path) :
    (calibratedCycleCertificate base noQuantum model budget wellFormed
      duration unitQueries).maximumCycleDepth duration path ≤
      ResourcePool.weightedCount duration
        (Initialized.firstEnvelope (Probability.Input.ofSemiprimeModel model)) :=
  count_maximumCycleDepth_le base noQuantum model (retryCount N budget) (retryCount_pos N budget)
    duration unitQueries path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
