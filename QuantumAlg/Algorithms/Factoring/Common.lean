/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.ResourceModel
public import QuantumAlg.Util.Nat

/-!
# RSA factoring resource accounting common vocabulary

This module records the shared failure-budget and retry-accounting structures
used by RSA-style factoring resource adapters.

The vocabulary is shared by the standard Shor route and the Ekera-Hastad
short-DLP route, whose success/retry accounting is kept explicit rather than
hidden inside asymptotic notation [Sho95, source.tex:1124-1148] [EH17,
source.tex:806-842].
-/

@[expose] public section

namespace QuantumAlg
namespace Factoring

/-! ## Generic run and success-accounting vocabulary -/

/-- Rational target failure budget for a success statement. The intended
failure parameter is `failureNumerator / failureDenominator`; well-formedness is
kept as a separate predicate so the data remains computational. -/
structure FailureBudget where
  /-- Numerator of the encoded failure-probability budget. -/
  failureNumerator : ℕ
  /-- Denominator of the encoded failure-probability budget. -/
  failureDenominator : ℕ
deriving DecidableEq

namespace FailureBudget

/-- A rational failure budget is usable when its denominator is positive and
the fraction is at most one. -/
def WellFormed (budget : FailureBudget) : Prop :=
  0 < budget.failureDenominator ∧
    budget.failureNumerator ≤ budget.failureDenominator

/-- Binary failure budget `2^{-k}`, represented as `1 / 2^k`. -/
def binary (k : ℕ) : FailureBudget where
  failureNumerator := 1
  failureDenominator := 2 ^ k

theorem binary_wellFormed (k : ℕ) : (binary k).WellFormed := by
  constructor
  · exact Nat.two_pow_pos k
  · exact Nat.one_le_two_pow

end FailureBudget

/-- Explicit retry multiplier chosen for a target failure budget. A final
resource theorem may use the multiplier directly only when `status` is
`exactCount` or `explicitUpperBound`; otherwise the record is a placeholder with
the concrete replacement criterion carried by `readyForFinalStatement`. -/
structure RetryMultiplierSpec where
  /-- Failure-probability budget controlled by this repetition spec. -/
  failureBudget : FailureBudget
  /-- Concrete number of repeated runs certified by this repetition spec. -/
  runCount : ℕ
  /-- Formula status or readiness status carried by this record. -/
  status : ResourceFormulaStatus
deriving DecidableEq

namespace RetryMultiplierSpec

/-- Retry multiplier whose run count is an exact count for the selected failure
budget. -/
def exactCount (budget : FailureBudget) (runCount : ℕ) : RetryMultiplierSpec where
  failureBudget := budget
  runCount := runCount
  status := .exactCount

/-- Retry multiplier whose run count is a concrete upper-bound function for
the selected failure budget. -/
def explicitUpperBound (budget : FailureBudget) (runCount : ℕ) :
    RetryMultiplierSpec where
  failureBudget := budget
  runCount := runCount
  status := .explicitUpperBound

/-- Whether this retry multiplier is concrete enough for a final theorem
resource metric. -/
def readyForFinalStatement (spec : RetryMultiplierSpec) : Bool :=
  spec.status.admissibleAsExactResource

@[simp] theorem exactCount_status (budget : FailureBudget) (runCount : ℕ) :
    (exactCount budget runCount).status = .exactCount :=
  rfl

@[simp] theorem exactCount_runCount (budget : FailureBudget) (runCount : ℕ) :
    (exactCount budget runCount).runCount = runCount :=
  rfl

@[simp] theorem explicitUpperBound_status
    (budget : FailureBudget) (runCount : ℕ) :
    (explicitUpperBound budget runCount).status = .explicitUpperBound :=
  rfl

@[simp] theorem explicitUpperBound_runCount
    (budget : FailureBudget) (runCount : ℕ) :
    (explicitUpperBound budget runCount).runCount = runCount :=
  rfl

@[simp] theorem exactCount_record_ready
    (budget : FailureBudget) (runCount : ℕ) :
    readyForFinalStatement (exactCount budget runCount) = true :=
  rfl

@[simp] theorem explicitUpperBound_record_ready
    (budget : FailureBudget) (runCount : ℕ) :
    readyForFinalStatement (explicitUpperBound budget runCount) = true :=
  rfl

@[simp] theorem exactCount_ready (budget : FailureBudget) (runCount : ℕ) :
    readyForFinalStatement
      { failureBudget := budget, runCount := runCount,
        status := ResourceFormulaStatus.exactCount } = true :=
  rfl

@[simp] theorem explicitUpperBound_ready (budget : FailureBudget) (runCount : ℕ) :
    readyForFinalStatement
      { failureBudget := budget, runCount := runCount,
        status := ResourceFormulaStatus.explicitUpperBound } = true :=
  rfl

@[simp] theorem sourceBackedEstimate_not_ready
    (budget : FailureBudget) (runCount : ℕ) :
    readyForFinalStatement
      { failureBudget := budget, runCount := runCount,
        status := ResourceFormulaStatus.sourceBackedEstimate } = false :=
  rfl

@[simp] theorem asymptoticOnly_not_ready
    (budget : FailureBudget) (runCount : ℕ) :
    readyForFinalStatement
      { failureBudget := budget, runCount := runCount,
        status := ResourceFormulaStatus.asymptoticOnly } = false :=
  rfl

/-- Well-formed retry accounting for a final exact-resource statement: the
failure budget is a genuine rational budget, the run count is positive, and the
run-count status is an exact count or explicit upper-bound function. -/
structure WellFormed (spec : RetryMultiplierSpec) : Prop where
  failureBudget_wellFormed : spec.failureBudget.WellFormed
  runCount_pos : 0 < spec.runCount
  ready : spec.readyForFinalStatement = true

/-- Source-certified repetition model for a retry multiplier. The fields record
the concrete rational failure probability after `spec.runCount` runs and compare
it with the requested failure budget. The independence/probability derivation is
supplied by the source-facing proof that constructs this certificate. -/
structure RepetitionModel (spec : RetryMultiplierSpec) where
  /-- Numerator of the encoded failure-probability budget. -/
  failureNumerator : ℕ
  /-- Denominator of the encoded failure-probability budget. -/
  failureDenominator : ℕ
  failureDenominator_pos : 0 < failureDenominator
  failure_le_budget :
    failureNumerator * spec.failureBudget.failureDenominator ≤
      spec.failureBudget.failureNumerator * failureDenominator
  runCount_pos : 0 < spec.runCount
  ready : spec.readyForFinalStatement = true

namespace RepetitionModel

/-- The certified repeated-run failure probability is bounded by the target
failure budget. -/
theorem satisfies_failureBudget {spec : RetryMultiplierSpec}
    (model : RepetitionModel spec) :
    model.failureNumerator * spec.failureBudget.failureDenominator ≤
      spec.failureBudget.failureNumerator * model.failureDenominator :=
  model.failure_le_budget

/-- A source-certified repetition model gives the retry fields required by a
final exact-resource theorem once the target budget itself is well-formed. -/
private theorem toWellFormed {spec : RetryMultiplierSpec}
    (model : RepetitionModel spec)
    (hbudget : spec.failureBudget.WellFormed) :
    WellFormed spec where
  failureBudget_wellFormed := hbudget
  runCount_pos := model.runCount_pos
  ready := model.ready

end RepetitionModel

/-- Apply the retry multiplier to a per-run modular-arithmetic profile. Repeated
runs reuse the live footprint and scale counted gates, depth, and classical
work exactly. -/
def successAccountedProfile (spec : RetryMultiplierSpec)
    (perRun : ModularArithmeticResourceProfile) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.repeatSequential spec.runCount perRun

@[simp] theorem successAccountedProfile_eq_repeatSequential
    (spec : RetryMultiplierSpec) (perRun : ModularArithmeticResourceProfile) :
    spec.successAccountedProfile perRun =
      ModularArithmeticResourceProfile.repeatSequential spec.runCount perRun :=
  rfl

theorem successAccountedProfile_toffoliGates
    (spec : RetryMultiplierSpec) (perRun : ModularArithmeticResourceProfile) :
    (spec.successAccountedProfile perRun).toffoliGates =
      spec.runCount * perRun.toffoliGates := by
  cases spec with
  | mk failureBudget runCount status =>
      cases runCount <;> simp [successAccountedProfile, ModularArithmeticResourceProfile.zero]

private theorem successAccountedProfile_toffoliDepth
    (spec : RetryMultiplierSpec) (perRun : ModularArithmeticResourceProfile) :
    (spec.successAccountedProfile perRun).toffoliDepth =
      spec.runCount * perRun.toffoliDepth := by
  cases spec with
  | mk failureBudget runCount status =>
      cases runCount <;> simp [successAccountedProfile, ModularArithmeticResourceProfile.zero]

theorem successAccountedProfile_circuitDepth
    (spec : RetryMultiplierSpec) (perRun : ModularArithmeticResourceProfile) :
    (spec.successAccountedProfile perRun).circuitDepth =
      spec.runCount * perRun.circuitDepth := by
  cases spec with
  | mk failureBudget runCount status =>
      cases runCount <;> simp [successAccountedProfile, ModularArithmeticResourceProfile.zero]

theorem successAccountedProfile_logicalQubits_of_pos
    (spec : RetryMultiplierSpec) (perRun : ModularArithmeticResourceProfile)
    (hpos : 0 < spec.runCount) :
    (spec.successAccountedProfile perRun).logicalQubits = perRun.logicalQubits := by
  cases spec with
  | mk failureBudget runCount status =>
      cases runCount with
      | zero => cases hpos
      | succ _ => rfl

end RetryMultiplierSpec
end Factoring
end QuantumAlg
