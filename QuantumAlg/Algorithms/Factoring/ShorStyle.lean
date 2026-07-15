/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Algorithms.OrderFinding.Probability
public import QuantumAlg.Primitives.MAU.ModularExponentiation
public import QuantumAlg.Util.ShorFactoring

/-!
# Shor-style RSA factoring resource adapters

This module records exact natural-number adapters for the standard
order-finding route to RSA-style factoring resource statements.

The route is the Shor order-finding reduction to factoring [Sho95,
source.tex:1124-1148]. The resource-envelope bridge is kept separate from
Gidney-Ekera concrete RSA estimates, which are source-backed estimates until an
exact or explicit-upper-bound pass discharges them [GE19, main.tex:459-522].
-/

@[expose] public section

namespace QuantumAlg
namespace Factoring

/-! ### Shor-style logical workspace accounting -/

namespace ShorStyle

/-- Shape assumption for the modular exponentiation register used by the
Shor-style order-finding route: an `n`-bit modulus register and a `2n`-bit
phase/exponent register. -/
structure ModExpRegisterShape (n : ℕ)
    (params : ModularExponentiation.ResourceParameters) : Prop where
  modulusBits_eq : params.modulusBits = n
  exponentWidth_eq : params.exponentWidth = 2 * n

/-- Public baseline logical-qubit term for Shor-style modular exponentiation:
`2n` exponent qubits plus an `n`-qubit residue register. -/
def baselineLogicalQubits (n : ℕ) : ℕ :=
  3 * n

/-- Exact addend which turns the reusable modular-exponentiation profile into a
`3n + addend` logical-qubit statement. Under the standard register shape,
`baseline_le_toProfile_logicalQubits` proves the subtraction is exact. -/
def modularExponentiationWorkspaceAddend (n : ℕ)
    (params : ModularExponentiation.ResourceParameters) : ℕ :=
  params.toProfile.logicalQubits - baselineLogicalQubits n

/-- The live register footprint has the expected `3n` baseline plus explicit
control and clean-work registers under the Shor-style register shape. -/
theorem registerFootprint_logicalQubits_eq_baseline_addend {n : ℕ}
    {params : ModularExponentiation.ResourceParameters}
    (hshape : ModExpRegisterShape n params) :
    params.registerFootprint.logicalQubits =
      baselineLogicalQubits n + params.controlQubits + params.workQubits := by
  simp [baselineLogicalQubits, ModularExponentiation.ResourceParameters.registerFootprint,
    hshape.modulusBits_eq, hshape.exponentWidth_eq]
  omega

/-- The reusable modular-exponentiation profile is at least the `3n` baseline
under the Shor-style register shape. -/
theorem baseline_le_toProfile_logicalQubits {n : ℕ}
    {params : ModularExponentiation.ResourceParameters}
    (hshape : ModExpRegisterShape n params) :
    baselineLogicalQubits n ≤ params.toProfile.logicalQubits := by
  rw [ModularExponentiation.ResourceParameters.toProfile_logicalQubits]
  have hregister :
      baselineLogicalQubits n ≤ params.registerFootprint.logicalQubits := by
    rw [registerFootprint_logicalQubits_eq_baseline_addend hshape]
    omega
  exact le_trans hregister (Nat.le_max_left _ _)

/-- Exact `3n + addend` decomposition for the modular-exponentiation logical
footprint used by the Shor-style factoring resource statement. -/
theorem toProfile_logicalQubits_eq_baseline_plus_workspaceAddend {n : ℕ}
    {params : ModularExponentiation.ResourceParameters}
    (hshape : ModExpRegisterShape n params) :
    params.toProfile.logicalQubits =
      baselineLogicalQubits n + modularExponentiationWorkspaceAddend n params := by
  unfold modularExponentiationWorkspaceAddend
  have hle := baseline_le_toProfile_logicalQubits hshape
  omega

/-- If the reusable modular-exponentiation profile is bounded by a concrete
logical-qubit function, the same function bounds the `3n + addend` statement. -/
theorem baseline_plus_workspaceAddend_le_of_toProfile_le {n upperBound : ℕ}
    {params : ModularExponentiation.ResourceParameters}
    (hshape : ModExpRegisterShape n params)
    (hbound : params.toProfile.logicalQubits ≤ upperBound) :
    baselineLogicalQubits n + modularExponentiationWorkspaceAddend n params ≤ upperBound := by
  rw [← toProfile_logicalQubits_eq_baseline_plus_workspaceAddend hshape]
  exact hbound

/-- The workspace addend is exactly the modular-exponentiation component maximum
minus the public `3n` baseline. This exposes the finite recurrence expression
used by the reusable MAU component. -/
private theorem modularExponentiationWorkspaceAddend_eq_componentMax_sub_baseline
    (n : ℕ) (params : ModularExponentiation.ResourceParameters) :
    modularExponentiationWorkspaceAddend n params =
      max params.registerFootprint.logicalQubits
          (max params.powerPrecomputeProfile.logicalQubits
            params.scheduledMultiplications.logicalQubits) -
        baselineLogicalQubits n := by
  simp [modularExponentiationWorkspaceAddend]

/-- A reusable modular-exponentiation source-bound certificate transfers a
source-facing logical-qubit bound into the Shor-style `3n + addend` shape. -/
theorem workspaceAddend_le_of_modexpSourceBoundCertificate {n upperBound : ℕ}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    (hshape : ModExpRegisterShape n modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical : modexpBounds.toProfile.logicalQubits ≤ upperBound) :
    baselineLogicalQubits n + modularExponentiationWorkspaceAddend n modexp ≤
      upperBound := by
  exact baseline_plus_workspaceAddend_le_of_toProfile_le hshape
    ((modexpCert.supportsUpperBound).logicalQubits_le.trans hlogical)

/-! ### Final-statement readiness -/

/-- Readiness certificate for replacing every Shor-style private-statement
resource placeholder by an exact count or explicit upper-bound function. -/
structure FinalResourceReadiness (retry : RetryMultiplierSpec) : Prop where
  retryReady : retry.readyForFinalStatement = true

namespace FinalResourceReadiness

/-- A retry multiplier whose status is admissible as an exact-resource metric
is ready for the final Shor-style support theorem. -/
private theorem of_retry_status_ready {retry : RetryMultiplierSpec}
    (h : retry.status.admissibleAsExactResource = true) :
    FinalResourceReadiness retry where
  retryReady := by
    simpa [RetryMultiplierSpec.readyForFinalStatement] using h

/-- A source-certified repetition model supplies the exact or explicit-upper-
bound retry status needed by the final Shor-style support theorem. -/
private theorem of_repetitionModel {retry : RetryMultiplierSpec}
    (model : RetryMultiplierSpec.RepetitionModel retry) :
    FinalResourceReadiness retry where
  retryReady := model.ready

/-- A retry multiplier recorded as a concrete upper-bound function is ready for
the final Shor-style resource theorem. -/
theorem of_explicitUpperBound
    (budget : FailureBudget) (runCount : ℕ) :
    FinalResourceReadiness
      (RetryMultiplierSpec.explicitUpperBound budget runCount) where
  retryReady := RetryMultiplierSpec.explicitUpperBound_record_ready budget runCount

/-- A retry multiplier recorded as an exact run count is ready for the final
Shor-style resource theorem. -/
theorem of_exactCount
    (budget : FailureBudget) (runCount : ℕ) :
    FinalResourceReadiness
      (RetryMultiplierSpec.exactCount budget runCount) where
  retryReady := RetryMultiplierSpec.exactCount_record_ready budget runCount

/-- A placeholder retry multiplier cannot be used as a final resource theorem
field. -/
private theorem not_of_retry_placeholder (budget : FailureBudget) :
    ¬ FinalResourceReadiness
      { failureBudget := budget, runCount := 1, status := .sourceBackedEstimate } := by
  intro h
  cases h.retryReady

end FinalResourceReadiness

/-! ### Shor-style retry selector -/

namespace EtaRetrySelector

/-- Failure budgets usable by the Shor eta retry selector.  The extra positive
numerator condition excludes the impossible zero-failure target; finite Shor
repetition can target a positive eta, with the repeated-run probability algebra
proved separately [Sho95, source.tex:1647-1663]. -/
def WellFormed (budget : FailureBudget) : Prop :=
  budget.WellFormed ∧ 0 < budget.failureNumerator

/-- Shor-style eta retry selector.  For a target failure budget `a / b`, the
selector uses `b` repeated source runs and records the count as an explicit
upper-bound function.  The probability proof that this count meets the eta
budget is kept in the retry-amplification layer [Sho95, source.tex:1647-1663]. -/
def spec (budget : FailureBudget) : RetryMultiplierSpec :=
  RetryMultiplierSpec.explicitUpperBound budget budget.failureDenominator

@[simp] theorem spec_failureBudget (budget : FailureBudget) :
    (spec budget).failureBudget = budget :=
  rfl

@[simp] theorem spec_runCount (budget : FailureBudget) :
    (spec budget).runCount = budget.failureDenominator :=
  rfl

@[simp] theorem spec_ready (budget : FailureBudget) :
    (spec budget).readyForFinalStatement = true :=
  rfl

theorem runCount_pos {budget : FailureBudget} (hbudget : WellFormed budget) :
    0 < (spec budget).runCount :=
  hbudget.1.1

/-- The selected retry multiplier is concrete enough for final resource
statements and carries the public failure-budget side conditions needed by the
later amplification proof. -/
theorem toRetryMultiplierSpecWellFormed {budget : FailureBudget}
    (hbudget : WellFormed budget) :
    RetryMultiplierSpec.WellFormed (spec budget) where
  failureBudget_wellFormed := hbudget.1
  runCount_pos := runCount_pos hbudget
  ready := spec_ready budget

/-- The Shor eta selector supplies the final-resource retry readiness
certificate used by resource statements. -/
theorem finalResourceReadiness (budget : FailureBudget) :
    FinalResourceReadiness (spec budget) where
  retryReady := spec_ready budget

/-- Record-level repetition model for the Shor eta selector.  The finite
repetition probability comparison is supplied explicitly here; the
source-facing independent-trial bound can instantiate this constructor. -/
def repetitionModel (budget : FailureBudget)
    {failureNumerator failureDenominator : ℕ}
    (failureDenominator_pos : 0 < failureDenominator)
    (failure_le_budget :
      failureNumerator * budget.failureDenominator ≤
        budget.failureNumerator * failureDenominator)
    (hbudget : WellFormed budget) :
    RetryMultiplierSpec.RepetitionModel (spec budget) where
  failureNumerator := failureNumerator
  failureDenominator := failureDenominator
  failureDenominator_pos := failureDenominator_pos
  failure_le_budget := failure_le_budget
  runCount_pos := runCount_pos hbudget
  ready := spec_ready budget

end EtaRetrySelector

/-! ### Repeated-trial failure-bound algebra -/

namespace RepeatedTrialFailureBound

/-- Failure numerator after `retry.runCount` independent source runs when the
one-run failure bound is represented by `oneRun`. This is only the explicit
natural-number field; the proof that the source runs instantiate this bound is
kept as a separate theorem obligation [Sho95, source.tex:1647-1663]. -/
def numerator (oneRun : FailureBudget) (retry : RetryMultiplierSpec) : ℕ :=
  oneRun.failureNumerator ^ retry.runCount

/-- Failure denominator after `retry.runCount` independent source runs when the
one-run failure bound is represented by `oneRun` [Sho95,
source.tex:1647-1663]. -/
def denominator (oneRun : FailureBudget) (retry : RetryMultiplierSpec) : ℕ :=
  oneRun.failureDenominator ^ retry.runCount

theorem denominator_pos (oneRun : FailureBudget) (retry : RetryMultiplierSpec)
    (honeRun : oneRun.WellFormed) :
    0 < denominator oneRun retry :=
  pow_pos honeRun.1 retry.runCount

theorem numerator_le_denominator (oneRun : FailureBudget)
    (retry : RetryMultiplierSpec) (honeRun : oneRun.WellFormed) :
    numerator oneRun retry ≤ denominator oneRun retry :=
  Nat.pow_le_pow_left honeRun.2 retry.runCount

/-- If a one-run failure budget is at most one half, then the powered failure
numerator times the elementary `2^k` denominator is bounded by the powered
one-run denominator. This is the arithmetic core used to calibrate the Shor
eta selector after the source proof has reduced independent repeated failure to
power fields [Sho95, source.tex:1647-1663]. -/
theorem numerator_mul_two_pow_le_denominator_of_atMostHalf
    (oneRun : FailureBudget) (k : ℕ)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator) :
    oneRun.failureNumerator ^ k * 2 ^ k ≤
      oneRun.failureDenominator ^ k := by
  have hpow :
      (2 * oneRun.failureNumerator) ^ k ≤
        oneRun.failureDenominator ^ k :=
    Nat.pow_le_pow_left honeHalf k
  simpa [mul_pow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hpow

/-- A denominator-sized repetition count is enough to replace the `2^k`
denominator when a one-run failure budget is at most one half. This remains an
explicit natural-number upper-bound proof, not an asymptotic estimate [Sho95,
source.tex:1647-1663]. -/
theorem numerator_mul_runCount_le_denominator_of_atMostHalf
    (oneRun : FailureBudget) (k : ℕ)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator) :
    oneRun.failureNumerator ^ k * k ≤
      oneRun.failureDenominator ^ k := by
  have hk : k ≤ 2 ^ k := Nat.le_of_lt k.lt_two_pow_self
  have hmul :
      oneRun.failureNumerator ^ k * k ≤
        oneRun.failureNumerator ^ k * 2 ^ k :=
    Nat.mul_le_mul_left (oneRun.failureNumerator ^ k) hk
  exact hmul.trans
    (numerator_mul_two_pow_le_denominator_of_atMostHalf oneRun k honeHalf)

/-- If the repeated-run failure field is bounded by the requested public
failure budget, then the complementary success field is at least `1 - eta` in
the exact cross-multiplied natural-number form used by the public endpoint
[Sho95, source.tex:1647-1663]. -/
theorem successAtLeastOneMinusFailureBudget (oneRun : FailureBudget)
    (retry : RetryMultiplierSpec)
    (hbudget : retry.failureBudget.WellFormed)
    (honeRun : oneRun.WellFormed)
    (hrepeated :
      numerator oneRun retry * retry.failureBudget.failureDenominator ≤
        retry.failureBudget.failureNumerator * denominator oneRun retry) :
    (retry.failureBudget.failureDenominator -
        retry.failureBudget.failureNumerator) *
        denominator oneRun retry ≤
      retry.failureBudget.failureDenominator *
        (denominator oneRun retry - numerator oneRun retry) := by
  have hfailure_le_one :
      numerator oneRun retry ≤ denominator oneRun retry :=
    numerator_le_denominator oneRun retry honeRun
  nlinarith [Nat.sub_add_cancel hbudget.2, Nat.sub_add_cancel hfailure_le_one]

/-- If the repeated-failure field is at most one third, then the complementary
success field is at least two thirds in the endpoint's cross-multiplied natural
number form [Sho95, source.tex:1647-1663]. -/
theorem successAtLeastTwoThirds_of_failureAtMostOneThird
    (oneRun : FailureBudget) (retry : RetryMultiplierSpec)
    (honeRun : oneRun.WellFormed)
    (hthird : 3 * numerator oneRun retry ≤ denominator oneRun retry) :
    2 * denominator oneRun retry ≤
      3 * (denominator oneRun retry - numerator oneRun retry) := by
  have hfailure_le_one :
      numerator oneRun retry ≤ denominator oneRun retry :=
    numerator_le_denominator oneRun retry honeRun
  omega

/-- Build the generic repetition model from explicit one-run failure fields and
the selected repeated-failure comparison. This theorem records the exact
natural-number fields; it does not hide the independent-trial proof, which is
the `hrepeated` premise [Sho95, source.tex:1647-1663]. -/
def repetitionModel (oneRun : FailureBudget) (retry : RetryMultiplierSpec)
    (hretry : RetryMultiplierSpec.WellFormed retry)
    (honeRun : oneRun.WellFormed)
    (hrepeated :
      numerator oneRun retry * retry.failureBudget.failureDenominator ≤
        retry.failureBudget.failureNumerator * denominator oneRun retry) :
    RetryMultiplierSpec.RepetitionModel retry where
  failureNumerator := numerator oneRun retry
  failureDenominator := denominator oneRun retry
  failureDenominator_pos := denominator_pos oneRun retry honeRun
  failure_le_budget := hrepeated
  runCount_pos := hretry.runCount_pos
  ready := hretry.ready

end RepeatedTrialFailureBound

namespace EtaRetrySelector

/-- Arithmetic calibration for the Shor eta selector. If the source route gives
a one-run failure bound at most one half, then the selector's concrete
`budget.failureDenominator` repetitions make the powered repeated-failure
field no larger than the target eta budget. The source independence/repetition
argument is represented by the powered fields from `RepeatedTrialFailureBound`;
this theorem only proves the remaining natural-number inequality [Sho95,
source.tex:1647-1663]. -/
theorem repeatedFailure_le_budget_of_oneRun_atMostHalf
    (oneRun budget : FailureBudget)
    (hbudget : WellFormed budget)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator) :
    RepeatedTrialFailureBound.numerator oneRun (spec budget) *
        budget.failureDenominator ≤
      budget.failureNumerator *
        RepeatedTrialFailureBound.denominator oneRun (spec budget) := by
  have hbase :
      oneRun.failureNumerator ^ budget.failureDenominator *
          budget.failureDenominator ≤
        oneRun.failureDenominator ^ budget.failureDenominator :=
    RepeatedTrialFailureBound.numerator_mul_runCount_le_denominator_of_atMostHalf
      oneRun budget.failureDenominator honeHalf
  have htarget_pos : 0 < budget.failureNumerator := hbudget.2
  have hscale :
      oneRun.failureDenominator ^ budget.failureDenominator ≤
        budget.failureNumerator *
          oneRun.failureDenominator ^ budget.failureDenominator := by
    simpa [Nat.one_mul] using
      Nat.mul_le_mul_right (oneRun.failureDenominator ^ budget.failureDenominator)
        (Nat.succ_le_of_lt htarget_pos)
  simpa [RepeatedTrialFailureBound.numerator,
    RepeatedTrialFailureBound.denominator, spec] using hbase.trans hscale

/-- If the public failure budget is at most one third, then the repeated
failure field selected by the Shor eta retry selector is at most one third.
The proof combines the selector's repeated-failure bound with the public
budget inequality, so later endpoints need not accept a separate two-thirds
certificate [Sho95, source.tex:1647-1663]. -/
theorem repeatedFailure_atMostOneThird_of_budget_atMostOneThird
    (oneRun budget : FailureBudget)
    (hbudget : WellFormed budget)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator)
    (hbudgetThird :
      3 * budget.failureNumerator ≤ budget.failureDenominator) :
    3 * RepeatedTrialFailureBound.numerator oneRun (spec budget) ≤
      RepeatedTrialFailureBound.denominator oneRun (spec budget) := by
  have hrep :=
    repeatedFailure_le_budget_of_oneRun_atMostHalf oneRun budget hbudget
      honeHalf
  have hden_pos : 0 < budget.failureDenominator := hbudget.1.1
  have hmul :
      (3 * RepeatedTrialFailureBound.numerator oneRun (spec budget)) *
          budget.failureDenominator ≤
        RepeatedTrialFailureBound.denominator oneRun (spec budget) *
          budget.failureDenominator := by
    nlinarith
  exact le_of_mul_le_mul_right hmul hden_pos

/-- Public-budget two-thirds success calibration for the Shor eta selector.
The caller supplies only public budget inequalities; the repeated-failure and
two-thirds fields are derived internally [Sho95, source.tex:1647-1663]. -/
theorem successAtLeastTwoThirds_of_budget_atMostOneThird
    (oneRun budget : FailureBudget)
    (hbudget : WellFormed budget)
    (honeRun : oneRun.WellFormed)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator)
    (hbudgetThird :
      3 * budget.failureNumerator ≤ budget.failureDenominator) :
    2 * RepeatedTrialFailureBound.denominator oneRun (spec budget) ≤
      3 * (RepeatedTrialFailureBound.denominator oneRun (spec budget) -
        RepeatedTrialFailureBound.numerator oneRun (spec budget)) :=
  RepeatedTrialFailureBound.successAtLeastTwoThirds_of_failureAtMostOneThird
    oneRun (spec budget) honeRun
    (repeatedFailure_atMostOneThird_of_budget_atMostOneThird oneRun budget
      hbudget honeHalf hbudgetThird)

/-- Build the selector's repetition model from an explicit one-run failure
budget and the source-facing at-most-half bound. The construction keeps the
one-run bound as a premise and uses `RepeatedTrialFailureBound` for the powered
failure fields, rather than hiding selector calibration in an opaque
certificate [Sho95, source.tex:1647-1663]. -/
def calibratedRepetitionModel (oneRun budget : FailureBudget)
    (hbudget : WellFormed budget)
    (honeRun : oneRun.WellFormed)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator) :
    RetryMultiplierSpec.RepetitionModel (spec budget) :=
  RepeatedTrialFailureBound.repetitionModel oneRun (spec budget)
    (toRetryMultiplierSpecWellFormed hbudget) honeRun
    (repeatedFailure_le_budget_of_oneRun_atMostHalf oneRun budget hbudget honeHalf)

end EtaRetrySelector

/-! ### Classical post-processing operation count -/

/-- Classical operation counts for one Shor-style factoring run, separated by
the shared operation taxonomy. The profile includes order-recovery
post-processing, gcd/EEA-style factor extraction, modular exponent checks, and
factor-validation work. -/
structure ClassicalPostProcessingParameters where
  /-- Classical work for recovering the order from an order-finding sample. -/
  orderRecovery : NumberTheoreticOperationProfile
  /-- Classical work for extracting a factor from the recovered order. -/
  factorExtraction : NumberTheoreticOperationProfile
  /-- Classical checks attached to modular-exponentiation data. -/
  modularExponentChecks : ModularFieldOperationProfile
  /-- Classical validation work for candidate factors. -/
  factorValidation : BitIntegerOperationProfile
  /-- Classical lookup/precomputation/control work for the route. -/
  lookupAndControl : GroupControlOperationProfile
deriving DecidableEq

namespace ClassicalPostProcessingParameters

/-- Structured classical arithmetic profile for a single Shor-style run. -/
def perRunProfile (params : ClassicalPostProcessingParameters) :
    ClassicalArithmeticProfile where
  bitInteger := params.factorValidation
  numberTheoretic :=
    NumberTheoreticOperationProfile.sequential params.orderRecovery
      params.factorExtraction
  modularField := params.modularExponentChecks
  groupControl := params.lookupAndControl

@[simp] theorem perRunProfile_bitInteger
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.bitInteger = params.factorValidation :=
  rfl

@[simp] theorem perRunProfile_numberTheoretic
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.numberTheoretic =
      NumberTheoreticOperationProfile.sequential params.orderRecovery
        params.factorExtraction :=
  rfl

@[simp] theorem perRunProfile_modularField
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.modularField = params.modularExponentChecks :=
  rfl

@[simp] theorem perRunProfile_groupControl
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.groupControl = params.lookupAndControl :=
  rfl

/-- Scalar classical operation count for one Shor-style run. -/
def perRunTotal (params : ClassicalPostProcessingParameters) : ℕ :=
  params.perRunProfile.total

@[simp] theorem perRunTotal_eq (params : ClassicalPostProcessingParameters) :
    params.perRunTotal = params.perRunProfile.total :=
  rfl

/-- Success-accounted structured classical arithmetic profile. -/
def successAccountedProfile (retry : RetryMultiplierSpec)
    (params : ClassicalPostProcessingParameters) : ClassicalArithmeticProfile :=
  ClassicalArithmeticProfile.scale retry.runCount params.perRunProfile

@[simp] theorem successAccountedProfile_total
    (retry : RetryMultiplierSpec) (params : ClassicalPostProcessingParameters) :
    (successAccountedProfile retry params).total =
      retry.runCount * params.perRunTotal := by
  simp [successAccountedProfile, perRunTotal]

/-- Replace the classical component of a modular-arithmetic profile with the
success-accounted Shor-style classical post-processing count. -/
def attachToProfile (retry : RetryMultiplierSpec)
    (params : ClassicalPostProcessingParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    ModularArithmeticResourceProfile :=
  { quantumProfile with
    classicalArithmetic := successAccountedProfile retry params }

@[simp] theorem attachToProfile_classicalArithmetic
    (retry : RetryMultiplierSpec) (params : ClassicalPostProcessingParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    (attachToProfile retry params quantumProfile).classicalArithmetic =
      successAccountedProfile retry params :=
  rfl

theorem attachToProfile_classicalOps
    (retry : RetryMultiplierSpec) (params : ClassicalPostProcessingParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    (attachToProfile retry params quantumProfile).toResourceProfile.classicalOps =
      retry.runCount * params.perRunTotal := by
  simp [attachToProfile, ModularArithmeticResourceProfile.toResourceProfile]

@[simp] theorem attachToProfile_toffoliGates
    (retry : RetryMultiplierSpec) (params : ClassicalPostProcessingParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    (attachToProfile retry params quantumProfile).toffoliGates =
      quantumProfile.toffoliGates :=
  rfl

@[simp] theorem attachToProfile_circuitDepth
    (retry : RetryMultiplierSpec) (params : ClassicalPostProcessingParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    (attachToProfile retry params quantumProfile).circuitDepth =
      quantumProfile.circuitDepth :=
  rfl

/-! ### Canonical Shor-style upper-bound instance -/

/-- Per-run classical post-processing upper bound for the Shor-style factoring
route, counted in the structured operation taxonomy. The bound counts one
continued-fraction step per denominator bit plus one reconstruction, two
gcd/EEA-style factor extractions, two square-and-multiply modular exponent
checks with at most `n` squarings and `n` multiplications each, and a fixed
factor-validation budget. -/
def shorPerRunUpperBound (n : ℕ) : ClassicalPostProcessingParameters where
  orderRecovery :=
    { NumberTheoreticOperationProfile.zero with
      continuedFractions := 2 * n + 1
      rationalReconstructions := 1 }
  factorExtraction :=
    { NumberTheoreticOperationProfile.zero with
      gcds := 2
      extendedEuclidean := 2 }
  modularExponentChecks :=
    { ModularFieldOperationProfile.zero with
      multiplications := 2 * n
      squarings := 2 * n }
  factorValidation :=
    { BitIntegerOperationProfile.zero with
      comparisons := 4
      divisions := 2
      modularReductions := 2 }
  lookupAndControl := GroupControlOperationProfile.zero

/-- Order-recovery part of the Shor-style per-run classical bound. -/
@[simp] theorem shorPerRunUpperBound_orderRecovery_total (n : ℕ) :
    (shorPerRunUpperBound n).orderRecovery.total = 2 * n + 2 := by
  simp [shorPerRunUpperBound, NumberTheoreticOperationProfile.total,
    NumberTheoreticOperationProfile.zero]

/-- GCD/EEA factor-extraction part of the Shor-style per-run classical bound. -/
@[simp] theorem shorPerRunUpperBound_factorExtraction_total (n : ℕ) :
    (shorPerRunUpperBound n).factorExtraction.total = 4 := by
  simp [shorPerRunUpperBound, NumberTheoreticOperationProfile.total,
    NumberTheoreticOperationProfile.zero]

/-- Modular-exponentiation check part of the Shor-style per-run classical bound. -/
@[simp] theorem shorPerRunUpperBound_modularExponentChecks_total (n : ℕ) :
    (shorPerRunUpperBound n).modularExponentChecks.total = 4 * n := by
  simp [shorPerRunUpperBound, ModularFieldOperationProfile.total,
    ModularFieldOperationProfile.zero]
  omega

/-- Bit/integer factor-validation part of the Shor-style per-run classical
bound. -/
@[simp] theorem shorPerRunUpperBound_factorValidation_total (n : ℕ) :
    (shorPerRunUpperBound n).factorValidation.total = 8 := by
  simp [shorPerRunUpperBound, BitIntegerOperationProfile.total,
    BitIntegerOperationProfile.zero]

/-- Scalar form of the canonical per-run Shor-style classical upper bound. -/
def shorPerRunUpperBoundTotal (n : ℕ) : ℕ :=
  6 * n + 14

/-- Taxonomy-level breakdown of the Shor-style per-run classical bound before it
is projected to a scalar count. -/
private theorem shorPerRunUpperBound_taxonomy_breakdown (n : ℕ) :
    (shorPerRunUpperBound n).perRunTotal =
      (2 * n + 2) + 4 + 4 * n + 8 := by
  simp [shorPerRunUpperBound, perRunTotal, perRunProfile,
    ClassicalArithmeticProfile.total, BitIntegerOperationProfile.zero,
    NumberTheoreticOperationProfile.zero, ModularFieldOperationProfile.zero,
    GroupControlOperationProfile.zero,
    NumberTheoreticOperationProfile.total, NumberTheoreticOperationProfile.sequential,
    ModularFieldOperationProfile.total, BitIntegerOperationProfile.total,
    GroupControlOperationProfile.total]
  omega

theorem shorPerRunUpperBound_total (n : ℕ) :
    (shorPerRunUpperBound n).perRunTotal = shorPerRunUpperBoundTotal n := by
  simp [shorPerRunUpperBound, shorPerRunUpperBoundTotal, perRunTotal, perRunProfile,
    ClassicalArithmeticProfile.total, BitIntegerOperationProfile.zero,
    NumberTheoreticOperationProfile.zero, ModularFieldOperationProfile.zero,
    GroupControlOperationProfile.zero,
    NumberTheoreticOperationProfile.total, NumberTheoreticOperationProfile.sequential,
    ModularFieldOperationProfile.total, BitIntegerOperationProfile.total,
    GroupControlOperationProfile.total]
  omega

/-- The canonical per-run classical count as an explicit upper-bound function
of the RSA modulus bit length parameter. -/
def shorPerRunUpperBoundSpec : ClassicalCountSpec ℕ :=
  ClassicalCountSpec.explicitUpperBound shorPerRunUpperBoundTotal

@[simp] theorem shorPerRunUpperBoundSpec_kind :
    shorPerRunUpperBoundSpec.kind = ClassicalCountKind.explicitUpperBound :=
  rfl

@[simp] theorem shorPerRunUpperBoundSpec_count (n : ℕ) :
    shorPerRunUpperBoundSpec.count n = shorPerRunUpperBoundTotal n :=
  rfl

/-- Success-accounted scalar classical upper bound for a concrete retry
multiplier. -/
def shorSuccessAccountedUpperBoundTotal
    (retry : RetryMultiplierSpec) (n : ℕ) : ℕ :=
  retry.runCount * shorPerRunUpperBoundTotal n

/-- Success-accounted explicit upper-bound function consumed by the private
RSA resource theorem once the retry multiplier itself is ready. -/
def shorSuccessAccountedUpperBoundSpec (retry : RetryMultiplierSpec) :
    ClassicalCountSpec ℕ :=
  ClassicalCountSpec.explicitUpperBound
    (fun n => shorSuccessAccountedUpperBoundTotal retry n)

@[simp] theorem shorSuccessAccountedUpperBoundSpec_kind
    (retry : RetryMultiplierSpec) :
    (shorSuccessAccountedUpperBoundSpec retry).kind =
      ClassicalCountKind.explicitUpperBound :=
  rfl

@[simp] theorem shorSuccessAccountedUpperBoundSpec_count
    (retry : RetryMultiplierSpec) (n : ℕ) :
    (shorSuccessAccountedUpperBoundSpec retry).count n =
      shorSuccessAccountedUpperBoundTotal retry n :=
  rfl

private theorem shorSuccessAccountedUpperBound_total
    (retry : RetryMultiplierSpec) (n : ℕ) :
    (successAccountedProfile retry (shorPerRunUpperBound n)).total =
      shorSuccessAccountedUpperBoundTotal retry n := by
  rw [successAccountedProfile_total, shorPerRunUpperBound_total]
  rfl

/-- The success-accounted Shor-style classical count is a concrete explicit
upper-bound function, so it can replace the private-statement classical
arithmetic placeholder once the retry multiplier itself is accepted. -/
private theorem shorClassicalCount_replacesPlaceholder
    (retry : RetryMultiplierSpec) (n : ℕ) :
    (shorSuccessAccountedUpperBoundSpec retry).kind =
        ClassicalCountKind.explicitUpperBound ∧
      (shorSuccessAccountedUpperBoundSpec retry).count n =
        retry.runCount * (6 * n + 14) := by
  simp [shorSuccessAccountedUpperBoundSpec, shorSuccessAccountedUpperBoundTotal,
    shorPerRunUpperBoundTotal]

/-- Attach the canonical Shor-style classical upper bound to an existing
success-accounted quantum resource profile. -/
def attachShorClassicalUpperBound (retry : RetryMultiplierSpec) (n : ℕ)
    (quantumProfile : ModularArithmeticResourceProfile) :
    ModularArithmeticResourceProfile :=
  attachToProfile retry (shorPerRunUpperBound n) quantumProfile

theorem attachShorClassicalUpperBound_classicalOps
    (retry : RetryMultiplierSpec) (n : ℕ)
    (quantumProfile : ModularArithmeticResourceProfile) :
    (attachShorClassicalUpperBound retry n quantumProfile).toResourceProfile.classicalOps =
      shorSuccessAccountedUpperBoundTotal retry n := by
  rw [attachShorClassicalUpperBound, attachToProfile_classicalOps,
    shorPerRunUpperBound_total]
  rfl

end ClassicalPostProcessingParameters

/-! ### Exact-resource support for public baseline fields -/

/-- Exact support profile for the Shor-style RSA factoring resource theorem.
It repeats the per-run modular-exponentiation profile according to the selected
retry multiplier, then attaches the canonical classical post-processing upper
bound. -/
def exactSupportProfile (retry : RetryMultiplierSpec) (n : ℕ)
    (params : ModularExponentiation.ResourceParameters) :
    ModularArithmeticResourceProfile :=
  ClassicalPostProcessingParameters.attachShorClassicalUpperBound retry n
    (retry.successAccountedProfile params.toProfile)

/-- Per-run quantum circuit used by the Shor-style RSA route. Retry and
classical post-processing are route-level accounting layers; this circuit is
the single modular-exponentiation run whose profile is scaled by the retry
certificate. -/
noncomputable def perRunQuantumCircuit {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ModularExponentiation.ResourceParameters) :
    Circuit (ModularExponentiation.register m N) :=
  ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u params

@[simp] theorem perRunQuantumCircuit_resources {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ModularExponentiation.ResourceParameters) :
    (perRunQuantumCircuit (m := m) u params).resources = params.toResourceProfile :=
  rfl

@[simp] theorem perRunQuantumCircuit_depth {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ModularExponentiation.ResourceParameters) :
    (perRunQuantumCircuit (m := m) u params).depth =
      params.toProfile.circuitDepth :=
  rfl

@[simp] theorem perRunQuantumCircuit_queryDepth {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ModularExponentiation.ResourceParameters) :
    (perRunQuantumCircuit (m := m) u params).queryDepth =
      params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for the Shor-style per-run quantum circuit. -/
theorem perRunQuantumCircuit_apply_ket {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ModularExponentiation.ResourceParameters)
    (x : ModularExponentiation.Data m N) :
    Circuit.apply (perRunQuantumCircuit (m := m) u params)
      (PureState.ket (R := ModularExponentiation.register m N) x :
        StateVector (ModularExponentiation.register m N)) =
      (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
        StateVector (ModularExponentiation.register m N)) :=
  ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_ket u params x

/-- Shor-style route accounting is based on retry-scaling the exact profile of
the same per-run quantum circuit. -/
private theorem exactSupportProfile_quantumProfile_eq_retryScale
    (retry : RetryMultiplierSpec) (n : ℕ)
    (params : ModularExponentiation.ResourceParameters) :
    (ClassicalPostProcessingParameters.attachShorClassicalUpperBound retry n
      (retry.successAccountedProfile params.toProfile)) =
      exactSupportProfile retry n params :=
  rfl

/-- Circuit/resource projection package for the Shor-style per-run quantum
component. Retry and classical counts remain explicit route-level certificates,
while the quantum run itself is a typed circuit. -/
noncomputable def perRunQuantumCircuitResourceCorrectWitness {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ModularExponentiation.ResourceParameters) :
    ResourceCorrectWitness (R := ModularExponentiation.register m N)
      (∀ x : ModularExponentiation.Data m N,
        Circuit.apply (perRunQuantumCircuit (m := m) u params)
          (PureState.ket (R := ModularExponentiation.register m N) x :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
            StateVector (ModularExponentiation.register m N)))
      ((perRunQuantumCircuit (m := m) u params).resources = params.toResourceProfile ∧
        (perRunQuantumCircuit (m := m) u params).depth =
          params.toProfile.circuitDepth ∧
        (perRunQuantumCircuit (m := m) u params).queryDepth =
          params.toProfile.oracleQueries) := by
  exact
    { circuit := perRunQuantumCircuit (m := m) u params
      correctness := fun x => perRunQuantumCircuit_apply_ket u params x
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Success-accounted Shor-style quantum circuit obtained by repeating the same
per-run modular-exponentiation circuit. Classical post-processing is attached
separately in `exactSupportProfile`; this circuit carries the retry-scaled
quantum profile. -/
noncomputable def successAccountedQuantumCircuit {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters) :
    Circuit (ModularExponentiation.register m N) :=
  Circuit.iterate retry.runCount (perRunQuantumCircuit (m := m) u params)

@[simp] theorem successAccountedQuantumCircuit_resources {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters) :
    (successAccountedQuantumCircuit (m := m) u retry params).resources =
      ResourceProfile.scale retry.runCount params.toResourceProfile :=
  rfl

@[simp] theorem successAccountedQuantumCircuit_depth {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters) :
    (successAccountedQuantumCircuit (m := m) u retry params).depth =
      retry.runCount * params.toProfile.circuitDepth :=
  rfl

@[simp] theorem successAccountedQuantumCircuit_queryDepth {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters) :
    (successAccountedQuantumCircuit (m := m) u retry params).queryDepth =
      retry.runCount * params.toProfile.oracleQueries :=
  rfl

/-- The retry-scaled Shor-style quantum circuit projects to the same coarse
resource tuple as the retry-scaled modular-arithmetic profile. -/
theorem successAccountedQuantumCircuit_resources_eq_profile_projection
    {N m : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters) :
    (successAccountedQuantumCircuit (m := m) u retry params).resources =
      (retry.successAccountedProfile params.toProfile).toResourceProfile := by
  rw [successAccountedQuantumCircuit_resources,
    RetryMultiplierSpec.successAccountedProfile_eq_repeatSequential,
    ModularArithmeticResourceProfile.toResourceProfile_repeatSequential]
  simp [ModularExponentiation.ResourceParameters.toResourceProfile_eq]

/-- Matrix semantics of the success-accounted Shor-style quantum circuit: the
same per-run circuit is repeated exactly `retry.runCount` times. -/
theorem successAccountedQuantumCircuit_matrix {N m : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters) :
    ((successAccountedQuantumCircuit (m := m) u retry params).matrix :
        HilbertOperator (ModularExponentiation.register m N)) =
      ((perRunQuantumCircuit (m := m) u params).matrix :
        HilbertOperator (ModularExponentiation.register m N)) ^ retry.runCount := by
  simp [successAccountedQuantumCircuit]

/-- Resource-correct witness for the retry-scaled Shor-style quantum part.
This keeps the route's repeated quantum work tied to one `Circuit`; classical
post-processing and public formula comparison remain theorem-level accounting
certificates. -/
noncomputable def successAccountedQuantumCircuitResourceCorrectWitness
    {N m : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters) :
    ResourceCorrectWitness (R := ModularExponentiation.register m N)
      (((successAccountedQuantumCircuit (m := m) u retry params).matrix :
          HilbertOperator (ModularExponentiation.register m N)) =
        ((perRunQuantumCircuit (m := m) u params).matrix :
          HilbertOperator (ModularExponentiation.register m N)) ^ retry.runCount)
      ((successAccountedQuantumCircuit (m := m) u retry params).resources =
          (retry.successAccountedProfile params.toProfile).toResourceProfile ∧
        (successAccountedQuantumCircuit (m := m) u retry params).depth =
          retry.runCount * params.toProfile.circuitDepth ∧
        (successAccountedQuantumCircuit (m := m) u retry params).queryDepth =
          retry.runCount * params.toProfile.oracleQueries) := by
  exact
    { circuit := successAccountedQuantumCircuit (m := m) u retry params
      correctness := successAccountedQuantumCircuit_matrix u retry params
      resources := by
        exact ⟨successAccountedQuantumCircuit_resources_eq_profile_projection
          u retry params, rfl, rfl⟩ }

/-- Public-facing baseline fields as concrete natural-number bounds. Source
formula instantiation supplies these values; this bridge only proves that a
stronger exact-resource support profile implies the fields. -/
structure PublicBaselineBounds where
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ℕ
  /-- Gate-count component for Toffoli gates. -/
  toffoliGates : ℕ
  /-- Depth component for circuit depth. -/
  circuitDepth : ℕ
  /-- Classical-operation count component. -/
  classicalOps : ℕ
deriving DecidableEq

namespace PublicBaselineBounds

/-- Public baseline fields together with the per-run base quantities from which
the success-accounted fields are formed. -/
structure WithPerRun where
  /-- Per-run logical-qubit count before success accounting. -/
  perRunLogicalQubits : ℕ
  /-- Per-run Toffoli-gate count before success accounting. -/
  perRunToffoliGates : ℕ
  /-- Per-run circuit-depth count before success accounting. -/
  perRunCircuitDepth : ℕ
  /-- Per-run classical-operation count before success accounting. -/
  perRunClassicalOps : ℕ
  /-- Success-accounted aggregate resource bounds. -/
  successAccounted : PublicBaselineBounds
deriving DecidableEq

/-- Public-bound parameters for the Shor-style RSA resource expression after
replacing `log n` by an explicit natural-number upper bound. -/
structure FormulaParameters where
  /-- Bit length of the RSA modulus. -/
  modulusBits : ℕ
  /-- Explicit upper bound for the logarithmic modulus-bit factor. -/
  logModulusBitsUpperBound : ℕ
  /-- Certified workspace addend for the modular-exponentiation profile. -/
  workspaceAddendBound : ℕ
deriving DecidableEq

namespace FormulaParameters

/-- Natural-number upper bound for `3n + exact logarithmic workspace addend`. -/
def logicalQubitBound (params : FormulaParameters) : ℕ :=
  3 * params.modulusBits + params.workspaceAddendBound

/-- Natural-number upper bound for `0.4n^3 + 0.0006n^3 log n`. -/
def toffoliBaseBound (params : FormulaParameters) : ℕ :=
  QuantumAlg.Nat.ceilDiv (2 * params.modulusBits ^ 3) 5 +
    QuantumAlg.Nat.ceilDiv
      (3 * params.modulusBits ^ 3 * params.logModulusBitsUpperBound) 5000

/-- Natural-number upper bound for `600n^2 + n^2 log n`. -/
def circuitDepthBaseBound (params : FormulaParameters) : ℕ :=
  600 * params.modulusBits ^ 2 +
    params.modulusBits ^ 2 * params.logModulusBitsUpperBound

/-- Success-accounted public bounds obtained by multiplying the per-sample
quantum base bounds by the exact retry multiplier and attaching the explicit
classical upper-bound function. -/
def toPublicBaselineBounds
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    PublicBaselineBounds where
  logicalQubits := params.logicalQubitBound
  toffoliGates := retry.runCount * params.toffoliBaseBound
  circuitDepth := retry.runCount * params.circuitDepthBaseBound
  classicalOps := ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
    retry params.modulusBits

/-- Per-run and success-accounted Shor-style formula fields in one record. -/
def toPublicBaselineBoundsWithPerRun
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    WithPerRun where
  perRunLogicalQubits := params.logicalQubitBound
  perRunToffoliGates := params.toffoliBaseBound
  perRunCircuitDepth := params.circuitDepthBaseBound
  perRunClassicalOps :=
    ClassicalPostProcessingParameters.shorPerRunUpperBoundTotal params.modulusBits
  successAccounted := params.toPublicBaselineBounds retry

@[simp] theorem toPublicBaselineBounds_logicalQubits
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    (params.toPublicBaselineBounds retry).logicalQubits =
      params.logicalQubitBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_toffoliGates
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    (params.toPublicBaselineBounds retry).toffoliGates =
      retry.runCount * params.toffoliBaseBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_circuitDepth
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    (params.toPublicBaselineBounds retry).circuitDepth =
      retry.runCount * params.circuitDepthBaseBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_classicalOps
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    (params.toPublicBaselineBounds retry).classicalOps =
      ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
        retry params.modulusBits :=
  rfl

/-- The public baseline classical field is exactly the Shor-style concrete
success-accounted classical count at the modulus bit length. -/
private theorem toPublicBaselineBounds_classicalOps_eq_shorClassicalCountSpec
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    (params.toPublicBaselineBounds retry).classicalOps =
      (ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundSpec retry).count
        params.modulusBits :=
  rfl

@[simp] theorem toPublicBaselineBoundsWithPerRun_successAccounted
    (params : FormulaParameters) (retry : RetryMultiplierSpec) :
    (params.toPublicBaselineBoundsWithPerRun retry).successAccounted =
      params.toPublicBaselineBounds retry :=
  rfl

end FormulaParameters

/-- Named public-bound envelope for the Shor-style RSA baseline formula.  The
fields are public theorem variables: modulus bit length, a concrete logarithmic
upper-bound value, and the modular-exponentiation workspace addend.  The
internal formula-parameter record is reconstructed from these fields when
connecting to reusable support theorems [Sho95, source.tex:1124-1148] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
structure Envelope where
  /-- Bit length of the RSA modulus. -/
  modulusBits : ℕ
  /-- Explicit upper bound for the logarithmic modulus-bit factor. -/
  logModulusBitsUpperBound : ℕ
  /-- Certified workspace addend for the modular-exponentiation profile. -/
  workspaceAddendBound : ℕ
deriving DecidableEq

namespace Envelope

/-- Convert the public envelope to the internal formula-parameter record used by
the support layer. -/
def internalParams (envelope : Envelope) : FormulaParameters where
  modulusBits := envelope.modulusBits
  logModulusBitsUpperBound := envelope.logModulusBitsUpperBound
  workspaceAddendBound := envelope.workspaceAddendBound

/-- Success-accounted public baseline fields selected by the envelope and retry
selector. -/
def toPublicBaselineBounds (envelope : Envelope)
    (retry : RetryMultiplierSpec) : PublicBaselineBounds :=
  envelope.internalParams.toPublicBaselineBounds retry

@[simp] theorem internalParams_modulusBits (envelope : Envelope) :
    envelope.internalParams.modulusBits = envelope.modulusBits :=
  rfl

@[simp] theorem internalParams_logModulusBitsUpperBound (envelope : Envelope) :
    envelope.internalParams.logModulusBitsUpperBound =
      envelope.logModulusBitsUpperBound :=
  rfl

@[simp] theorem internalParams_workspaceAddendBound (envelope : Envelope) :
    envelope.internalParams.workspaceAddendBound =
      envelope.workspaceAddendBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_logicalQubits
    (envelope : Envelope) (retry : RetryMultiplierSpec) :
    (envelope.toPublicBaselineBounds retry).logicalQubits =
      3 * envelope.modulusBits + envelope.workspaceAddendBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_toffoliGates
    (envelope : Envelope) (retry : RetryMultiplierSpec) :
    (envelope.toPublicBaselineBounds retry).toffoliGates =
      retry.runCount *
        (QuantumAlg.Nat.ceilDiv (2 * envelope.modulusBits ^ 3) 5 +
          QuantumAlg.Nat.ceilDiv
            (3 * envelope.modulusBits ^ 3 *
              envelope.logModulusBitsUpperBound) 5000) :=
  rfl

@[simp] theorem toPublicBaselineBounds_circuitDepth
    (envelope : Envelope) (retry : RetryMultiplierSpec) :
    (envelope.toPublicBaselineBounds retry).circuitDepth =
      retry.runCount *
        (600 * envelope.modulusBits ^ 2 +
          envelope.modulusBits ^ 2 * envelope.logModulusBitsUpperBound) :=
  rfl

@[simp] theorem toPublicBaselineBounds_classicalOps
    (envelope : Envelope) (retry : RetryMultiplierSpec) :
    (envelope.toPublicBaselineBounds retry).classicalOps =
      ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
        retry envelope.modulusBits :=
  rfl

end Envelope

end PublicBaselineBounds

/-- Formula-bound form of `workspaceAddend_le_of_modexpSourceBoundCertificate`:
if the modular-exponentiation component is bounded by the Shor public logical
qubit field, then its exact addend is bounded by the formula's addend field. -/
theorem workspaceAddend_le_formulaBound_of_modexpSourceBoundCertificate
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound) :
    modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
      params.workspaceAddendBound := by
  have hsum :
      baselineLogicalQubits params.modulusBits +
          modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.logicalQubitBound :=
    workspaceAddend_le_of_modexpSourceBoundCertificate hshape modexpCert hlogical
  simp [PublicBaselineBounds.FormulaParameters.logicalQubitBound,
    baselineLogicalQubits] at hsum
  omega

/-- The exact support profile is strong enough for a public baseline record when
each exact field is bounded by the corresponding public-facing field. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits
  toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates
  circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth
  classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps

/-- Source-backed certificate for the private Shor-style exact-resource support
theorem. It records that placeholder statuses have been resolved and that the
exact support profile is bounded by the public-facing fields. -/
structure SourceBoundCertificate
    (retry : RetryMultiplierSpec)
    (params : ModularExponentiation.ResourceParameters)
    (bounds : PublicBaselineBounds) : Prop where
  readiness : FinalResourceReadiness retry
  retry_pos : 0 < retry.runCount
  logicalQubits_le :
    baselineLogicalQubits params.modulusBits +
      modularExponentiationWorkspaceAddend params.modulusBits params ≤
        bounds.logicalQubits
  toffoliGates_le :
    retry.runCount * params.toProfile.toffoliGates ≤ bounds.toffoliGates
  circuitDepth_le :
    retry.runCount * params.toProfile.circuitDepth ≤ bounds.circuitDepth
  classicalOps_le :
    ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
      retry params.modulusBits ≤ bounds.classicalOps

@[simp] theorem exactSupportProfile_logicalQubits_of_pos {n : ℕ}
    {retry : RetryMultiplierSpec}
    {params : ModularExponentiation.ResourceParameters}
    (hshape : ModExpRegisterShape n params) (hpos : 0 < retry.runCount) :
    (exactSupportProfile retry n params).logicalQubits =
      baselineLogicalQubits n + modularExponentiationWorkspaceAddend n params := by
  rw [exactSupportProfile,
    ClassicalPostProcessingParameters.attachShorClassicalUpperBound,
    ClassicalPostProcessingParameters.attachToProfile,
    RetryMultiplierSpec.successAccountedProfile_logicalQubits_of_pos retry
      params.toProfile hpos,
    toProfile_logicalQubits_eq_baseline_plus_workspaceAddend hshape]

@[simp] theorem exactSupportProfile_toffoliGates
    (retry : RetryMultiplierSpec) (n : ℕ)
    (params : ModularExponentiation.ResourceParameters) :
    (exactSupportProfile retry n params).toffoliGates =
      retry.runCount * params.toProfile.toffoliGates := by
  rw [exactSupportProfile,
    ClassicalPostProcessingParameters.attachShorClassicalUpperBound,
    ClassicalPostProcessingParameters.attachToProfile,
    RetryMultiplierSpec.successAccountedProfile_toffoliGates]

@[simp] theorem exactSupportProfile_circuitDepth
    (retry : RetryMultiplierSpec) (n : ℕ)
    (params : ModularExponentiation.ResourceParameters) :
    (exactSupportProfile retry n params).circuitDepth =
      retry.runCount * params.toProfile.circuitDepth := by
  rw [exactSupportProfile,
    ClassicalPostProcessingParameters.attachShorClassicalUpperBound,
    ClassicalPostProcessingParameters.attachToProfile,
    RetryMultiplierSpec.successAccountedProfile_circuitDepth]

theorem exactSupportProfile_classicalOps
    (retry : RetryMultiplierSpec) (n : ℕ)
    (params : ModularExponentiation.ResourceParameters) :
    (exactSupportProfile retry n params).toResourceProfile.classicalOps =
      ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal retry n := by
  rw [exactSupportProfile,
    ClassicalPostProcessingParameters.attachShorClassicalUpperBound_classicalOps]

/-- Package the per-run modular-exponentiation fields and the corresponding
success-accounted Shor-style route fields. This is the local statement used by
the exact-resource support theorem to keep per-run and repeated-run quantities
separate. -/
private theorem exactSupportProfile_perRun_and_successAccounted_fields {n : ℕ}
    {retry : RetryMultiplierSpec}
    {params : ModularExponentiation.ResourceParameters}
    (hshape : ModExpRegisterShape n params) (hpos : 0 < retry.runCount) :
    params.toProfile.logicalQubits =
        baselineLogicalQubits n + modularExponentiationWorkspaceAddend n params ∧
      (exactSupportProfile retry n params).logicalQubits =
        baselineLogicalQubits n + modularExponentiationWorkspaceAddend n params ∧
      (exactSupportProfile retry n params).toffoliGates =
        retry.runCount * params.toProfile.toffoliGates ∧
      (exactSupportProfile retry n params).circuitDepth =
        retry.runCount * params.toProfile.circuitDepth ∧
      (exactSupportProfile retry n params).toResourceProfile.classicalOps =
        ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal retry n := by
  exact
    ⟨toProfile_logicalQubits_eq_baseline_plus_workspaceAddend hshape,
      exactSupportProfile_logicalQubits_of_pos hshape hpos,
      exactSupportProfile_toffoliGates retry n params,
      exactSupportProfile_circuitDepth retry n params,
      exactSupportProfile_classicalOps retry n params⟩

/-- Bridge theorem from the exact-resource support profile to public baseline
fields. The hypotheses are explicit fieldwise upper bounds supplied by the
source-backed public baseline formula; no asymptotic resource term appears in
the bridge. -/
theorem exactSupportProfile_supportsPublicBaseline {n : ℕ}
    {retry : RetryMultiplierSpec}
    {params : ModularExponentiation.ResourceParameters}
    {bounds : PublicBaselineBounds}
    (hshape : ModExpRegisterShape n params) (hpos : 0 < retry.runCount)
    (hlogical :
      baselineLogicalQubits n + modularExponentiationWorkspaceAddend n params ≤
        bounds.logicalQubits)
    (htoffoli :
      retry.runCount * params.toProfile.toffoliGates ≤ bounds.toffoliGates)
    (hdepth :
      retry.runCount * params.toProfile.circuitDepth ≤ bounds.circuitDepth)
    (hclassical :
      ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal retry n ≤
        bounds.classicalOps) :
    SupportsPublicBaseline (exactSupportProfile retry n params) bounds where
  logicalQubits_le := by
    rw [exactSupportProfile_logicalQubits_of_pos hshape hpos]
    exact hlogical
  toffoliGates_le := by
    rw [exactSupportProfile_toffoliGates]
    exact htoffoli
  circuitDepth_le := by
    rw [exactSupportProfile_circuitDepth]
    exact hdepth
  classicalOps_le := by
    rw [exactSupportProfile_classicalOps]
    exact hclassical

/-- A source-bound certificate discharges the private exact-resource support
obligations for the public Shor-style baseline fields. -/
theorem SourceBoundCertificate.supportsPublicBaseline
    {retry : RetryMultiplierSpec}
    {params : ModularExponentiation.ResourceParameters}
    {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate retry params bounds)
    (hshape : ModExpRegisterShape params.modulusBits params) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits params) bounds :=
  exactSupportProfile_supportsPublicBaseline hshape cert.retry_pos
    cert.logicalQubits_le cert.toffoliGates_le cert.circuitDepth_le cert.classicalOps_le

namespace SourceBoundCertificate

/-- A Shor-style source-bound certificate exposes that every retry multiplier
placeholder has been resolved before it can feed the final private resource
statement. -/
private theorem finalResourceReady
    {retry : RetryMultiplierSpec}
    {params : ModularExponentiation.ResourceParameters}
    {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate retry params bounds) :
    retry.readyForFinalStatement = true :=
  cert.readiness.retryReady

end SourceBoundCertificate

/-- Named private support endpoint for the exact-resource Shor-style RSA
factoring statement. It packages the final-status check together with the
fieldwise exact-profile support for the public baseline formulas following
Shor's order-finding route [Sho95, source.tex:1124-1148] and the
Gidney-Ekera resource envelope [GE19, main.tex:459-522]. -/
structure PrivateResourceStatementWitness
    (retry : RetryMultiplierSpec)
    (modexp : ModularExponentiation.ResourceParameters)
    (params : PublicBaselineBounds.FormulaParameters) : Prop where
  readiness : FinalResourceReadiness retry
  supportsPublicBaseline :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry)

/-- Build the Shor-style source-bound certificate from explicit natural-number
public baseline functions. The logarithmic source term has already been
replaced by `logModulusBitsUpperBound`, so the remaining hypotheses are
ordinary fieldwise upper bounds for one modular-exponentiation run. This is the
Lean-side upper-bound version of the Shor order-finding route and GE19 formula
envelope [Sho95, source.tex:1124-1148] [GE19, main.tex:70-79, 211-216,
1785-1788]. -/
theorem SourceBoundCertificate.of_formulaBounds
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hbits : modexp.modulusBits = params.modulusBits)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SourceBoundCertificate retry modexp (params.toPublicBaselineBounds retry) where
  readiness := readiness
  retry_pos := hpos
  logicalQubits_le := by
    rw [hbits]
    simp [PublicBaselineBounds.FormulaParameters.logicalQubitBound, baselineLogicalQubits]
    omega
  toffoliGates_le := Nat.mul_le_mul_left retry.runCount htoffoli
  circuitDepth_le := Nat.mul_le_mul_left retry.runCount hdepth
  classicalOps_le := by
    rw [hbits]
    exact le_rfl

/-- Direct endpoint from explicit Shor-style public formula bounds to support
of the public baseline record. This packages the source-bound certificate and
the exact support-profile bridge into one theorem for later theorem-node
realization [Sho95, source.tex:1124-1148] [GE19, main.tex:70-79, 211-216,
1785-1788]. -/
theorem exactSupportProfile_supportsPublicBaseline_of_formulaBounds
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry) := by
  have cert :
      SourceBoundCertificate retry modexp (params.toPublicBaselineBounds retry) :=
    SourceBoundCertificate.of_formulaBounds readiness hpos hshape.modulusBits_eq
      hworkspace htoffoli hdepth
  have hshape' : ModExpRegisterShape modexp.modulusBits modexp := by
    refine ⟨rfl, ?_⟩
    simpa [← hshape.modulusBits_eq] using hshape.exponentWidth_eq
  simpa [hshape.modulusBits_eq] using cert.supportsPublicBaseline hshape'

/-- Private endpoint from explicit Shor-style public formula bounds. The
result is stronger than the public-facing statement because it retains the
resolved retry status and the exact support-profile comparison [Sho95,
source.tex:1124-1148] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
theorem PrivateResourceStatementWitness.of_formulaBounds
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness retry modexp params where
  readiness := readiness
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_of_formulaBounds readiness hpos
      hshape hworkspace htoffoli hdepth

/-- Direct Shor-style support from a reusable modular-exponentiation component
certificate. The component certificate supplies a composed public-bound profile;
the remaining hypotheses compare that composed profile with the Shor-style
formula fields. -/
theorem exactSupportProfile_supportsPublicBaseline_of_modexpCertificate
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (_readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry) := by
  have hupper := modexpCert.supportsUpperBound
  refine exactSupportProfile_supportsPublicBaseline hshape hpos ?_ ?_ ?_ ?_
  · rw [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds_logicalQubits]
    rw [← toProfile_logicalQubits_eq_baseline_plus_workspaceAddend hshape]
    exact hupper.logicalQubits_le.trans hlogical
  · rw [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds_toffoliGates]
    exact Nat.mul_le_mul_left retry.runCount
      (hupper.toffoliGates_le.trans htoffoli)
  · rw [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds_circuitDepth]
    exact Nat.mul_le_mul_left retry.runCount
      (hupper.circuitDepth_le.trans hdepth)
  · rw [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds_classicalOps]

/-- Private endpoint from a reusable modular-exponentiation component
certificate. This is the non-circuit support form of the exact-resource target. -/
theorem PrivateResourceStatementWitness.of_modexpCertificate
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness retry modexp params where
  readiness := readiness
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_of_modexpCertificate readiness
      hpos hshape modexpCert hlogical htoffoli hdepth

/-- Shor-style support from a reusable modular-exponentiation component
certificate, with the formula workspace-addend obligation derived explicitly
from the component logical-qubit bound. -/
theorem exactSupportProfile_supportsPublicBaseline_of_modexpWorkspaceCertificate
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry) := by
  have hupper := modexpCert.supportsUpperBound
  exact exactSupportProfile_supportsPublicBaseline_of_formulaBounds readiness hpos hshape
    (workspaceAddend_le_formulaBound_of_modexpSourceBoundCertificate hshape
      modexpCert hlogical)
    (hupper.toffoliGates_le.trans htoffoli)
    (hupper.circuitDepth_le.trans hdepth)

/-- Private endpoint from a reusable modular-exponentiation component
certificate, deriving the workspace-addend formula obligation before packaging
the exact-resource Shor-style witness. -/
theorem PrivateResourceStatementWitness.of_modexpWorkspaceCertificate
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness retry modexp params where
  readiness := readiness
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_of_modexpWorkspaceCertificate
      readiness hpos hshape modexpCert hlogical htoffoli hdepth

/-- Source-backed modular-exponentiation resource package for the Shor-style RSA
route.  The package keeps the reusable modular-exponentiation
`SourceBoundCertificate` as the gatekeeper for the quantum resource profile; the
endpoint no longer accepts raw modular-exponentiation resource fields together
with reflexive fieldwise inequalities [VBE95, 9511018.tex:372-416] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
structure SourceBackedModexpResourcePackage
    (params : PublicBaselineBounds.FormulaParameters) where
  /-- Reusable modular-exponentiation resource parameters selected by the source route. -/
  modexp : ModularExponentiation.ResourceParameters
  /-- Public componentwise bounds for the selected modular-exponentiation route. -/
  modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds
  /-- Source-bound certificate tying `modexp` to `modexpBounds`. -/
  sourceCertificate :
    ModularExponentiation.ResourceParameters.SourceBoundCertificate modexp modexpBounds
  /-- Shor-style register shape for the selected modular-exponentiation profile. -/
  registerShape : ModExpRegisterShape params.modulusBits modexp
  /-- Logical-qubit comparison from reusable component bounds to Shor formula fields. -/
  logicalQubits_le : modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound
  /-- Toffoli comparison from reusable component bounds to Shor formula fields. -/
  toffoliGates_le : modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound
  /-- Depth comparison from reusable component bounds to Shor formula fields. -/
  circuitDepth_le : modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound

namespace SourceBackedModexpResourcePackage

/-- Canonical VBE modular-exponentiation package for Shor-style formula
parameters.  The package fixes the reusable MAU route to the
Vedral--Barenco--Ekert controlled-power schedule; callers may still need to
prove that this route fits the selected Shor public formula envelope [VBE95,
9511018.tex:372-416] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
def ofVBECounting
    (params : PublicBaselineBounds.FormulaParameters)
    (hmodulusBits_pos : 0 < params.modulusBits)
    (hlogical :
      (ModularExponentiation.VBECounting.vbeModularExponentiationBounds
          (2 * params.modulusBits) params.modulusBits).toProfile.logicalQubits ≤
        params.logicalQubitBound)
    (htoffoli :
      (ModularExponentiation.VBECounting.vbeModularExponentiationBounds
          (2 * params.modulusBits) params.modulusBits).toProfile.toffoliGates ≤
        params.toffoliBaseBound)
    (hdepth :
      (ModularExponentiation.VBECounting.vbeModularExponentiationBounds
          (2 * params.modulusBits) params.modulusBits).toProfile.circuitDepth ≤
        params.circuitDepthBaseBound) :
    SourceBackedModexpResourcePackage params where
  modexp :=
    ModularExponentiation.VBECounting.vbeModularExponentiationResourceParameters
      (2 * params.modulusBits) params.modulusBits
  modexpBounds :=
    ModularExponentiation.VBECounting.vbeModularExponentiationBounds
      (2 * params.modulusBits) params.modulusBits
  sourceCertificate :=
    ModularExponentiation.VBECounting.vbeModularExponentiationSourceBoundCertificate
      (2 * params.modulusBits) params.modulusBits hmodulusBits_pos
  registerShape := by
    constructor <;> rfl
  logicalQubits_le := hlogical
  toffoliGates_le := htoffoli
  circuitDepth_le := hdepth

/-- The source-backed package derives the Shor workspace-addend formula bound. -/
theorem workspaceAddend_le {params : PublicBaselineBounds.FormulaParameters}
    (pkg : SourceBackedModexpResourcePackage params) :
    modularExponentiationWorkspaceAddend params.modulusBits pkg.modexp ≤
      params.workspaceAddendBound :=
  workspaceAddend_le_formulaBound_of_modexpSourceBoundCertificate
    pkg.registerShape pkg.sourceCertificate pkg.logicalQubits_le

/-- The selected source-backed modular-exponentiation package supports the Shor
public-baseline fields for any final-statement-ready retry selector. -/
theorem supportsPublicBaseline
    {retry : RetryMultiplierSpec}
    {params : PublicBaselineBounds.FormulaParameters}
    (pkg : SourceBackedModexpResourcePackage params)
    (readiness : FinalResourceReadiness retry) (hpos : 0 < retry.runCount) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits pkg.modexp)
      (params.toPublicBaselineBounds retry) :=
  exactSupportProfile_supportsPublicBaseline_of_modexpWorkspaceCertificate
    readiness hpos pkg.registerShape pkg.sourceCertificate pkg.logicalQubits_le
    pkg.toffoliGates_le pkg.circuitDepth_le

/-- Package-level private resource witness.  This is still a support witness, not
the public theorem-node realization: the formula envelope remains a separate
public-bound layer. -/
private theorem privateResourceWitness
    {retry : RetryMultiplierSpec}
    {params : PublicBaselineBounds.FormulaParameters}
    (pkg : SourceBackedModexpResourcePackage params)
    (readiness : FinalResourceReadiness retry) (hpos : 0 < retry.runCount) :
    PrivateResourceStatementWitness retry pkg.modexp params where
  readiness := readiness
  supportsPublicBaseline := pkg.supportsPublicBaseline readiness hpos

end SourceBackedModexpResourcePackage

namespace PublicBaselineBounds
namespace Envelope

/-- Canonical VBE modular-exponentiation resource parameters for an `n`-bit
Shor modulus. -/
def vbeModexpParams (n : ℕ) : ModularExponentiation.ResourceParameters :=
  ModularExponentiation.VBECounting.vbeModularExponentiationResourceParameters (2 * n) n

/-- Canonical VBE modular-exponentiation bounds for an `n`-bit Shor modulus. -/
def vbeModexpBounds (n : ℕ) :
    ModularExponentiation.ResourceParameters.PublicBaselineBounds :=
  ModularExponentiation.VBECounting.vbeModularExponentiationBounds (2 * n) n

/-- Explicit logarithmic-envelope value large enough for the canonical VBE
Toffoli and depth bounds. -/
def vbeModexpLogUpperBound (n : ℕ) : ℕ :=
  max (5000 * (vbeModexpBounds n).toProfile.toffoliGates)
    (vbeModexpBounds n).toProfile.circuitDepth

/-- Canonical public envelope for the VBE modular-exponentiation route.  The
logarithmic field is chosen as an explicit upper-bound value so the envelope
can certify the canonical VBE route without endpoint callers supplying
fieldwise comparison proofs [VBE95, 9511018.tex:372-416] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
def vbeModexpEnvelope (n : ℕ) : Envelope where
  modulusBits := n
  logModulusBitsUpperBound := vbeModexpLogUpperBound n
  workspaceAddendBound := (vbeModexpBounds n).toProfile.logicalQubits

@[simp] theorem vbeModexpEnvelope_modulusBits (n : ℕ) :
    (vbeModexpEnvelope n).modulusBits = n :=
  rfl

@[simp] theorem vbeModexpEnvelope_logModulusBitsUpperBound (n : ℕ) :
    (vbeModexpEnvelope n).logModulusBitsUpperBound = vbeModexpLogUpperBound n :=
  rfl

@[simp] theorem vbeModexpEnvelope_workspaceAddendBound (n : ℕ) :
    (vbeModexpEnvelope n).workspaceAddendBound =
      (vbeModexpBounds n).toProfile.logicalQubits :=
  rfl

theorem vbeModexpBounds_logicalQubits_le_envelope (n : ℕ) :
    (vbeModexpBounds n).toProfile.logicalQubits ≤
      (vbeModexpEnvelope n).internalParams.logicalQubitBound := by
  simp [vbeModexpEnvelope, PublicBaselineBounds.FormulaParameters.logicalQubitBound]

theorem vbeModexpBounds_toffoliGates_le_envelope (n : ℕ) (hpos : 0 < n) :
    (vbeModexpBounds n).toProfile.toffoliGates ≤
      (vbeModexpEnvelope n).internalParams.toffoliBaseBound := by
  set T := (vbeModexpBounds n).toProfile.toffoliGates with hT
  have hn : 1 ≤ 3 * n ^ 3 := by
    nlinarith [Nat.succ_le_of_lt hpos, pow_pos hpos 3]
  have hlog : 5000 * T ≤ vbeModexpLogUpperBound n := by
    rw [hT]
    unfold vbeModexpLogUpperBound
    exact Nat.le_max_left _ _
  have hceil :
      T ≤ QuantumAlg.Nat.ceilDiv (3 * n ^ 3 * vbeModexpLogUpperBound n) 5000 := by
    rw [QuantumAlg.Nat.ceilDiv_eq]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5000)]
    have hmul :
        1 * (5000 * T) ≤ (3 * n ^ 3) * vbeModexpLogUpperBound n :=
      Nat.mul_le_mul hn hlog
    have hbase :
        T * 5000 ≤ 3 * n ^ 3 * vbeModexpLogUpperBound n := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    omega
  have hceil' :
      (vbeModexpBounds n).toProfile.toffoliGates ≤
        QuantumAlg.Nat.ceilDiv (3 * n ^ 3 * vbeModexpLogUpperBound n) 5000 := by
    simpa [hT] using hceil
  simpa [vbeModexpEnvelope, PublicBaselineBounds.FormulaParameters.toffoliBaseBound] using
    le_trans hceil'
      (Nat.le_add_left
        (QuantumAlg.Nat.ceilDiv (3 * n ^ 3 * vbeModexpLogUpperBound n) 5000)
        (QuantumAlg.Nat.ceilDiv (2 * n ^ 3) 5))

theorem vbeModexpBounds_circuitDepth_le_envelope (n : ℕ) (hpos : 0 < n) :
    (vbeModexpBounds n).toProfile.circuitDepth ≤
      (vbeModexpEnvelope n).internalParams.circuitDepthBaseBound := by
  set D := (vbeModexpBounds n).toProfile.circuitDepth with hD
  have hn : 1 ≤ n ^ 2 := by
    nlinarith [Nat.succ_le_of_lt hpos, pow_pos hpos 2]
  have hlog : D ≤ vbeModexpLogUpperBound n := by
    rw [hD]
    unfold vbeModexpLogUpperBound
    exact Nat.le_max_right _ _
  simp [vbeModexpEnvelope, PublicBaselineBounds.FormulaParameters.circuitDepthBaseBound]
  nlinarith

/-- Canonical source-backed modular-exponentiation package obtained from the
VBE envelope without exposing fieldwise comparison proofs to endpoint callers. -/
def vbeModexpPackage (n : ℕ) (hpos : 0 < n) :
    SourceBackedModexpResourcePackage (vbeModexpEnvelope n).internalParams :=
  SourceBackedModexpResourcePackage.ofVBECounting (vbeModexpEnvelope n).internalParams
    hpos
    (vbeModexpBounds_logicalQubits_le_envelope n)
    (vbeModexpBounds_toffoliGates_le_envelope n hpos)
    (vbeModexpBounds_circuitDepth_le_envelope n hpos)

end Envelope
end PublicBaselineBounds

/-- Circuit-aware Shor-style support from a reusable modular-exponentiation
component certificate. The quantum modular-exponentiation resource fields and
basis action are tied to `ModularExponentiation.applyUnitCircuit`; retry and
classical post-processing remain route-level accounting certificates. -/
theorem exactSupportProfile_supportsPublicBaseline_of_modexpCircuit
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {N m : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry) ∧
      (∀ x : ModularExponentiation.Data m N,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp)
          (PureState.ket (R := ModularExponentiation.register m N) x :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
            StateVector (ModularExponentiation.register m N))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).resources =
        modexp.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).depth =
        modexp.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).queryDepth =
        modexp.toProfile.oracleQueries := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact exactSupportProfile_supportsPublicBaseline_of_modexpCertificate
      readiness hpos hshape modexpCert hlogical htoffoli hdepth
  · intro x
    exact ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_ket u modexp x
  · rfl
  · rfl
  · rfl

/-- Circuit-aware private Shor-style endpoint from a reusable
modular-exponentiation component certificate. -/
theorem PrivateResourceStatementWitness.of_modexpCircuit
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {N m : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness retry modexp params ∧
      (∀ x : ModularExponentiation.Data m N,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp)
          (PureState.ket (R := ModularExponentiation.register m N) x :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
            StateVector (ModularExponentiation.register m N))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).resources =
        modexp.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).depth =
        modexp.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).queryDepth =
        modexp.toProfile.oracleQueries := by
  rcases exactSupportProfile_supportsPublicBaseline_of_modexpCircuit u readiness
      hpos hshape modexpCert hlogical htoffoli hdepth with
    ⟨hsupport, hcorrect, hresources, hdepth', hquery⟩
  exact ⟨⟨readiness, hsupport⟩, hcorrect, hresources, hdepth', hquery⟩

/-- Circuit-aware Shor-style support with the clean accumulator action exposed
in the same shape as the modular-exponentiation endpoint. This keeps the
factoring support theorem aligned with the reversible accumulator circuit rather
than treating exponentiation as a non-injective one-register map. -/
theorem exactSupportProfile_supportsPublicBaseline_of_modexpCleanCircuit
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {N m : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry) ∧
      (∀ exponent : Fin (2 ^ m), ∀ target : ZMod N,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp)
          (PureState.ket (R := ModularExponentiation.register m N)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data m N) :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N)
            ({ exponent := exponent
               target := target * ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
               flag := false } : ModularExponentiation.Data m N) :
            StateVector (ModularExponentiation.register m N))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).resources =
        modexp.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).depth =
        modexp.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).queryDepth =
        modexp.toProfile.oracleQueries := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact exactSupportProfile_supportsPublicBaseline_of_modexpCertificate
      readiness hpos hshape modexpCert hlogical htoffoli hdepth
  · intro exponent target
    exact ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_clean_ket
      u modexp exponent target
  · rfl
  · rfl
  · rfl

/-- Clean-circuit private Shor-style endpoint from a reusable
modular-exponentiation component certificate. The first conjunct is the named
private resource statement witness; the remaining conjuncts keep the same typed
`Circuit` action and resource equalities as the reusable exponentiation layer. -/
theorem PrivateResourceStatementWitness.of_modexpCleanCircuit
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {N m : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness retry modexp params ∧
      (∀ exponent : Fin (2 ^ m), ∀ target : ZMod N,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp)
          (PureState.ket (R := ModularExponentiation.register m N)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data m N) :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N)
            ({ exponent := exponent
               target := target * ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
               flag := false } : ModularExponentiation.Data m N) :
            StateVector (ModularExponentiation.register m N))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).resources =
        modexp.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).depth =
        modexp.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).queryDepth =
        modexp.toProfile.oracleQueries := by
  rcases exactSupportProfile_supportsPublicBaseline_of_modexpCleanCircuit u readiness
      hpos hshape modexpCert hlogical htoffoli hdepth with
    ⟨hsupport, hcorrect, hresources, hdepth', hquery⟩
  exact ⟨⟨readiness, hsupport⟩, hcorrect, hresources, hdepth', hquery⟩

/-! ### Public-baseline theorem endpoints -/

/-- The Shor-style exact support profile implies the public RSA baseline fields
once the reusable modular-exponentiation component supplies source-backed
upper-bound fields and the retry multiplier is final-statement ready [Sho95,
source.tex:1124-1148] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
theorem main_supportsPublicBaseline
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry) :=
  exactSupportProfile_supportsPublicBaseline_of_modexpWorkspaceCertificate
    readiness hpos hshape modexpCert hlogical htoffoli hdepth

/-- The private exact-resource Shor-style statement packages the public-baseline
implication with final-statement retry readiness [Sho95, source.tex:1124-1148]
[GE19, main.tex:70-79, 211-216, 1785-1788]. -/
theorem main_with_public_baseline
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness retry modexp params :=
  PrivateResourceStatementWitness.of_modexpWorkspaceCertificate readiness hpos hshape
    modexpCert hlogical htoffoli hdepth

/-- Circuit-aware Shor-style endpoint: the exact-resource public-baseline witness
and the modular-exponentiation accumulator action are exposed together, so the
same typed `Circuit` carries the quantum correctness and resource projection
[Sho95, source.tex:1124-1148] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
theorem main_with_public_baseline_cleanCircuit
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {N m : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness retry modexp params ∧
      (∀ exponent : Fin (2 ^ m), ∀ target : ZMod N,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp)
          (PureState.ket (R := ModularExponentiation.register m N)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data m N) :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N)
            ({ exponent := exponent
               target := target * ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
               flag := false } : ModularExponentiation.Data m N) :
            StateVector (ModularExponentiation.register m N))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).resources =
        modexp.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).depth =
        modexp.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u modexp).queryDepth =
        modexp.toProfile.oracleQueries :=
  PrivateResourceStatementWitness.of_modexpCleanCircuit u readiness hpos hshape modexpCert
    hlogical htoffoli hdepth

/-! ### Public factor-return endpoint -/

/-- Deterministic factor-return constructor for the successful Shor half-order
branch. Once order finding has returned an even order and the nontrivial
half-order side conditions hold, the source route computes
`gcd(x^(r/2)-1,N)` to obtain an RSA factor [Sho95, source.tex:1124-1148]. -/
def halfOrderFactorReturnCertificate {N x r : ℕ}
    (model : ShorFactoring.SemiprimeFactorModel N)
    (route : ShorFactoring.HalfOrderGcdInput N x r) :
    ShorFactoring.FactorReturnCertificate model :=
  ShorFactoring.halfOrderLeftFactorReturnCertificate model route

/-- Source-shaped certificate for Shor's random-base factor-yield event. It
keeps the selected base, recovered order, half-order gcd side conditions, and
the rational lower-bound fields together, matching the random-base analysis in
Shor's factoring reduction [Sho95, source.tex:1132-1169]. -/
structure RandomBaseFactorYieldCertificate {N : ℕ}
    (model : ShorFactoring.SemiprimeFactorModel N) where
  /-- Random base used by the factor-yield certificate. -/
  base : ℕ
  /-- Multiplicative order associated with the selected base. -/
  order : ℕ
  route : ShorFactoring.HalfOrderGcdInput N base order
  /-- Numerator of the certified success-probability lower bound. -/
  successNumerator : ℕ
  /-- Denominator of the certified success-probability lower bound. -/
  successDenominator : ℕ
  successDenominator_pos : 0 < successDenominator
  factorYield_atLeast_oneHalf :
    successDenominator ≤ 2 * successNumerator
  /-- Factor-return certificate supplied to the public endpoint. -/
  factorReturn :
    ShorFactoring.FactorReturnCertificate model :=
      halfOrderFactorReturnCertificate model route

namespace RandomBaseFactorYieldCertificate

/-- The recovered order carried by a Shor factor-yield certificate is positive;
otherwise the half-order gcd route would violate its nonzero side condition
[Sho95, source.tex:1124-1148]. -/
theorem order_pos {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : RandomBaseFactorYieldCertificate model) : 0 < cert.order :=
  cert.route.order_pos

/-- Construct the random-base factor-yield certificate from the explicit
source-route data: a selected base, the recovered even order with half-order
gcd side conditions, and the rational one-run lower-bound fields. This is the
Lean-facing constructor for Shor's factor-yield branch, before the separate
order-recovery and retry-amplification passes combine it into the final
success certificate [Sho95, source.tex:1132-1169]. -/
def ofHalfOrderRoute {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (base order : ℕ)
    (route : ShorFactoring.HalfOrderGcdInput N base order)
    (successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (factorYield_atLeast_oneHalf :
      successDenominator ≤ 2 * successNumerator) :
    RandomBaseFactorYieldCertificate model where
  base := base
  order := order
  route := route
  successNumerator := successNumerator
  successDenominator := successDenominator
  successDenominator_pos := successDenominator_pos
  factorYield_atLeast_oneHalf := factorYield_atLeast_oneHalf

/-- Internal bridge from the public random-base good-event lower-bound package
to the source-shaped factor-yield certificate consumed by the Shor retry route.
The lower-bound numerator, denominator, positivity, and one-half comparison
come from the counted public semiprime good event; the only remaining internal
route data is the selected good-base half-order gcd witness [Sho95,
source.tex:1132-1169; source.tex:1155-1169]. -/
def ofPublicGoodEventRoute {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (good :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound model)
    (sample : ShorFactoring.RandomBaseUnitSample model)
    (order : ℕ)
    (route : ShorFactoring.HalfOrderGcdInput N sample.baseResidue order) :
    RandomBaseFactorYieldCertificate model :=
  ofHalfOrderRoute sample.baseResidue order route good.goodEventCount
    good.sampleSpaceCount good.sampleSpaceCount_pos
    good.goodEvent_atLeast_oneHalf

/-- Internal selected-route bridge from the public random-base good-event
package to the Shor factor-yield certificate. The endpoint-facing signature
takes only the public good-event lower-bound package; the selected sample,
order, and half-order gcd route are obtained internally from the good-event
existence theorem [Sho95, source.tex:1132-1169; source.tex:1155-1169]. -/
noncomputable def ofPublicGoodEvent {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (good :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound model) :
    RandomBaseFactorYieldCertificate model := by
  classical
  let hroute := good.exists_halfOrderGcdInput
  let sample := Classical.choose hroute
  let route := (Classical.choose_spec hroute).2
  exact ofPublicGoodEventRoute good sample (orderOf sample.unit) route

end RandomBaseFactorYieldCertificate

/-- Rational order-recovery fields tied to the Shor source-success lower bound.
The numerator and denominator are the natural-number fields later consumed by
`RetrySuccessCertificate`; this certificate records that their rational value
is below the source-level order-recovery mass lower bound [Sho95,
source.tex:1614-1663]. -/
structure OrderRecoveryRationalFieldCertificate
    (r successNumerator successDenominator : ℕ) : Prop where
  successDenominator_pos : 0 < successDenominator
  rational_le_sourceLowerBound :
    (successNumerator : ℝ) / (successDenominator : ℝ) ≤
      OrderFinding.shorOrderRecoverySuccessLowerBound r

namespace OrderRecoveryRationalFieldCertificate

/-- Construct rational order-recovery fields from an explicit comparison
against the Shor source lower bound. This keeps the analytic probability
comparison visible instead of hiding it in the Shor factoring certificate
[Sho95, source.tex:1614-1663]. -/
theorem ofSourceLowerBound
    (r successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (hbound :
      (successNumerator : ℝ) / (successDenominator : ℝ) ≤
        OrderFinding.shorOrderRecoverySuccessLowerBound r) :
    OrderRecoveryRationalFieldCertificate r successNumerator successDenominator :=
  ⟨successDenominator_pos, hbound⟩

/-- A rational order-recovery field certificate composes with the source joint
event-map certificate to give a bound below the certified total source mass.
This is the bridge from the order-finding probability layer to the natural
fields consumed by Shor's factoring route [Sho95, source.tex:1614-1663]. -/
theorem rational_le_sourceJointTotalMass
    {t r successNumerator successDenominator : ℕ}
    (fields :
      OrderRecoveryRationalFieldCertificate r successNumerator successDenominator)
    (cert : OrderFinding.ShorSourceJointEventMapCertificate t r)
    (hr : 0 < r) :
    (successNumerator : ℝ) / (successDenominator : ℝ) ≤
      ∑ outcome : OrderFinding.ShorSourceJointOutcome t r, cert.prob outcome :=
  le_trans fields.rational_le_sourceLowerBound
    (cert.successLowerBound_le_totalMass hr)

/-- Canonical rational fields for Shor order recovery.  The source order-
finding analysis gives the output-order success lower bound
`φ(r)/(3r)` [Sho95, source.tex:1614-1663], and the public order-finding layer
uses the same lower-bound expression. -/
theorem ofPublicOrderFindingLowerBound (r : ℕ) (hr : 0 < r) :
    OrderRecoveryRationalFieldCertificate r (Nat.totient r) (3 * r) := by
  refine ofSourceLowerBound r (Nat.totient r) (3 * r) ?_ ?_
  · exact Nat.mul_pos (by norm_num : 0 < 3) hr
  · simp [OrderFinding.shorOrderRecoverySuccessLowerBound, Nat.cast_mul]

/-- The public order-finding output-success theorem supplies the same rational
lower-bound fields consumed by the Shor factoring route.  This bridge keeps
the theorem-node endpoint from taking an order-recovery certificate as an
external input [Sho95, source.tex:1614-1663]. -/
theorem rationalFields_le_publicOutputSuccessMass
    {G : Type*} [Monoid G] {g : G} {t r : ℕ}
    {prob : OrderFinding.ShorSourceJointOutcome t r → ℝ}
    (houtput :
      OrderFinding.orderFindingOutputSuccessLowerBound r ≤
        OrderFinding.orderFindingOutputSuccessMass g prob) :
    ((Nat.totient r : ℝ) / (((3 * r : ℕ) : ℝ))) ≤
      OrderFinding.orderFindingOutputSuccessMass g prob := by
  simpa [OrderFinding.orderFindingOutputSuccessLowerBound, Nat.cast_mul]
    using houtput

end OrderRecoveryRationalFieldCertificate

/-- Retry-amplification fields for the Shor source route. The record separates
the repeated-run success calculation from the factor-yield and order-recovery
certificates: it carries the final rational success lower bound together with
the two public comparisons consumed by the RSA factoring endpoint [Sho95,
source.tex:1647-1663]. -/
structure RetryAmplificationCertificate (retry : RetryMultiplierSpec) where
  /-- Numerator of the certified repeated-run success lower bound. -/
  successNumerator : ℕ
  /-- Denominator of the certified repeated-run success lower bound. -/
  successDenominator : ℕ
  successDenominator_pos : 0 < successDenominator
  success_atLeast_twoThirds :
    2 * successDenominator ≤ 3 * successNumerator
  success_atLeast_failureBudget :
    (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
        successDenominator ≤
      retry.failureBudget.failureDenominator * successNumerator

namespace EtaRetrySelector

/-- Record-level amplification certificate for the Shor eta selector.  The
success comparisons are explicit cross-multiplied natural-number inequalities;
their probabilistic derivation is kept in the dedicated failure-bound layer. -/
def amplificationCertificate (budget : FailureBudget)
    {successNumerator successDenominator : ℕ}
    (successDenominator_pos : 0 < successDenominator)
    (success_atLeast_twoThirds :
      2 * successDenominator ≤ 3 * successNumerator)
    (success_atLeast_failureBudget :
      (budget.failureDenominator - budget.failureNumerator) *
          successDenominator ≤
        budget.failureDenominator * successNumerator) :
    RetryAmplificationCertificate (spec budget) where
  successNumerator := successNumerator
  successDenominator := successDenominator
  successDenominator_pos := successDenominator_pos
  success_atLeast_twoThirds := success_atLeast_twoThirds
  success_atLeast_failureBudget := success_atLeast_failureBudget

end EtaRetrySelector

namespace RepeatedTrialFailureBound

/-- Build the Shor retry-amplification certificate from an explicit repeated
failure bound. The success numerator is the complement of the repeated-failure
field, and the `1 - eta` comparison is proved by
`successAtLeastOneMinusFailureBudget`. A separate premise records any stronger
constant success target, such as the public two-thirds endpoint [Sho95,
source.tex:1647-1663]. -/
def amplificationCertificate (oneRun : FailureBudget)
    (retry : RetryMultiplierSpec)
    (hbudget : retry.failureBudget.WellFormed)
    (honeRun : oneRun.WellFormed)
    (hrepeated :
      numerator oneRun retry * retry.failureBudget.failureDenominator ≤
        retry.failureBudget.failureNumerator * denominator oneRun retry)
    (htwoThirds :
      2 * denominator oneRun retry ≤
        3 * (denominator oneRun retry - numerator oneRun retry)) :
    RetryAmplificationCertificate retry where
  successNumerator := denominator oneRun retry - numerator oneRun retry
  successDenominator := denominator oneRun retry
  successDenominator_pos := denominator_pos oneRun retry honeRun
  success_atLeast_twoThirds := htwoThirds
  success_atLeast_failureBudget :=
    successAtLeastOneMinusFailureBudget oneRun retry hbudget honeRun hrepeated

end RepeatedTrialFailureBound

namespace EtaRetrySelector

/-- Build the Shor eta selector's retry-amplification fields from public
failure-budget data, a one-run half-failure bound, and the source route's
constant-success comparison. This packages the repetition and amplification
records behind a single public-budget API so theorem-node endpoints do not take
`RepetitionModel` or `RetryAmplificationCertificate` as external inputs
[Sho95, source.tex:1647-1663]. -/
def calibratedAmplificationCertificate (oneRun budget : FailureBudget)
    (hbudget : WellFormed budget)
    (honeRun : oneRun.WellFormed)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator)
    (htwoThirds :
      2 * RepeatedTrialFailureBound.denominator oneRun (spec budget) ≤
        3 * (RepeatedTrialFailureBound.denominator oneRun (spec budget) -
          RepeatedTrialFailureBound.numerator oneRun (spec budget))) :
    RetryAmplificationCertificate (spec budget) :=
  RepeatedTrialFailureBound.amplificationCertificate oneRun (spec budget)
    hbudget.1 honeRun
    (repeatedFailure_le_budget_of_oneRun_atMostHalf oneRun budget hbudget honeHalf)
    htwoThirds

/-- Public-budget selector package for Shor retry accounting. It exposes the
concrete final-ready retry spec together with the internally constructed
repetition model and amplification fields [Sho95, source.tex:1647-1663]. -/
structure PublicBudgetRetryPackage (oneRun budget : FailureBudget) where
  /-- Retry multiplier selected by the public budget. -/
  retry : RetryMultiplierSpec
  /-- The selected retry multiplier is the canonical eta selector output. -/
  retry_eq_spec : retry = spec budget
  hbudget : WellFormed budget
  honeRun : oneRun.WellFormed
  honeHalf : 2 * oneRun.failureNumerator ≤ oneRun.failureDenominator
  htwoThirds :
    2 * RepeatedTrialFailureBound.denominator oneRun (spec budget) ≤
      3 * (RepeatedTrialFailureBound.denominator oneRun (spec budget) -
        RepeatedTrialFailureBound.numerator oneRun (spec budget))

/-- Build the public retry package from public failure-budget inequalities,
deriving the two-thirds success comparison internally. This is the constructor
used by theorem-facing endpoints instead of accepting a prebuilt
`PublicBudgetRetryPackage` [Sho95, source.tex:1647-1663]. -/
@[nolint defLemma]
def publicBudgetRetryPackage (oneRun budget : FailureBudget)
    (hbudget : WellFormed budget)
    (honeRun : oneRun.WellFormed)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator)
    (hbudgetThird :
      3 * budget.failureNumerator ≤ budget.failureDenominator) :
    PublicBudgetRetryPackage oneRun budget where
  retry := spec budget
  retry_eq_spec := rfl
  hbudget := hbudget
  honeRun := honeRun
  honeHalf := honeHalf
  htwoThirds :=
    successAtLeastTwoThirds_of_budget_atMostOneThird oneRun budget hbudget
      honeRun honeHalf hbudgetThird

namespace PublicBudgetRetryPackage

/-- The package constructs the repetition model internally from public-budget
data and the one-run half-failure bound. -/
def repetition {oneRun budget : FailureBudget}
    (pkg : PublicBudgetRetryPackage oneRun budget) :
    RetryMultiplierSpec.RepetitionModel pkg.retry := by
  rw [pkg.retry_eq_spec]
  exact calibratedRepetitionModel oneRun budget pkg.hbudget pkg.honeRun pkg.honeHalf

/-- The package constructs the retry-amplification fields internally; final
endpoints can consume this projection without accepting an external
amplification certificate. -/
def amplification {oneRun budget : FailureBudget}
    (pkg : PublicBudgetRetryPackage oneRun budget) :
    RetryAmplificationCertificate pkg.retry := by
  rw [pkg.retry_eq_spec]
  exact
    calibratedAmplificationCertificate oneRun budget pkg.hbudget pkg.honeRun
      pkg.honeHalf pkg.htwoThirds

@[simp] theorem retry_eq {oneRun budget : FailureBudget}
    (pkg : PublicBudgetRetryPackage oneRun budget) :
    pkg.retry = spec budget :=
  pkg.retry_eq_spec

-- Generated structure lemma; this retry package is projected through named API
-- fields, so keeping constructor injectivity out of simp is intentional.
attribute [-simp]
  QuantumAlg.Factoring.ShorStyle.EtaRetrySelector.PublicBudgetRetryPackage.mk.injEq
attribute [nolint simpNF]
  QuantumAlg.Factoring.ShorStyle.EtaRetrySelector.PublicBudgetRetryPackage.mk.injEq

end PublicBudgetRetryPackage

/-- Canonical one-run failure budget used by the public Shor retry wrapper. It
records the source-level one-run constant-success route as a half-failure bound,
so endpoint declarations need not expose a separate one-run budget parameter
[Sho95, source.tex:1647-1663]. -/
def halfFailureOneRunBudget : FailureBudget :=
  FailureBudget.binary 1

@[simp] theorem halfFailureOneRunBudget_failureNumerator :
    halfFailureOneRunBudget.failureNumerator = 1 :=
  rfl

@[simp] theorem halfFailureOneRunBudget_failureDenominator :
    halfFailureOneRunBudget.failureDenominator = 2 :=
  rfl

theorem halfFailureOneRunBudget_wellFormed :
    halfFailureOneRunBudget.WellFormed :=
  FailureBudget.binary_wellFormed 1

theorem halfFailureOneRunBudget_atMostHalf :
    2 * halfFailureOneRunBudget.failureNumerator ≤
      halfFailureOneRunBudget.failureDenominator := by
  norm_num [halfFailureOneRunBudget, FailureBudget.binary]

/-- Public retry-domain conditions for the Shor eta selector. The final endpoint
should consume this public failure-budget data, not a one-run budget or retry
package [Sho95, source.tex:1647-1663]. -/
structure PublicFailureBudget (budget : FailureBudget) : Prop where
  hbudget : WellFormed budget
  hbudgetThird : 3 * budget.failureNumerator ≤ budget.failureDenominator

namespace PublicFailureBudget

/-- Convert public failure-budget conditions into the existing retry package
using the canonical half-failure one-run budget. -/
@[nolint defLemma]
def toPublicBudgetRetryPackage {budget : FailureBudget}
    (h : PublicFailureBudget budget) :
    PublicBudgetRetryPackage halfFailureOneRunBudget budget :=
  publicBudgetRetryPackage halfFailureOneRunBudget budget h.hbudget
    halfFailureOneRunBudget_wellFormed halfFailureOneRunBudget_atMostHalf
    h.hbudgetThird

@[simp] theorem toPublicBudgetRetryPackage_retry {budget : FailureBudget}
    (h : PublicFailureBudget budget) :
    h.toPublicBudgetRetryPackage.retry = spec budget :=
  rfl

end PublicFailureBudget

end EtaRetrySelector

/-- Source-shaped success certificate for the Shor RSA route. It combines the
random-base factor-yield certificate, the order-recovery rational fields, and a
source-certified repetition model into the explicit success fields consumed by
`ProbabilisticFactorReturnCertificate` [Sho95, source.tex:1132-1169,
source.tex:1647-1663]. -/
structure RetrySuccessCertificate {N : ℕ}
    (model : ShorFactoring.SemiprimeFactorModel N)
    (retry : RetryMultiplierSpec) where
  /-- Single-run factor-yield certificate used by the retry model. -/
  factorYield : RandomBaseFactorYieldCertificate model
  /-- Numerator of the order-recovery success lower bound. -/
  orderRecoverySuccessNumerator : ℕ
  /-- Denominator of the order-recovery success lower bound. -/
  orderRecoverySuccessDenominator : ℕ
  orderRecoverySuccessDenominator_pos : 0 < orderRecoverySuccessDenominator
  orderRecoverySource :
    OrderRecoveryRationalFieldCertificate factorYield.order
      orderRecoverySuccessNumerator orderRecoverySuccessDenominator
  /-- Repetition model or certificate used for success amplification. -/
  repetition : RetryMultiplierSpec.RepetitionModel retry
  /-- Numerator of the certified success-probability lower bound. -/
  successNumerator : ℕ
  /-- Denominator of the certified success-probability lower bound. -/
  successDenominator : ℕ
  successDenominator_pos : 0 < successDenominator
  success_atLeast_twoThirds :
    2 * successDenominator ≤ 3 * successNumerator
  success_atLeast_failureBudget :
    (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
        successDenominator ≤
      retry.failureBudget.failureDenominator * successNumerator

/-- Convert the Shor source-shaped retry/success certificate into the generic
probabilistic factor-return certificate used by the public RSA factoring
endpoint [Sho95, source.tex:1132-1169, source.tex:1647-1663]. -/
def RetrySuccessCertificate.toProbabilisticFactorReturnCertificate {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    (cert : RetrySuccessCertificate model retry) :
    ShorFactoring.ProbabilisticFactorReturnCertificate model where
  output := cert.factorYield.factorReturn
  successNumerator := cert.successNumerator
  successDenominator := cert.successDenominator
  successDenominator_pos := cert.successDenominator_pos
  success_atLeast := cert.success_atLeast_twoThirds

namespace RetrySuccessCertificate

/-- Construct the Shor retry-success certificate from explicit source-route
pieces: the random-base factor-yield certificate, rational order-recovery
fields tied to the source lower bound, a certified repetition model, and a
retry-amplification success record. This is the source-route constructor used
before projecting to the public RSA endpoint [Sho95, source.tex:1132-1169,
source.tex:1614-1663]. -/
def ofSourcePieces {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    {orderRecoverySuccessNumerator orderRecoverySuccessDenominator : ℕ}
    (factorYield : RandomBaseFactorYieldCertificate model)
    (orderRecoverySource :
      OrderRecoveryRationalFieldCertificate factorYield.order
        orderRecoverySuccessNumerator orderRecoverySuccessDenominator)
    (repetition : RetryMultiplierSpec.RepetitionModel retry)
    (amplification : RetryAmplificationCertificate retry) :
    RetrySuccessCertificate model retry where
  factorYield := factorYield
  orderRecoverySuccessNumerator := orderRecoverySuccessNumerator
  orderRecoverySuccessDenominator := orderRecoverySuccessDenominator
  orderRecoverySuccessDenominator_pos :=
    orderRecoverySource.successDenominator_pos
  orderRecoverySource := orderRecoverySource
  repetition := repetition
  successNumerator := amplification.successNumerator
  successDenominator := amplification.successDenominator
  successDenominator_pos := amplification.successDenominator_pos
  success_atLeast_twoThirds := amplification.success_atLeast_twoThirds
  success_atLeast_failureBudget := amplification.success_atLeast_failureBudget

/-- Construct the Shor retry-success certificate while deriving the
order-recovery rational fields internally from the recovered order. This keeps
`OrderRecoveryRationalFieldCertificate` out of endpoint-facing signatures; the
canonical `φ(r)/(3r)` fields come from the public order-finding lower-bound
bridge [Sho95, source.tex:1614-1663]. -/
def ofPublicOrderRecovery {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    (factorYield : RandomBaseFactorYieldCertificate model)
    (repetition : RetryMultiplierSpec.RepetitionModel retry)
    (amplification : RetryAmplificationCertificate retry) :
    RetrySuccessCertificate model retry :=
  ofSourcePieces factorYield
    (OrderRecoveryRationalFieldCertificate.ofPublicOrderFindingLowerBound
      factorYield.order factorYield.order_pos)
    repetition amplification

/-- The Shor source-shaped retry certificate also exposes the eta-parametric
success statement: if the retry failure budget represents `eta`, then the
stored rational success lower bound is at least `1 - eta`. This is the
natural-number cross-multiplied form used by the public RSA theorem route
[Sho95, source.tex:1132-1169, source.tex:1647-1663]. -/
theorem successAtLeastOneMinusFailureBudget {N : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    (cert : RetrySuccessCertificate model retry) :
    (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
        cert.successDenominator ≤
      retry.failureBudget.failureDenominator * cert.successNumerator :=
  cert.success_atLeast_failureBudget

end RetrySuccessCertificate

/-- Public Shor-style RSA factor-recovery certificate. It combines the
number-theoretic factor-return certificate, the source-certified retry/failure
model, and the exact-resource support witness for the public baseline fields.
The factor-return reduction is Shor's order-finding route [Sho95,
source.tex:1124-1148, 1630-1663]. -/
structure PublicFactorizationCertificate
    {N : ℕ} (model : ShorFactoring.SemiprimeFactorModel N)
    (retry : RetryMultiplierSpec)
    (modexp : ModularExponentiation.ResourceParameters)
    (params : PublicBaselineBounds.FormulaParameters) where
  /-- Factor-return certificate supplied to the public endpoint. -/
  factorReturn : ShorFactoring.ProbabilisticFactorReturnCertificate model
  /-- Repetition model or certificate used for success amplification. -/
  repetition : RetryMultiplierSpec.RepetitionModel retry
  /-- Eta-parametric success lower bound in exact rational form: if the retry
  failure budget represents `eta`, then the factor-return success lower bound is
  at least `1 - eta` [Sho95, source.tex:1132-1169, source.tex:1647-1663]. -/
  successAtLeastOneMinusFailureBudget :
    (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
        factorReturn.successDenominator ≤
      retry.failureBudget.failureDenominator * factorReturn.successNumerator
  resources : PrivateResourceStatementWitness retry modexp params

namespace PublicFactorizationCertificate

/-- Public consequence predicate for the Shor-style RSA factor-recovery
certificate. It packages the factor-return event, the two success lower-bound
comparisons, the retry/failure accounting, final-statement readiness, and the
public resource-baseline support in one theorem-node-facing proposition
[Sho95, source.tex:1124-1148, 1630-1663] [GE19, main.tex:70-79, 211-216,
1785-1788]. -/
def Statement {N : ℕ} {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (cert : PublicFactorizationCertificate model retry modexp params) : Prop :=
  (cert.factorReturn.output.output = model.leftFactor ∨
      cert.factorReturn.output.output = model.rightFactor) ∧
    2 * cert.factorReturn.successDenominator ≤
      3 * cert.factorReturn.successNumerator ∧
    (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
        cert.factorReturn.successDenominator ≤
      retry.failureBudget.failureDenominator *
        cert.factorReturn.successNumerator ∧
    cert.repetition.failureNumerator * retry.failureBudget.failureDenominator ≤
      retry.failureBudget.failureNumerator * cert.repetition.failureDenominator ∧
    retry.readyForFinalStatement = true ∧
    SupportsPublicBaseline
      (exactSupportProfile retry params.modulusBits modexp)
      (params.toPublicBaselineBounds retry)

end PublicFactorizationCertificate

/-! ### Public endpoint theorem shape -/

/-- Public input carrier for the Shor-style RSA factorization theorem.  The
bit-length fields are the Lean-side exact carrier for the statement's
`n = ceil(log_2 N)` phrase; later endpoints may prove the window from a
canonical bit-length definition before constructing this input. -/
structure PublicInput (N n : ℕ) where
  /-- Declared semiprime model for the known public modulus. -/
  model : ShorFactoring.SemiprimeFactorModel N
  /-- Lower bit-length window for the public modulus. -/
  modulus_lower : 2 ^ (n - 1) ≤ N
  /-- Upper bit-length window for the public modulus. -/
  modulus_upper : N < 2 ^ n

/-- Public random-base route extracted from the public semiprime input.  The
branch where one declared factor is two is handled as a trivial factor-return
case; otherwise the input supplies the odd-prime side conditions needed to
construct Shor's random-base good-event lower-bound package internally
[Sho95, source.tex:1124-1148; source.tex:1132-1169; source.tex:1155-1169]. -/
inductive PublicRandomBaseRoute {N n : ℕ} (input : PublicInput N n) where
  /-- A trivial declared-prime branch, used before the odd-prime random-base
  analysis. -/
  | evenFactor :
      ShorFactoring.FactorReturnCertificate input.model →
        PublicRandomBaseRoute input
  /-- The odd-prime Shor route, with the random-base good-event package derived
  from the public semiprime model rather than supplied by the endpoint. -/
  | oddGood :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound
        input.model →
        PublicRandomBaseRoute input

namespace PublicInput

/-- The public bit-length window and semiprime model imply that the declared
modulus bit length is positive. -/
theorem modulusBits_pos {N n : ℕ} (input : PublicInput N n) : 0 < n := by
  by_contra h
  have hn : n = 0 := Nat.eq_zero_of_not_pos h
  have hlt : N < 1 := by
    simpa [hn] using input.modulus_upper
  exact (not_lt_of_ge (Nat.le_of_lt input.model.modulus_gt_one)) hlt

/-- Split the public semiprime input into the trivial factor-two branch or the
odd-prime branch required by Shor's random-base analysis.  The odd branch builds
the good-event lower-bound package from the declared prime model; the selected
random base and half-order route remain internal to later constructors
[Sho95, source.tex:1124-1148; source.tex:1132-1169; source.tex:1155-1169]. -/
noncomputable def randomBaseRoute {N n : ℕ}
    (input : PublicInput N n) : PublicRandomBaseRoute input := by
  classical
  by_cases hleft : input.model.leftFactor = 2
  · exact PublicRandomBaseRoute.evenFactor
      (ShorFactoring.FactorReturnCertificate.declaredLeft input.model)
  by_cases hright : input.model.rightFactor = 2
  · exact PublicRandomBaseRoute.evenFactor
      (ShorFactoring.FactorReturnCertificate.declaredRight input.model)
  exact PublicRandomBaseRoute.oddGood
    (ShorFactoring.SemiprimeFactorModel.randomBaseGoodEventLowerBound
      input.model
      (input.model.leftFactor_gt_two_of_ne_two hleft)
      (input.model.rightFactor_gt_two_of_ne_two hright))

end PublicInput

/-- Public endpoint witness for the Shor-style RSA factorization theorem.  It
records only public endpoint data: a returned factor, rational success fields,
the retry/failure-budget comparison, final retry readiness, and the explicit
public resource baseline.  Source-piece certificates are intentionally absent
from this type; source-route proofs must construct this witness internally
before a theorem-node endpoint can consume it [Sho95, source.tex:1124-1148,
source.tex:1132-1169, source.tex:1647-1663] [GE19, main.tex:70-79, 211-216,
1785-1788]. -/
structure PublicEndpointWitness {N n : ℕ} (input : PublicInput N n)
    (retry : RetryMultiplierSpec) (bounds : PublicBaselineBounds) where
  /-- Returned factor candidate. -/
  output : ℕ
  /-- Resource profile for the algorithm represented by this witness. -/
  profile : ModularArithmeticResourceProfile
  /-- The returned factor is one of the two declared semiprime factors. -/
  output_mem_declared_factors :
    output = input.model.leftFactor ∨ output = input.model.rightFactor
  /-- Numerator of the certified success-probability lower bound. -/
  successNumerator : ℕ
  /-- Denominator of the certified success-probability lower bound. -/
  successDenominator : ℕ
  successDenominator_pos : 0 < successDenominator
  /-- Baseline Shor success lower bound. -/
  success_atLeast_twoThirds :
    2 * successDenominator ≤ 3 * successNumerator
  /-- Eta/failure-budget success lower bound. -/
  success_atLeast_failureBudget :
    (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
        successDenominator ≤
      retry.failureBudget.failureDenominator * successNumerator
  /-- The selected retry multiplier is exact or an explicit upper-bound
  function, not an unresolved source estimate. -/
  retry_ready : retry.readyForFinalStatement = true
  /-- Exact resource profile supports the public baseline fields. -/
  supportsPublicBaseline : SupportsPublicBaseline profile bounds

namespace PublicEndpointWitness

/-- Public consequence predicate for a Shor-style RSA endpoint witness.  This is
the theorem-shape target consumed by the final public endpoint, separated from
the source-route constructors that may build such a witness. -/
def Statement {N n : ℕ} {input : PublicInput N n}
    {retry : RetryMultiplierSpec} {bounds : PublicBaselineBounds}
    (witness : PublicEndpointWitness input retry bounds) : Prop :=
  (witness.output = input.model.leftFactor ∨
      witness.output = input.model.rightFactor) ∧
    2 * witness.successDenominator ≤ 3 * witness.successNumerator ∧
    (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
        witness.successDenominator ≤
      retry.failureBudget.failureDenominator * witness.successNumerator ∧
    retry.readyForFinalStatement = true ∧
    SupportsPublicBaseline witness.profile bounds

/-- Any public endpoint witness exposes the public theorem-shape consequence. -/
theorem statement {N n : ℕ} {input : PublicInput N n}
    {retry : RetryMultiplierSpec} {bounds : PublicBaselineBounds}
    (witness : PublicEndpointWitness input retry bounds) :
    witness.Statement :=
  ⟨witness.output_mem_declared_factors, witness.success_atLeast_twoThirds,
    witness.success_atLeast_failureBudget, witness.retry_ready,
    witness.supportsPublicBaseline⟩

/-- Internal bridge from the older source-route certificate package to the
public endpoint witness shape.  This theorem is deliberately not a public
theorem-node realization: it still consumes `PublicFactorizationCertificate`.
It exists so remaining public endpoint work can target a public witness without
letting source-piece certificates leak into the final endpoint signature. -/
def ofPublicFactorizationCertificate {N n : ℕ}
    (input : PublicInput N n)
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (cert : PublicFactorizationCertificate input.model retry modexp params) :
    PublicEndpointWitness input retry (params.toPublicBaselineBounds retry) where
  output := cert.factorReturn.output.output
  profile := exactSupportProfile retry params.modulusBits modexp
  output_mem_declared_factors :=
    cert.factorReturn.output_mem_declared_factors
  successNumerator := cert.factorReturn.successNumerator
  successDenominator := cert.factorReturn.successDenominator
  successDenominator_pos := cert.factorReturn.successDenominator_pos
  success_atLeast_twoThirds := cert.factorReturn.successAtLeastTwoThirds
  success_atLeast_failureBudget :=
    cert.successAtLeastOneMinusFailureBudget
  retry_ready := cert.resources.readiness.retryReady
  supportsPublicBaseline := cert.resources.supportsPublicBaseline

/-- Direct public-endpoint constructor from endpoint fields and reusable
modular-exponentiation resource support.  This is the resource bridge used by
the Shor public endpoint: `PrivateResourceStatementWitness` stays an internal
support theorem, while the public witness records only the exact profile and
the baseline comparison [Sho95, source.tex:1124-1148] [GE19, main.tex:70-79,
211-216, 1785-1788]. -/
def ofEndpointFieldsAndModexpWorkspaceCertificate {N n : ℕ}
    (input : PublicInput N n)
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (output : ℕ)
    (output_mem_declared_factors :
      output = input.model.leftFactor ∨ output = input.model.rightFactor)
    (successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (success_atLeast_twoThirds :
      2 * successDenominator ≤ 3 * successNumerator)
    (success_atLeast_failureBudget :
      (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
          successDenominator ≤
        retry.failureBudget.failureDenominator * successNumerator)
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input retry (params.toPublicBaselineBounds retry) where
  output := output
  profile := exactSupportProfile retry params.modulusBits modexp
  output_mem_declared_factors := output_mem_declared_factors
  successNumerator := successNumerator
  successDenominator := successDenominator
  successDenominator_pos := successDenominator_pos
  success_atLeast_twoThirds := success_atLeast_twoThirds
  success_atLeast_failureBudget := success_atLeast_failureBudget
  retry_ready := readiness.retryReady
  supportsPublicBaseline :=
    main_supportsPublicBaseline readiness hpos hshape modexpCert hlogical
      htoffoli hdepth

/-- Direct public-endpoint constructor from endpoint fields and public
Shor-style formula bounds. This is the theorem-facing resource bridge: callers
provide explicit natural-number formula obligations, not a modular-
exponentiation source-bound certificate or a prebuilt private resource witness
[Sho95, source.tex:1124-1148] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
def ofEndpointFieldsAndFormulaBounds {N n : ℕ}
    (input : PublicInput N n)
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (output : ℕ)
    (output_mem_declared_factors :
      output = input.model.leftFactor ∨ output = input.model.rightFactor)
    (successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (success_atLeast_twoThirds :
      2 * successDenominator ≤ 3 * successNumerator)
    (success_atLeast_failureBudget :
      (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
          successDenominator ≤
        retry.failureBudget.failureDenominator * successNumerator)
    (readiness : FinalResourceReadiness retry)
    (hpos : 0 < retry.runCount)
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input retry (params.toPublicBaselineBounds retry) where
  output := output
  profile := exactSupportProfile retry params.modulusBits modexp
  output_mem_declared_factors := output_mem_declared_factors
  successNumerator := successNumerator
  successDenominator := successDenominator
  successDenominator_pos := successDenominator_pos
  success_atLeast_twoThirds := success_atLeast_twoThirds
  success_atLeast_failureBudget := success_atLeast_failureBudget
  retry_ready := readiness.retryReady
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_of_formulaBounds readiness hpos
      hshape hworkspace htoffoli hdepth

/-- Selected-route-free Shor endpoint bridge from public/internal packages. It
combines the public random-base good-event package, the public-budget retry
selector, the internal order-recovery bridge, and reusable modular-
exponentiation resource support into the public endpoint witness. The signature
does not expose selected random bases, half-order gcd routes, order-recovery
certificates, repetition models, amplification certificates, or private
resource witnesses [Sho95, source.tex:1124-1148; source.tex:1132-1169;
source.tex:1614-1663; source.tex:1647-1663] [GE19, main.tex:70-79, 211-216,
1785-1788]. -/
noncomputable def ofInternalizedShorRouteAndModexpWorkspaceCertificate
    {N n : ℕ}
    (input : PublicInput N n)
    (good :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound
        input.model)
    {oneRun budget : FailureBudget}
    (retryPackage : EtaRetrySelector.PublicBudgetRetryPackage oneRun budget)
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input retryPackage.retry
      (params.toPublicBaselineBounds retryPackage.retry) := by
  let factorYield := RandomBaseFactorYieldCertificate.ofPublicGoodEvent good
  let success :=
    RetrySuccessCertificate.ofPublicOrderRecovery factorYield
      retryPackage.repetition retryPackage.amplification
  let factorReturn := success.toProbabilisticFactorReturnCertificate
  rw [retryPackage.retry_eq_spec]
  exact ofEndpointFieldsAndModexpWorkspaceCertificate input
    factorReturn.output.output
    factorReturn.output_mem_declared_factors
    factorReturn.successNumerator
    factorReturn.successDenominator
    factorReturn.successDenominator_pos
    factorReturn.successAtLeastTwoThirds
    (by
      simpa [factorReturn, RetrySuccessCertificate.toProbabilisticFactorReturnCertificate,
        retryPackage.retry_eq_spec] using
      success.successAtLeastOneMinusFailureBudget)
    (EtaRetrySelector.finalResourceReadiness budget)
    (EtaRetrySelector.runCount_pos retryPackage.hbudget)
    hshape modexpCert hlogical htoffoli hdepth

/-- Selected-route-free Shor endpoint bridge from public/internal packages and
public Shor-style formula bounds. This variant removes the modular-
exponentiation source-bound certificate from the endpoint-facing path; callers
provide explicit natural-number formula obligations instead [Sho95,
source.tex:1124-1148; source.tex:1132-1169; source.tex:1614-1663;
source.tex:1647-1663] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def ofInternalizedShorRouteAndFormulaBounds
    {N n : ℕ}
    (input : PublicInput N n)
    (good :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound
        input.model)
    {oneRun budget : FailureBudget}
    (retryPackage : EtaRetrySelector.PublicBudgetRetryPackage oneRun budget)
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input retryPackage.retry
      (params.toPublicBaselineBounds retryPackage.retry) := by
  let factorYield := RandomBaseFactorYieldCertificate.ofPublicGoodEvent good
  let success :=
    RetrySuccessCertificate.ofPublicOrderRecovery factorYield
      retryPackage.repetition retryPackage.amplification
  let factorReturn := success.toProbabilisticFactorReturnCertificate
  rw [retryPackage.retry_eq_spec]
  exact ofEndpointFieldsAndFormulaBounds input
    factorReturn.output.output
    factorReturn.output_mem_declared_factors
    factorReturn.successNumerator
    factorReturn.successDenominator
    factorReturn.successDenominator_pos
    factorReturn.successAtLeastTwoThirds
    (by
      simpa [factorReturn, RetrySuccessCertificate.toProbabilisticFactorReturnCertificate,
        retryPackage.retry_eq_spec] using
      success.successAtLeastOneMinusFailureBudget)
    (EtaRetrySelector.finalResourceReadiness budget)
    (EtaRetrySelector.runCount_pos retryPackage.hbudget)
    hshape hworkspace htoffoli hdepth

/-- Shor endpoint bridge with the random-base branch internalized from the
public semiprime input.  This wrapper is still not the final public theorem
node: retry calibration and modular-exponentiation resource support are
handled by sibling packages.  Its purpose is to ensure the endpoint caller no
longer supplies a `RandomBaseGoodEventLowerBound`; the route is split from
`input.randomBaseRoute`, with the factor-two case handled directly and the
odd-prime case routed through Shor's random-base good-event analysis [Sho95,
source.tex:1124-1148; source.tex:1132-1169; source.tex:1155-1169]. -/
noncomputable def ofPublicRandomBaseRouteAndModexpWorkspaceCertificate
    {N n : ℕ}
    (input : PublicInput N n)
    {oneRun budget : FailureBudget}
    (retryPackage : EtaRetrySelector.PublicBudgetRetryPackage oneRun budget)
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input retryPackage.retry
      (params.toPublicBaselineBounds retryPackage.retry) := by
  classical
  cases hroute : input.randomBaseRoute with
  | evenFactor factorCert =>
      rw [retryPackage.retry_eq_spec]
      exact ofEndpointFieldsAndModexpWorkspaceCertificate input
        factorCert.output
        factorCert.output_mem_declared_factors
        1
        1
        (by norm_num)
        (by norm_num)
        (by
          simp [EtaRetrySelector.spec])
        (EtaRetrySelector.finalResourceReadiness budget)
        (EtaRetrySelector.runCount_pos retryPackage.hbudget)
        hshape modexpCert hlogical htoffoli hdepth
  | oddGood good =>
      exact ofInternalizedShorRouteAndModexpWorkspaceCertificate input good
        retryPackage hshape modexpCert hlogical htoffoli hdepth

/-- Shor endpoint bridge with the random-base branch internalized from the
public semiprime input and resource support expressed as public formula
obligations. This wrapper removes both selected random-base data and modular-
exponentiation source-bound certificates from the endpoint-facing path, leaving
retry calibration to the sibling retry wrapper [Sho95, source.tex:1124-1148;
source.tex:1132-1169; source.tex:1155-1169] [GE19, main.tex:70-79, 211-216,
1785-1788]. -/
noncomputable def ofPublicRandomBaseRouteAndFormulaBounds
    {N n : ℕ}
    (input : PublicInput N n)
    {oneRun budget : FailureBudget}
    (retryPackage : EtaRetrySelector.PublicBudgetRetryPackage oneRun budget)
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input retryPackage.retry
      (params.toPublicBaselineBounds retryPackage.retry) := by
  classical
  cases hroute : input.randomBaseRoute with
  | evenFactor factorCert =>
      rw [retryPackage.retry_eq_spec]
      exact ofEndpointFieldsAndFormulaBounds input
        factorCert.output
        factorCert.output_mem_declared_factors
        1
        1
        (by norm_num)
        (by norm_num)
        (by
          simp [EtaRetrySelector.spec])
        (EtaRetrySelector.finalResourceReadiness budget)
        (EtaRetrySelector.runCount_pos retryPackage.hbudget)
        hshape hworkspace htoffoli hdepth
  | oddGood good =>
      exact ofInternalizedShorRouteAndFormulaBounds input good retryPackage
        hshape hworkspace htoffoli hdepth

/-- Shor endpoint bridge with both random-base routing and retry calibration
internalized from public data.  This wrapper is still not the final public
private theorem node because modular-exponentiation resource support remains a sibling
package, but it no longer asks callers for `RandomBaseGoodEventLowerBound`,
`PublicBudgetRetryPackage`, `RepetitionModel`, or
`RetryAmplificationCertificate` [Sho95, source.tex:1124-1148;
source.tex:1132-1169; source.tex:1155-1169; source.tex:1647-1663]. -/
noncomputable def ofPublicRandomBaseAndRetryBudgetAndModexpWorkspaceCertificate
    {N n : ℕ}
    (input : PublicInput N n)
    (oneRun budget : FailureBudget)
    (hbudget : EtaRetrySelector.WellFormed budget)
    (honeRun : oneRun.WellFormed)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator)
    (hbudgetThird :
      3 * budget.failureNumerator ≤ budget.failureDenominator)
    {modexp : ModularExponentiation.ResourceParameters}
    {modexpBounds : ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (modexpCert :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        modexp modexpBounds)
    (hlogical :
      modexpBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      modexpBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      modexpBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      (params.toPublicBaselineBounds (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseRouteAndModexpWorkspaceCertificate input
    (EtaRetrySelector.publicBudgetRetryPackage oneRun budget hbudget honeRun
      honeHalf hbudgetThird)
    hshape modexpCert hlogical htoffoli hdepth

/-- Shor endpoint bridge with random-base routing, retry calibration, and
resource formula support internalized to theorem-facing public data. This is
the clean assembly point before the final theorem-shape promotion audit:
it takes public semiprime input, public failure-budget inequalities, and
explicit public formula-bound obligations, not selected-route certificates,
retry packages, modular-exponentiation source-bound certificates, private
resource witnesses, or a prebuilt endpoint witness [Sho95, source.tex:1124-1148;
source.tex:1132-1169; source.tex:1155-1169; source.tex:1647-1663] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def ofPublicRandomBaseAndRetryBudgetAndFormulaBounds
    {N n : ℕ}
    (input : PublicInput N n)
    (oneRun budget : FailureBudget)
    (hbudget : EtaRetrySelector.WellFormed budget)
    (honeRun : oneRun.WellFormed)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator)
    (hbudgetThird :
      3 * budget.failureNumerator ≤ budget.failureDenominator)
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (hshape : ModExpRegisterShape params.modulusBits modexp)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      (params.toPublicBaselineBounds (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseRouteAndFormulaBounds input
    (EtaRetrySelector.publicBudgetRetryPackage oneRun budget hbudget honeRun
      honeHalf hbudgetThird)
    hshape hworkspace htoffoli hdepth

/-- Shor endpoint bridge with the route, retry, and resource support packages
internalized to theorem-facing public fields. The modular-exponentiation register shape is
constructed from explicit resource-field equalities, so the endpoint signature
does not expose `ModExpRegisterShape` as an external certificate [Sho95,
source.tex:1124-1148; source.tex:1132-1169; source.tex:1155-1169;
source.tex:1647-1663] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def ofPublicRandomBaseAndRetryBudgetAndFormulaFields
    {N n : ℕ}
    (input : PublicInput N n)
    (oneRun budget : FailureBudget)
    (hbudget : EtaRetrySelector.WellFormed budget)
    (honeRun : oneRun.WellFormed)
    (honeHalf :
      2 * oneRun.failureNumerator ≤ oneRun.failureDenominator)
    (hbudgetThird :
      3 * budget.failureNumerator ≤ budget.failureDenominator)
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (hmodulusBits : modexp.modulusBits = params.modulusBits)
    (hexponentWidth : modexp.exponentWidth = 2 * params.modulusBits)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      (params.toPublicBaselineBounds (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseAndRetryBudgetAndFormulaBounds input oneRun budget hbudget
    honeRun honeHalf hbudgetThird
    (hshape :=
      { modulusBits_eq := hmodulusBits
        exponentWidth_eq := by
          rw [hexponentWidth] })
    hworkspace htoffoli hdepth

/-- Shor endpoint bridge with the route and retry domain normalized to public
data.  The one-run half-failure budget is selected internally, so this wrapper
does not ask callers for a one-run budget, a retry package, a repetition model,
or a retry-amplification certificate.  Modular-exponentiation resource fields
and public formula parameters remain explicit here; the final theorem endpoint
must hide them behind source-backed baseline definitions [Sho95,
source.tex:1124-1148; source.tex:1132-1169; source.tex:1155-1169;
source.tex:1647-1663] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def ofPublicRandomBaseAndPublicFailureBudgetAndFormulaFields
    {N n : ℕ}
    (input : PublicInput N n)
    (budget : FailureBudget)
    (hbudget : EtaRetrySelector.PublicFailureBudget budget)
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (hmodulusBits : modexp.modulusBits = params.modulusBits)
    (hexponentWidth : modexp.exponentWidth = 2 * params.modulusBits)
    (hworkspace :
      modularExponentiationWorkspaceAddend params.modulusBits modexp ≤
        params.workspaceAddendBound)
    (htoffoli : modexp.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : modexp.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      (params.toPublicBaselineBounds (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseAndRetryBudgetAndFormulaFields input
    EtaRetrySelector.halfFailureOneRunBudget budget hbudget.hbudget
    EtaRetrySelector.halfFailureOneRunBudget_wellFormed
    EtaRetrySelector.halfFailureOneRunBudget_atMostHalf hbudget.hbudgetThird
    hmodulusBits hexponentWidth hworkspace htoffoli hdepth

/-- Endpoint wrapper consuming a source-backed modular-exponentiation package
instead of raw modular-exponentiation resource fields.  The formula parameters
remain visible here as an explicit public-bound layer. -/
noncomputable def ofPublicRandomBaseAndPublicFailureBudgetAndSourceBackedModexpPackage
    {N n : ℕ}
    (input : PublicInput N n)
    (budget : FailureBudget)
    (hbudget : EtaRetrySelector.PublicFailureBudget budget)
    {params : PublicBaselineBounds.FormulaParameters}
    (pkg : SourceBackedModexpResourcePackage params) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      (params.toPublicBaselineBounds (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseAndPublicFailureBudgetAndFormulaFields input budget hbudget
    pkg.registerShape.modulusBits_eq pkg.registerShape.exponentWidth_eq
    pkg.workspaceAddend_le
    ((pkg.sourceCertificate.supportsUpperBound).toffoliGates_le.trans
      pkg.toffoliGates_le)
    ((pkg.sourceCertificate.supportsUpperBound).circuitDepth_le.trans
      pkg.circuitDepth_le)

/-- Endpoint wrapper using a named public baseline envelope instead of exposing
the internal formula-parameter record.  The source-backed modular-
exponentiation package is still a support object, so public theorem realizations
should construct it internally [Sho95, source.tex:1124-1148] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def ofPublicRandomBaseAndPublicFailureBudgetAndBaselineEnvelope
    {N n : ℕ}
    (input : PublicInput N n)
    (budget : FailureBudget)
    (hbudget : EtaRetrySelector.PublicFailureBudget budget)
    (envelope : PublicBaselineBounds.Envelope)
    (pkg : SourceBackedModexpResourcePackage envelope.internalParams) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      (envelope.toPublicBaselineBounds (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseAndPublicFailureBudgetAndSourceBackedModexpPackage input
    budget hbudget pkg

/-- Endpoint wrapper using the canonical VBE modular-exponentiation package and
a named public baseline envelope.  The signature hides the reusable MAU package
object from endpoint users; the remaining proof obligations are exactly the
fieldwise comparisons between the canonical VBE route and the selected public
formula envelope [Sho95, source.tex:1124-1148] [VBE95,
9511018.tex:372-416] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def ofPublicRandomBaseAndPublicFailureBudgetAndVBEEnvelope
    {N n : ℕ}
    (input : PublicInput N n)
    (budget : FailureBudget)
    (hbudget : EtaRetrySelector.PublicFailureBudget budget)
    (envelope : PublicBaselineBounds.Envelope)
    (hmodulusBits_pos : 0 < envelope.modulusBits)
    (hlogical :
      (ModularExponentiation.VBECounting.vbeModularExponentiationBounds
          (2 * envelope.modulusBits) envelope.modulusBits).toProfile.logicalQubits ≤
        envelope.internalParams.logicalQubitBound)
    (htoffoli :
      (ModularExponentiation.VBECounting.vbeModularExponentiationBounds
          (2 * envelope.modulusBits) envelope.modulusBits).toProfile.toffoliGates ≤
        envelope.internalParams.toffoliBaseBound)
    (hdepth :
      (ModularExponentiation.VBECounting.vbeModularExponentiationBounds
          (2 * envelope.modulusBits) envelope.modulusBits).toProfile.circuitDepth ≤
        envelope.internalParams.circuitDepthBaseBound) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      (envelope.toPublicBaselineBounds (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseAndPublicFailureBudgetAndBaselineEnvelope input budget hbudget envelope
    (SourceBackedModexpResourcePackage.ofVBECounting envelope.internalParams
      hmodulusBits_pos hlogical htoffoli hdepth)

/-- Endpoint wrapper using the canonical VBE modular-exponentiation envelope.
The endpoint caller supplies only the public factoring input and public retry
budget; the VBE envelope and its comparison proofs are selected internally
[Sho95, source.tex:1124-1148] [VBE95, 9511018.tex:372-416] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def ofPublicRandomBaseAndPublicFailureBudgetAndCanonicalVBEEnvelope
    {N n : ℕ}
    (input : PublicInput N n)
    (budget : FailureBudget)
    (hbudget : EtaRetrySelector.PublicFailureBudget budget)
    (hmodulusBits_pos : 0 < n) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      ((PublicBaselineBounds.Envelope.vbeModexpEnvelope n).toPublicBaselineBounds
        (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseAndPublicFailureBudgetAndBaselineEnvelope input budget hbudget
    (PublicBaselineBounds.Envelope.vbeModexpEnvelope n)
    (PublicBaselineBounds.Envelope.vbeModexpPackage n hmodulusBits_pos)

/-- Endpoint wrapper using the canonical VBE modular-exponentiation envelope,
with the positive bit-length fact derived from the public input window. -/
noncomputable def ofPublicInputAndPublicFailureBudgetAndCanonicalVBEEnvelope
    {N n : ℕ}
    (input : PublicInput N n)
    (budget : FailureBudget)
    (hbudget : EtaRetrySelector.PublicFailureBudget budget) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      ((PublicBaselineBounds.Envelope.vbeModexpEnvelope n).toPublicBaselineBounds
        (EtaRetrySelector.spec budget)) :=
  ofPublicRandomBaseAndPublicFailureBudgetAndCanonicalVBEEnvelope input budget
    hbudget input.modulusBits_pos

end PublicEndpointWitness

/-- Public theorem-node candidate for the Shor-style RSA factorization route.
The theorem-facing inputs are the public semiprime/bit-length carrier and the
public failure-budget carrier. Random-base routing, retry calibration, and the
canonical VBE modular-exponentiation envelope are selected internally [Sho95,
source.tex:1124-1148, 1132-1169, 1647-1663] [VBE95, 9511018.tex:372-416]
[GE19, main.tex:70-79, 211-216, 1785-1788]. -/
noncomputable def main {N n : ℕ}
    (input : PublicInput N n)
    (budget : FailureBudget)
    (hbudget : EtaRetrySelector.PublicFailureBudget budget) :
    PublicEndpointWitness input (EtaRetrySelector.spec budget)
      ((PublicBaselineBounds.Envelope.vbeModexpEnvelope n).toPublicBaselineBounds
        (EtaRetrySelector.spec budget)) :=
  PublicEndpointWitness.ofPublicInputAndPublicFailureBudgetAndCanonicalVBEEnvelope
    input budget hbudget

/-- Assemble the public Shor-style factorization certificate from the
source-shaped success certificate and the exact-resource support witness. This
is the route constructor used to avoid treating the probabilistic factor-return
certificate as an unexplained external input [Sho95, source.tex:1124-1148,
source.tex:1630-1663]. -/
def PublicFactorizationCertificate.ofSourceRoute
    {N : ℕ} {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (success : RetrySuccessCertificate model retry)
    (resources : PrivateResourceStatementWitness retry modexp params) :
    PublicFactorizationCertificate model retry modexp params where
  factorReturn := success.toProbabilisticFactorReturnCertificate
  repetition := success.repetition
  successAtLeastOneMinusFailureBudget :=
    success.successAtLeastOneMinusFailureBudget
  resources := resources

/-- Public endpoint for the Shor-style RSA factor-recovery statement. The
source route supplies a factor-return certificate and a retry/failure
certificate; the exact-resource support witness then projects to the public
natural-number baseline fields without asymptotic metrics. The source route is
Shor's factoring-by-order-finding reduction and continued-fraction
post-processing [Sho95, source.tex:1124-1148, 1630-1663]. -/
theorem main_factorization
    {N : ℕ} {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (cert : PublicFactorizationCertificate model retry modexp params) :
    (cert.factorReturn.output.output = model.leftFactor ∨
        cert.factorReturn.output.output = model.rightFactor) ∧
      2 * cert.factorReturn.successDenominator ≤
        3 * cert.factorReturn.successNumerator ∧
      (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
          cert.factorReturn.successDenominator ≤
        retry.failureBudget.failureDenominator *
          cert.factorReturn.successNumerator ∧
      cert.repetition.failureNumerator * retry.failureBudget.failureDenominator ≤
        retry.failureBudget.failureNumerator * cert.repetition.failureDenominator ∧
      retry.readyForFinalStatement = true ∧
      SupportsPublicBaseline
        (exactSupportProfile retry params.modulusBits modexp)
        (params.toPublicBaselineBounds retry) :=
  ⟨cert.factorReturn.output_mem_declared_factors,
    cert.factorReturn.successAtLeastTwoThirds,
    cert.successAtLeastOneMinusFailureBudget,
    cert.repetition.satisfies_failureBudget,
    cert.resources.readiness.retryReady,
    cert.resources.supportsPublicBaseline⟩

/-- The expanded public endpoint proves the packaged public consequence
predicate used by the existential theorem-node wrapper [Sho95,
source.tex:1124-1148, 1630-1663] [GE19, main.tex:70-79, 211-216,
1785-1788]. -/
theorem main_factorization_statement
    {N : ℕ} {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (cert : PublicFactorizationCertificate model retry modexp params) :
    PublicFactorizationCertificate.Statement cert := by
  simpa [PublicFactorizationCertificate.Statement] using main_factorization cert

/-- Source-route projection into the Shor-style factorization consequence. This
support theorem still consumes source-shaped success and resource witnesses; it
is not the public theorem-node endpoint [Sho95, source.tex:1124-1148,
1630-1663] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
theorem sourceRoute_factorization_statement
    {N : ℕ} {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (success : RetrySuccessCertificate model retry)
    (resources : PrivateResourceStatementWitness retry modexp params) :
    let cert := PublicFactorizationCertificate.ofSourceRoute success resources
    (cert.factorReturn.output.output = model.leftFactor ∨
        cert.factorReturn.output.output = model.rightFactor) ∧
      2 * cert.factorReturn.successDenominator ≤
        3 * cert.factorReturn.successNumerator ∧
      (retry.failureBudget.failureDenominator - retry.failureBudget.failureNumerator) *
          cert.factorReturn.successDenominator ≤
        retry.failureBudget.failureDenominator *
          cert.factorReturn.successNumerator ∧
      cert.repetition.failureNumerator * retry.failureBudget.failureDenominator ≤
        retry.failureBudget.failureNumerator *
          cert.repetition.failureDenominator ∧
      retry.readyForFinalStatement = true ∧
      SupportsPublicBaseline
        (exactSupportProfile retry params.modulusBits modexp)
        (params.toPublicBaselineBounds retry) :=
  main_factorization (PublicFactorizationCertificate.ofSourceRoute success resources)

/-- Existential source-piece bridge for the Shor-style route. The theorem
constructs a public factorization certificate from factor-yield,
order-recovery, repetition, retry-amplification, and exact-resource support
pieces, then exposes the packaged consequence predicate. It remains a support
bridge because it consumes source-piece witnesses [Sho95, source.tex:1124-1148,
source.tex:1132-1169, source.tex:1614-1663, source.tex:1647-1663] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
theorem sourcePieces_factorization_exists_statement
    {N : ℕ} {model : ShorFactoring.SemiprimeFactorModel N}
    {retry : RetryMultiplierSpec}
    {modexp : ModularExponentiation.ResourceParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    {orderRecoverySuccessNumerator orderRecoverySuccessDenominator : ℕ}
    (factorYield : RandomBaseFactorYieldCertificate model)
    (orderRecoverySource :
      OrderRecoveryRationalFieldCertificate factorYield.order
        orderRecoverySuccessNumerator orderRecoverySuccessDenominator)
    (repetition : RetryMultiplierSpec.RepetitionModel retry)
    (amplification : RetryAmplificationCertificate retry)
    (resources : PrivateResourceStatementWitness retry modexp params) :
    ∃ cert : PublicFactorizationCertificate model retry modexp params,
      PublicFactorizationCertificate.Statement cert := by
  let success :=
    RetrySuccessCertificate.ofSourcePieces factorYield orderRecoverySource
      repetition amplification
  let cert := PublicFactorizationCertificate.ofSourceRoute success resources
  exact ⟨cert, main_factorization_statement cert⟩

end ShorStyle
end Factoring
end QuantumAlg
