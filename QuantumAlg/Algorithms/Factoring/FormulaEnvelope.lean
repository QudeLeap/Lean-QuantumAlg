/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.Factoring.ShorStyle
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle

/-!
# RSA factoring formula envelopes

This module records source-formula envelopes that are useful for comparing
published RSA resource estimates with the exact-resource support API.  These
envelopes deliberately keep their source status separate from the natural-number
formula fields: a concrete formula copied from an estimate is not automatically
an exact count or a theorem-level upper-bound function.

The concrete RSA formula families currently mirrored here come from the
Gidney-Ekera abstract RSA resource estimate and impact tables [GE19,
main.tex:70-79, 710-733, 1073-1110].
-/

@[expose] public section

namespace QuantumAlg
namespace Factoring

/-! ## Shared formula-envelope status -/

namespace FormulaEnvelope

/-- Quantum resource dimensions tracked by the RSA public baseline formulas. -/
structure QuantumFields where
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ℕ
  /-- Gate-count component for Toffoli gates. -/
  toffoliGates : ℕ
  /-- Depth component for circuit depth. -/
  circuitDepth : ℕ
deriving DecidableEq

/-- Source status for each quantum formula field in a baseline envelope. -/
structure QuantumStatus where
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ResourceFormulaStatus
  /-- Gate-count component for Toffoli gates. -/
  toffoliGates : ResourceFormulaStatus
  /-- Depth component for circuit depth. -/
  circuitDepth : ResourceFormulaStatus
deriving DecidableEq

namespace QuantumStatus

/-- The status attached to formula fields copied from a published estimate:
the fields are concrete natural-number expressions, but they still need an
exact-count or explicit-upper-bound pass before they can instantiate a final
resource theorem. -/
def sourceBackedEstimate : QuantumStatus where
  logicalQubits := .sourceBackedEstimate
  toffoliGates := .sourceBackedEstimate
  circuitDepth := .sourceBackedEstimate

/-- Status when every tracked formula field has been justified as a concrete
upper-bound function. -/
def explicitUpperBounds : QuantumStatus where
  logicalQubits := .explicitUpperBound
  toffoliGates := .explicitUpperBound
  circuitDepth := .explicitUpperBound

/-- Whether the formula-field statuses are strong enough for a final
exact-resource theorem. -/
def readyForFinalStatement (status : QuantumStatus) : Bool :=
  status.logicalQubits.admissibleAsExactResource &&
    status.toffoliGates.admissibleAsExactResource &&
      status.circuitDepth.admissibleAsExactResource

@[simp] theorem sourceBackedEstimate_not_ready :
    sourceBackedEstimate.readyForFinalStatement = false :=
  rfl

@[simp] theorem explicitUpperBounds_ready :
    explicitUpperBounds.readyForFinalStatement = true :=
  rfl

end QuantumStatus

/-- A formula envelope pairs the natural-number baseline fields with their
source status. -/
structure QuantumEnvelope where
  /-- Underlying quantum resource fields carried by the envelope. -/
  fields : QuantumFields
  /-- Formula status or readiness status carried by this record. -/
  status : QuantumStatus
deriving DecidableEq

namespace QuantumEnvelope

/-- Whether the envelope may instantiate a final exact-resource target. -/
def readyForFinalStatement (envelope : QuantumEnvelope) : Bool :=
  envelope.status.readyForFinalStatement

/-- Re-tag an envelope once every formula field has been justified as a concrete
upper-bound function. This does not change the numeric fields. -/
def asExplicitUpperBounds (envelope : QuantumEnvelope) : QuantumEnvelope where
  fields := envelope.fields
  status := QuantumStatus.explicitUpperBounds

@[simp] theorem asExplicitUpperBounds_fields (envelope : QuantumEnvelope) :
    envelope.asExplicitUpperBounds.fields = envelope.fields :=
  rfl

@[simp] theorem asExplicitUpperBounds_ready (envelope : QuantumEnvelope) :
    envelope.asExplicitUpperBounds.readyForFinalStatement = true :=
  rfl

end QuantumEnvelope

/-! ## Shor-style baseline formula envelope -/

namespace ShorStyle

/-- Source-estimate envelope for the Shor-style public baseline formula fields.
The fields are concrete natural-number expressions; their status records that a
later exact-resource pass must justify them before final use. The baseline shape
tracks the Shor order-finding route and GE19 RSA resource formulas [Sho95,
source.tex:1124-1148] [GE19, main.tex:70-79, 211-216, 1785-1788]. -/
def sourceEstimateEnvelope
    (params : Factoring.ShorStyle.PublicBaselineBounds.FormulaParameters) :
    QuantumEnvelope where
  fields :=
    { logicalQubits := params.logicalQubitBound
      toffoliGates := params.toffoliBaseBound
      circuitDepth := params.circuitDepthBaseBound }
  status := QuantumStatus.sourceBackedEstimate

@[simp] theorem sourceEstimateEnvelope_logicalQubits
    (params : Factoring.ShorStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).fields.logicalQubits =
      params.logicalQubitBound :=
  rfl

@[simp] theorem sourceEstimateEnvelope_toffoliGates
    (params : Factoring.ShorStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).fields.toffoliGates =
      params.toffoliBaseBound :=
  rfl

@[simp] theorem sourceEstimateEnvelope_circuitDepth
    (params : Factoring.ShorStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).fields.circuitDepth =
      params.circuitDepthBaseBound :=
  rfl

@[simp] theorem sourceEstimateEnvelope_not_ready
    (params : Factoring.ShorStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).readyForFinalStatement = false :=
  rfl

end ShorStyle

/-! ## Ekera-Hastad baseline formula envelope -/

namespace EkeraHastadStyle

/-- Source-estimate envelope for the Ekera-Hastad public baseline formula
fields. The fields are concrete natural-number expressions; their status
records that a later exact-resource pass must justify them before final use. The
route follows the short-DLP RSA reduction and GE19's RSA estimate tables [EH17,
source.tex:878-953] [GE19, main.tex:70-79, 1100-1108, 1785-1788]. -/
def sourceEstimateEnvelope
    (params :
      Factoring.EkeraHastadStyle.PublicBaselineBounds.FormulaParameters) :
    QuantumEnvelope where
  fields :=
    { logicalQubits := params.logicalQubitBound
      toffoliGates := params.toffoliBaseBound
      circuitDepth := params.circuitDepthBaseBound }
  status := QuantumStatus.sourceBackedEstimate

@[simp] theorem sourceEstimateEnvelope_logicalQubits
    (params :
      Factoring.EkeraHastadStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).fields.logicalQubits =
      params.logicalQubitBound :=
  rfl

@[simp] theorem sourceEstimateEnvelope_toffoliGates
    (params :
      Factoring.EkeraHastadStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).fields.toffoliGates =
      params.toffoliBaseBound :=
  rfl

@[simp] theorem sourceEstimateEnvelope_circuitDepth
    (params :
      Factoring.EkeraHastadStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).fields.circuitDepth =
      params.circuitDepthBaseBound :=
  rfl

@[simp] theorem sourceEstimateEnvelope_not_ready
    (params :
      Factoring.EkeraHastadStyle.PublicBaselineBounds.FormulaParameters) :
    (sourceEstimateEnvelope params).readyForFinalStatement = false :=
  rfl

end EkeraHastadStyle

/-! ## RSA-2048 logical-resource terminal profile -/

namespace RSA2048

/-- The RSA-2048 modulus bit length used by the terminal logical-resource
estimate. -/
def modulusBits : ℕ := 2048

/-- Natural-number upper bound for `log_2 2048`, used by the abstract GE19
formula envelope [GE19, main.tex:78, 211-216]. -/
def logModulusBitsUpperBound : ℕ := 11

/-- GE19 RSA-2048 logical-qubit baseline `6.19 * 10^3`, stored as an integer
count for the terminal RSA-2048 resource profile [GE19, main.tex:78, 211-216]. -/
def logicalQubits : ℕ := 6190

/-- GE19 RSA-2048 Toffoli baseline `2.7 * 10^9`, stored as an integer count.
GE19 records that this count is not adjusted for retry chance [GE19,
main.tex:211-216, 1785-1788]. -/
def toffoliGates : ℕ := 2700000000

/-- GE19 RSA-2048 maximal circuit-depth baseline `2.14 * 10^9`, stored as an
integer count by evaluating the abstract depth formula at `n = 2048` [GE19,
main.tex:78, 211-216]. -/
def circuitDepth : ℕ := 2140000000

/-- The external factor-return certificate target is at least `2/3`, so the
support profile records a one-third failure budget. GE19's RSA-2048 tuple below
is still only a source estimate: it assumes one quantum run for the seven-hour
logical estimate and does not itself discharge this factor-return success
certificate [GE19, main.tex:888-889, 1785-1788]. -/
def failureBudget : FailureBudget where
  failureNumerator := 1
  failureDenominator := 3

/-- Public one-third failure budget for the terminal RSA-2048 theorem. -/
theorem failureBudget_wellFormed : failureBudget.WellFormed := by
  constructor <;> norm_num [failureBudget]

/-- Public Shor retry-budget side conditions for the terminal RSA-2048 theorem.
The final retry selector is the same eta selector used by the generic Shor
endpoint, not the one-run GE19 source estimate [Sho95, source.tex:1647-1663]. -/
theorem publicFailureBudget :
    ShorStyle.EtaRetrySelector.PublicFailureBudget failureBudget where
  hbudget := ⟨failureBudget_wellFormed, by norm_num [failureBudget]⟩
  hbudgetThird := by norm_num [failureBudget]

/-- Retry multiplier selected by the public Shor eta selector for the
RSA-2048 one-third failure budget. For this budget the concrete multiplier is
`3`; this is the success-accounting multiplier for the final theorem, distinct
from the one-run GE19 source estimate [Sho95, source.tex:1647-1663] [GE19,
main.tex:888-889, 1785-1788]. -/
def retry : RetryMultiplierSpec :=
  ShorStyle.EtaRetrySelector.spec failureBudget

/-- RSA-2048 input class for the terminal source-estimate endpoint.  The
resource tuple below is specialized at the fixed 2048-bit modulus size; this
record keeps the semiprime model and the bit-length window explicit instead of
silently accepting arbitrary semiprimes [GE19, main.tex:70-79, 211-216]. -/
structure InputClass where
  /-- Public RSA modulus. -/
  modulus : ℕ
  /-- Semiprime factor model for the public modulus. -/
  model : ShorFactoring.SemiprimeFactorModel modulus
  /-- Lower endpoint of the 2048-bit modulus window. -/
  modulus_lower : 2 ^ (modulusBits - 1) ≤ modulus
  /-- Upper endpoint of the 2048-bit modulus window. -/
  modulus_upper : modulus < 2 ^ modulusBits

/-- Success-accounted multiplier selected for the final RSA-2048 theorem. This
is not the GE19 one-run source-estimate multiplier; it is the public Shor eta
selector's concrete retry count for failure budget `1/3` [Sho95,
source.tex:1647-1663] [GE19, main.tex:1785-1788]. -/
def successAccountedMultiplier : ℕ := retry.runCount

/-- One-run classical arithmetic operation count attached to the RSA-2048
Shor-style factor-recovery workflow using the explicit arithmetic-operation
taxonomy and the Shor-style post-processing upper-bound function [Sho95,
source.tex:1124-1148, 1630-1663]. -/
def classicalArithmeticOpsPerRun : ℕ :=
  ShorStyle.ClassicalPostProcessingParameters.shorPerRunUpperBoundTotal modulusBits

/-- Success-accounted classical arithmetic operation count under the selected
public Shor retry multiplier [Sho95, source.tex:1647-1663]. -/
def classicalArithmeticOps : ℕ :=
  ShorStyle.ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
    retry modulusBits

/-- GE19 one-run logical-resource tuple for RSA-2048. These fields are the
source-backed estimate and are not success-accounted [GE19, main.tex:78,
211-216, 1785-1788]. -/
def logicalResourceEstimate : QuantumFields where
  logicalQubits := logicalQubits
  toffoliGates := toffoliGates
  circuitDepth := circuitDepth

/-- Final success-accounted RSA-2048 resource tuple obtained by applying the
selected public Shor retry multiplier to the counted run-sensitive fields.
Logical qubits record the live footprint and therefore are not multiplied by
sequential retries [Sho95, source.tex:1647-1663] [GE19, main.tex:70-79,
211-216, 1785-1788]. -/
def finalLogicalResourceEstimate : QuantumFields where
  logicalQubits := logicalQubits
  toffoliGates := successAccountedMultiplier * toffoliGates
  circuitDepth := successAccountedMultiplier * circuitDepth

/-- The terminal profile together with its source status. The quantum fields
remain source-backed estimates, while the concrete classical count is exposed
by `classicalArithmeticOps`. -/
def sourceEstimateEnvelope : QuantumEnvelope where
  fields := logicalResourceEstimate
  status := QuantumStatus.sourceBackedEstimate

/-- Final success-accounted RSA-2048 resource envelope for the selected public
Shor retry model. The envelope is separate from the GE19 source-estimate
envelope: counted run-sensitive fields use `retry.runCount`, while live
footprint remains the GE19 logical-qubit count [Sho95, source.tex:1647-1663]
[GE19, main.tex:70-79, 211-216, 1785-1788]. -/
def finalSuccessAccountedEnvelope : QuantumEnvelope where
  fields := finalLogicalResourceEstimate
  status := QuantumStatus.explicitUpperBounds

@[simp] theorem retry_runCount : retry.runCount = 3 :=
  rfl

@[simp] theorem retry_ready : retry.readyForFinalStatement = true :=
  rfl

/-- Repetition model selected by the public Shor eta selector for the terminal
RSA-2048 failure budget. The powered repeated-failure arithmetic is constructed
from the canonical one-run half-failure bound, giving a concrete three-run
upper-bound multiplier for the public one-third failure budget [Sho95,
source.tex:1647-1663]. -/
def retryRepetitionModel : RetryMultiplierSpec.RepetitionModel retry where
  failureNumerator :=
    (publicFailureBudget.toPublicBudgetRetryPackage).repetition.failureNumerator
  failureDenominator :=
    (publicFailureBudget.toPublicBudgetRetryPackage).repetition.failureDenominator
  failureDenominator_pos :=
    (publicFailureBudget.toPublicBudgetRetryPackage).repetition.failureDenominator_pos
  failure_le_budget :=
    (publicFailureBudget.toPublicBudgetRetryPackage).repetition.failure_le_budget
  runCount_pos :=
    (publicFailureBudget.toPublicBudgetRetryPackage).repetition.runCount_pos
  ready := (publicFailureBudget.toPublicBudgetRetryPackage).repetition.ready

/-- Terminal RSA-2048 retry-amplification arithmetic from the public Shor eta
selector. The success numerator/denominator are derived from the repeated
half-failure fields instead of being asserted as an independent `2/3` record
[Sho95, source.tex:1647-1663]. -/
def retryAmplificationCertificate : ShorStyle.RetryAmplificationCertificate retry :=
  (publicFailureBudget.toPublicBudgetRetryPackage).amplification

@[simp] theorem successAccountedMultiplier_eq_three :
    successAccountedMultiplier = 3 :=
  rfl

@[simp] theorem logicalResourceEstimate_logicalQubits :
    logicalResourceEstimate.logicalQubits = 6190 :=
  rfl

@[simp] theorem logicalResourceEstimate_toffoliGates :
    logicalResourceEstimate.toffoliGates = 2700000000 :=
  rfl

@[simp] theorem logicalResourceEstimate_circuitDepth :
    logicalResourceEstimate.circuitDepth = 2140000000 :=
  rfl

@[simp] theorem classicalArithmeticOpsPerRun_eq :
    classicalArithmeticOpsPerRun = 12302 := by
  norm_num [classicalArithmeticOpsPerRun,
    ShorStyle.ClassicalPostProcessingParameters.shorPerRunUpperBoundTotal,
    modulusBits]

@[simp] theorem classicalArithmeticOps_eq :
    classicalArithmeticOps = 36906 := by
  norm_num [classicalArithmeticOps,
    ShorStyle.ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal,
    ShorStyle.ClassicalPostProcessingParameters.shorPerRunUpperBoundTotal,
    retry, ShorStyle.EtaRetrySelector.spec, failureBudget, modulusBits]

@[simp] theorem sourceEstimateEnvelope_not_ready :
    sourceEstimateEnvelope.readyForFinalStatement = false :=
  rfl

@[simp] theorem finalSuccessAccountedEnvelope_ready :
    finalSuccessAccountedEnvelope.readyForFinalStatement = true :=
  rfl

@[simp] theorem finalSuccessAccountedEnvelope_logicalQubits :
    finalSuccessAccountedEnvelope.fields.logicalQubits = 6190 :=
  rfl

@[simp] theorem finalSuccessAccountedEnvelope_toffoliGates :
    finalSuccessAccountedEnvelope.fields.toffoliGates =
      retry.runCount * 2700000000 :=
  rfl

private theorem finalSuccessAccountedEnvelope_toffoliGates_concrete :
    finalSuccessAccountedEnvelope.fields.toffoliGates = 8100000000 := by
  norm_num [finalSuccessAccountedEnvelope, finalLogicalResourceEstimate,
    successAccountedMultiplier, retry, ShorStyle.EtaRetrySelector.spec,
    failureBudget, toffoliGates]

@[simp] theorem finalSuccessAccountedEnvelope_circuitDepth :
    finalSuccessAccountedEnvelope.fields.circuitDepth =
      retry.runCount * 2140000000 :=
  rfl

private theorem finalSuccessAccountedEnvelope_circuitDepth_concrete :
    finalSuccessAccountedEnvelope.fields.circuitDepth = 6420000000 := by
  norm_num [finalSuccessAccountedEnvelope, finalLogicalResourceEstimate,
    successAccountedMultiplier, retry, ShorStyle.EtaRetrySelector.spec,
    failureBudget, circuitDepth]

private theorem finalClassicalArithmeticOps_eq_retryBound :
    classicalArithmeticOps =
      ShorStyle.ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
        retry modulusBits :=
  rfl

/-- Final success-accounted RSA-2048 resource-field package. The theorem ties
the quantum fields and classical arithmetic count to the same selected retry
multiplier used by the Shor success certificate, while keeping the numerical
source tuple traceable to GE19 and the retry route traceable to Shor [Sho95,
source.tex:1647-1663] [GE19, main.tex:70-79, 211-216, 888-889,
1785-1788]. -/
private theorem finalSuccessAccountedFields :
    finalSuccessAccountedEnvelope.fields.logicalQubits = 6190 ∧
      finalSuccessAccountedEnvelope.fields.toffoliGates =
        retry.runCount * 2700000000 ∧
      finalSuccessAccountedEnvelope.fields.circuitDepth =
        retry.runCount * 2140000000 ∧
      classicalArithmeticOps =
        ShorStyle.ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
          retry modulusBits ∧
      retry.readyForFinalStatement = true ∧
      finalSuccessAccountedEnvelope.readyForFinalStatement = true :=
  ⟨finalSuccessAccountedEnvelope_logicalQubits,
    finalSuccessAccountedEnvelope_toffoliGates,
    finalSuccessAccountedEnvelope_circuitDepth,
    finalClassicalArithmeticOps_eq_retryBound,
    retry_ready,
    finalSuccessAccountedEnvelope_ready⟩

/-- Concrete final RSA-2048 success-accounted resource-field values under the
public Shor eta selector for failure budget `1/3`. The GE19 one-run Toffoli and
depth fields are multiplied by the selected retry count `3`, while the live
logical-qubit footprint is unchanged [Sho95, source.tex:1647-1663] [GE19,
main.tex:70-79, 211-216, 1785-1788]. -/
private theorem finalSuccessAccountedConcreteFields :
    finalSuccessAccountedEnvelope.fields.logicalQubits = 6190 ∧
      finalSuccessAccountedEnvelope.fields.toffoliGates = 8100000000 ∧
      finalSuccessAccountedEnvelope.fields.circuitDepth = 6420000000 ∧
      classicalArithmeticOps = 36906 ∧
      retry.runCount = 3 ∧
      retry.readyForFinalStatement = true ∧
      finalSuccessAccountedEnvelope.readyForFinalStatement = true :=
  ⟨finalSuccessAccountedEnvelope_logicalQubits,
    finalSuccessAccountedEnvelope_toffoliGates_concrete,
    finalSuccessAccountedEnvelope_circuitDepth_concrete,
    classicalArithmeticOps_eq,
    retry_runCount,
    retry_ready,
    finalSuccessAccountedEnvelope_ready⟩

/-! ### RSA-2048 public theorem shape -/

/-- Convert the terminal RSA-2048 input carrier to the generic Shor-style public
input shape. The fixed bit length is the RSA-2048 modulus window used by the
logical-resource estimate [Sho95, source.tex:1124-1148] [GE19, main.tex:70-79,
211-216]. -/
def toShorPublicInput (input : InputClass) :
    ShorStyle.PublicInput input.modulus modulusBits where
  model := input.model
  modulus_lower := input.modulus_lower
  modulus_upper := input.modulus_upper

/-- Public Shor endpoint specialized to RSA-2048's one-third failure budget.
Random-base routing, the one-run half-failure budget, retry calibration, and the
canonical generic Shor success route are selected internally by the Shor public
endpoint; the RSA-2048 wrapper uses this only for the factor-return success
part, while the terminal resource tuple is the GE19 RSA-2048 estimate with
explicit Shor retry accounting [Sho95, source.tex:1124-1148, 1132-1169,
1647-1663] [GE19, main.tex:70-79, 211-216, 888-889, 1785-1788]. -/
noncomputable def shorPublicEndpoint (input : InputClass) :
    ShorStyle.PublicEndpointWitness (toShorPublicInput input) retry
      (ShorStyle.PublicBaselineBounds.Envelope.toPublicBaselineBounds
        (ShorStyle.PublicBaselineBounds.Envelope.vbeModexpEnvelope modulusBits)
        retry) :=
  ShorStyle.PublicEndpointWitness.ofPublicInputAndPublicFailureBudgetAndCanonicalVBEEnvelope
    (toShorPublicInput input) failureBudget publicFailureBudget

/-- Public theorem-shape predicate for the RSA-2048 logical-resource estimate.
It is intentionally phrased with only the theorem-facing RSA-2048 input and the
final success-accounted resource fields.  Source-route certificates, selected
random bases, order-recovery certificates, retry certificates, and private
resource witnesses are not inputs to this predicate [Sho95, source.tex:1124-1148,
1647-1663] [GE19, main.tex:70-79, 211-216, 888-889, 1785-1788]. -/
def PublicTheoremShape (input : InputClass) : Prop :=
  ∃ d successNumerator successDenominator : ℕ,
    0 < successDenominator ∧
      (d = input.model.leftFactor ∨ d = input.model.rightFactor) ∧
      2 * successDenominator ≤ 3 * successNumerator ∧
      (failureBudget.failureDenominator - failureBudget.failureNumerator) *
          successDenominator ≤
        failureBudget.failureDenominator * successNumerator ∧
      2 ^ (modulusBits - 1) ≤ input.modulus ∧
      input.modulus < 2 ^ modulusBits ∧
      retry.runCount = 3 ∧
      finalSuccessAccountedEnvelope.fields.logicalQubits = 6190 ∧
      finalSuccessAccountedEnvelope.fields.toffoliGates =
        retry.runCount * 2700000000 ∧
      finalSuccessAccountedEnvelope.fields.circuitDepth =
        retry.runCount * 2140000000 ∧
      classicalArithmeticOps = 36906 ∧
      retry.readyForFinalStatement = true ∧
      finalSuccessAccountedEnvelope.readyForFinalStatement = true

/-- Final public endpoint wrapper for the RSA-2048 logical-resource estimate.
The proof obtains the factor-return success fields from the generic public Shor
endpoint and combines them with the GE19 one-run RSA-2048 resource tuple after
applying the public Shor retry selector for failure budget `1/3`. The only input
is the public RSA-2048 carrier; source pieces and private support witnesses are
constructed or selected internally by the supporting endpoints [Sho95,
source.tex:1124-1148, 1132-1169, 1647-1663] [GE19, main.tex:70-79, 211-216,
888-889, 1785-1788]. -/
theorem main (input : InputClass) :
    PublicTheoremShape input := by
  let endpoint := shorPublicEndpoint input
  refine ⟨endpoint.output, endpoint.successNumerator,
    endpoint.successDenominator, endpoint.successDenominator_pos,
    endpoint.output_mem_declared_factors, endpoint.success_atLeast_twoThirds,
    endpoint.success_atLeast_failureBudget, input.modulus_lower,
    input.modulus_upper, retry_runCount,
    finalSuccessAccountedEnvelope_logicalQubits,
    finalSuccessAccountedEnvelope_toffoliGates,
    finalSuccessAccountedEnvelope_circuitDepth,
    classicalArithmeticOps_eq, retry_ready,
    finalSuccessAccountedEnvelope_ready⟩

/-! ### RSA-2048 source-backed public endpoint -/

/-- Public RSA-2048 resource-estimate certificate. The correctness part is a
source-level factor-return certificate; the resource tuple is the pinned
source-backed logical estimate recorded in this namespace. The factor-return
route is the Shor order-finding reduction, while the numerical tuple is the GE19
RSA-2048 estimate [Sho95, source.tex:1124-1148] [GE19, main.tex:70-79,
211-216, 888-889, 1785-1788]. -/
private structure PublicSourceEstimateCertificate
    {N : ℕ} (model : ShorFactoring.SemiprimeFactorModel N) where
  /-- Factor-return certificate supplied to the public endpoint. -/
  factorReturn : ShorFactoring.ProbabilisticFactorReturnCertificate model

/-- Build the RSA-2048 terminal Shor-style success certificate from source
pieces. This is the terminal wrapper around the generic Shor constructor: the
random-base factor-yield route, order-recovery rational lower-bound fields,
repetition model, and retry-amplification certificate are assembled before the
RSA-2048 source-estimate endpoint consumes the success certificate [Sho95,
source.tex:1124-1148, source.tex:1132-1169, source.tex:1614-1663,
source.tex:1647-1663]. -/
private def retrySuccessCertificateOfSourcePieces
    (input : InputClass)
    {retry : RetryMultiplierSpec}
    {orderRecoverySuccessNumerator orderRecoverySuccessDenominator : ℕ}
    (good :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound
        input.model)
    (sample : ShorFactoring.RandomBaseUnitSample input.model)
    (order : ℕ)
    (route :
      ShorFactoring.HalfOrderGcdInput input.modulus sample.baseResidue order)
    (orderRecoverySource :
      ShorStyle.OrderRecoveryRationalFieldCertificate order
        orderRecoverySuccessNumerator orderRecoverySuccessDenominator)
    (repetition : RetryMultiplierSpec.RepetitionModel retry)
    (amplification : ShorStyle.RetryAmplificationCertificate retry) :
    ShorStyle.RetrySuccessCertificate input.model retry := by
  let factorYield :=
    ShorStyle.RandomBaseFactorYieldCertificate.ofPublicGoodEventRoute
      good sample order route
  exact ShorStyle.RetrySuccessCertificate.ofSourcePieces factorYield
    orderRecoverySource repetition amplification

/-- Public endpoint for the RSA-2048 logical-resource estimate. This proves the
stored source-backed tuple and the explicit classical arithmetic count attached
to the factor-return certificate. The quantum tuple remains a source-backed
estimate rather than an exact-resource theorem. The external correctness
certificate follows the Shor order-finding route [Sho95, source.tex:1124-1148,
1630-1663], while the resource tuple is GE19's source estimate [GE19,
main.tex:70-79, 211-216, 888-889, 1785-1788]. -/
private theorem main_sourceEstimate
    {N : ℕ} {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : PublicSourceEstimateCertificate model) :
    (cert.factorReturn.output.output = model.leftFactor ∨
        cert.factorReturn.output.output = model.rightFactor) ∧
      2 * cert.factorReturn.successDenominator ≤
        3 * cert.factorReturn.successNumerator ∧
      logicalResourceEstimate.logicalQubits = 6190 ∧
      logicalResourceEstimate.toffoliGates = 2700000000 ∧
      logicalResourceEstimate.circuitDepth = 2140000000 ∧
      classicalArithmeticOpsPerRun = 12302 ∧
      sourceEstimateEnvelope.fields = logicalResourceEstimate ∧
      sourceEstimateEnvelope.readyForFinalStatement = false :=
  ⟨cert.factorReturn.output_mem_declared_factors,
    cert.factorReturn.successAtLeastTwoThirds,
    logicalResourceEstimate_logicalQubits,
    logicalResourceEstimate_toffoliGates,
    logicalResourceEstimate_circuitDepth,
    classicalArithmeticOpsPerRun_eq,
    rfl,
    sourceEstimateEnvelope_not_ready⟩

/-- Source-route RSA-2048 endpoint.  This variant replaces the opaque
factor-return certificate with the Shor-style source-piece success certificate,
and keeps the fixed 2048-bit input window visible.  The numerical quantum tuple
remains the GE19 source estimate rather than a final exact-resource theorem
[Sho95, source.tex:1124-1148, source.tex:1132-1169, source.tex:1614-1663,
source.tex:1647-1663] [GE19, main.tex:70-79, 211-216, 888-889, 1785-1788]. -/
private theorem main_sourceEstimate_ofSourceRoute
    (input : InputClass)
    {retry : RetryMultiplierSpec}
    (success : ShorStyle.RetrySuccessCertificate input.model retry) :
    ((success.toProbabilisticFactorReturnCertificate).output.output =
          input.model.leftFactor ∨
        (success.toProbabilisticFactorReturnCertificate).output.output =
          input.model.rightFactor) ∧
      2 * (success.toProbabilisticFactorReturnCertificate).successDenominator ≤
        3 * (success.toProbabilisticFactorReturnCertificate).successNumerator ∧
      2 ^ (modulusBits - 1) ≤ input.modulus ∧
      input.modulus < 2 ^ modulusBits ∧
      logicalResourceEstimate.logicalQubits = 6190 ∧
      logicalResourceEstimate.toffoliGates = 2700000000 ∧
      logicalResourceEstimate.circuitDepth = 2140000000 ∧
      classicalArithmeticOpsPerRun = 12302 ∧
      sourceEstimateEnvelope.fields = logicalResourceEstimate ∧
      sourceEstimateEnvelope.readyForFinalStatement = false :=
  ⟨success.toProbabilisticFactorReturnCertificate.output_mem_declared_factors,
    success.toProbabilisticFactorReturnCertificate.successAtLeastTwoThirds,
    input.modulus_lower,
    input.modulus_upper,
    logicalResourceEstimate_logicalQubits,
    logicalResourceEstimate_toffoliGates,
    logicalResourceEstimate_circuitDepth,
    classicalArithmeticOpsPerRun_eq,
    rfl,
    sourceEstimateEnvelope_not_ready⟩

/-- Source-piece RSA-2048 endpoint. This variant exposes the source-route
construction of the Shor-style success certificate before projecting it through
`main_sourceEstimate_ofSourceRoute`. It still records the GE19 numerical tuple
as source-estimate-only, not as a final success-accounted resource theorem
[Sho95, source.tex:1124-1148, source.tex:1132-1169, source.tex:1614-1663,
source.tex:1647-1663] [GE19, main.tex:70-79, 211-216, 888-889,
1785-1788]. -/
private theorem main_sourceEstimate_ofSourcePieces
    (input : InputClass)
    {retry : RetryMultiplierSpec}
    {orderRecoverySuccessNumerator orderRecoverySuccessDenominator : ℕ}
    (good :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound
        input.model)
    (sample : ShorFactoring.RandomBaseUnitSample input.model)
    (order : ℕ)
    (route :
      ShorFactoring.HalfOrderGcdInput input.modulus sample.baseResidue order)
    (orderRecoverySource :
      ShorStyle.OrderRecoveryRationalFieldCertificate order
        orderRecoverySuccessNumerator orderRecoverySuccessDenominator)
    (repetition : RetryMultiplierSpec.RepetitionModel retry)
    (amplification : ShorStyle.RetryAmplificationCertificate retry) :
    let success :=
      retrySuccessCertificateOfSourcePieces input good sample order route
        orderRecoverySource repetition amplification
    ((success.toProbabilisticFactorReturnCertificate).output.output =
          input.model.leftFactor ∨
        (success.toProbabilisticFactorReturnCertificate).output.output =
          input.model.rightFactor) ∧
      2 * (success.toProbabilisticFactorReturnCertificate).successDenominator ≤
        3 * (success.toProbabilisticFactorReturnCertificate).successNumerator ∧
      2 ^ (modulusBits - 1) ≤ input.modulus ∧
      input.modulus < 2 ^ modulusBits ∧
      logicalResourceEstimate.logicalQubits = 6190 ∧
      logicalResourceEstimate.toffoliGates = 2700000000 ∧
      logicalResourceEstimate.circuitDepth = 2140000000 ∧
      classicalArithmeticOpsPerRun = 12302 ∧
      sourceEstimateEnvelope.fields = logicalResourceEstimate ∧
      sourceEstimateEnvelope.readyForFinalStatement = false := by
  simpa [retrySuccessCertificateOfSourcePieces] using
    main_sourceEstimate_ofSourceRoute input
      (retrySuccessCertificateOfSourcePieces input good sample order route
        orderRecoverySource repetition amplification)

/-- Final RSA-2048 logical-resource endpoint from source pieces. The theorem
uses Shor's factor-yield/order-recovery route and the selected RSA-2048 retry
arithmetic certificate, then exposes the success-accounted resource fields
proved by `finalSuccessAccountedFields` [Sho95, source.tex:1124-1148,
source.tex:1132-1169, source.tex:1614-1663, source.tex:1647-1663] [GE19,
main.tex:70-79, 211-216, 888-889, 1785-1788]. -/
private theorem main_finalResourceEstimate_ofSourcePieces
    (input : InputClass)
    {orderRecoverySuccessNumerator orderRecoverySuccessDenominator : ℕ}
    (good :
      ShorFactoring.SemiprimeFactorModel.RandomBaseGoodEventLowerBound
        input.model)
    (sample : ShorFactoring.RandomBaseUnitSample input.model)
    (order : ℕ)
    (route :
      ShorFactoring.HalfOrderGcdInput input.modulus sample.baseResidue order)
    (orderRecoverySource :
      ShorStyle.OrderRecoveryRationalFieldCertificate order
        orderRecoverySuccessNumerator orderRecoverySuccessDenominator) :
    let success :=
      retrySuccessCertificateOfSourcePieces input good sample order route
        orderRecoverySource retryRepetitionModel retryAmplificationCertificate
    ((success.toProbabilisticFactorReturnCertificate).output.output =
          input.model.leftFactor ∨
        (success.toProbabilisticFactorReturnCertificate).output.output =
          input.model.rightFactor) ∧
      2 * (success.toProbabilisticFactorReturnCertificate).successDenominator ≤
        3 * (success.toProbabilisticFactorReturnCertificate).successNumerator ∧
      2 ^ (modulusBits - 1) ≤ input.modulus ∧
      input.modulus < 2 ^ modulusBits ∧
      finalSuccessAccountedEnvelope.fields.logicalQubits = 6190 ∧
      finalSuccessAccountedEnvelope.fields.toffoliGates =
        retry.runCount * 2700000000 ∧
      finalSuccessAccountedEnvelope.fields.circuitDepth =
        retry.runCount * 2140000000 ∧
      classicalArithmeticOps =
        ShorStyle.ClassicalPostProcessingParameters.shorSuccessAccountedUpperBoundTotal
          retry modulusBits ∧
      retry.readyForFinalStatement = true ∧
      finalSuccessAccountedEnvelope.readyForFinalStatement = true := by
  let success :=
    retrySuccessCertificateOfSourcePieces input good sample order route
      orderRecoverySource retryRepetitionModel retryAmplificationCertificate
  rcases main_sourceEstimate_ofSourceRoute input success with
    ⟨hfactor, hprob, hlower, hupper, _hql, _htoffoli, _hdepth,
      _hclassical, _hfields, _hnotReady⟩
  rcases finalSuccessAccountedFields with
    ⟨hlogical, htoffoli, hdepth, hclassical, hretryReady, hfinalReady⟩
  exact ⟨hfactor, hprob, hlower, hupper, hlogical, htoffoli, hdepth,
    hclassical, hretryReady, hfinalReady⟩

end RSA2048

end FormulaEnvelope

end Factoring
end QuantumAlg
