/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.EllipticCurve.SuccessResources

/-!
# Public polynomial envelope for elliptic-curve scalar recovery

This module packages the bridge from private exact resource fields to the
coarse public polynomial ECC statement.  The public statement is intentionally
free of P-256 constants and signed-window coefficients: it asks only for
logical qubits bounded by a linear polynomial in the field bit size and
quantum/classical work bounded by explicit polynomial envelopes.  This matches
the Proos--Zalka source-level summary that elliptic-curve DLP uses `O(n)`
qubits and `O(n^3)` gates/time [PZ03, ecc.tex:331-338, 1463-1468], with
failure-budget retry support following Shor's repeated discrete-logarithm
sampling route [Sho95, source.tex:1924-1987].
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ECDLP

universe u v

namespace PublicPolynomial

open SuccessAccountedResources

variable {eta : Factoring.FailureBudget}

/-- A compact bivariate monomial envelope in the bit size and retry upper-bound
parameter.  The optional intercept keeps the interface stable for source
routes with additive constants while still exposing a coarse polynomial shape. -/
structure BivariatePolynomialEnvelope where
  /-- Degree of the bit-size variable in the envelope. -/
  bitSizeDegree : Nat
  /-- Degree of the retry upper-bound variable in the envelope. -/
  retryDegree : Nat
  /-- Natural coefficient multiplying the bivariate monomial. -/
  coefficient : Nat
  /-- Additive natural intercept included in the envelope. -/
  intercept : Nat
deriving DecidableEq

namespace BivariatePolynomialEnvelope

/-- Degree-shape predicate for a public polynomial envelope.  Coefficients stay
as explicit natural-number choices; the predicate fixes the variables and
degrees used by the public coarse statement. -/
def HasDegreeShape (envelope : BivariatePolynomialEnvelope)
    (bitSizeDegree retryDegree : Nat) : Prop :=
  envelope.bitSizeDegree = bitSizeDegree ∧
    envelope.retryDegree = retryDegree

/-- Evaluate a bivariate resource envelope at the chosen bit size and retry
upper-bound parameter. -/
def eval (envelope : BivariatePolynomialEnvelope)
    (bitSize retryUpperBound : Nat) : Nat :=
  envelope.coefficient * bitSize ^ envelope.bitSizeDegree *
      retryUpperBound ^ envelope.retryDegree +
    envelope.intercept

/-- Linear-in-bit-size envelope, independent of the retry parameter. -/
def linearBitSize (coefficient intercept : Nat) : BivariatePolynomialEnvelope where
  bitSizeDegree := 1
  retryDegree := 0
  coefficient := coefficient
  intercept := intercept

/-- Cubic-in-bit-size and linear-in-retry envelope for success-accounted
quantum work. -/
def cubicBitSizeLinearRetry
    (coefficient intercept : Nat) : BivariatePolynomialEnvelope where
  bitSizeDegree := 3
  retryDegree := 1
  coefficient := coefficient
  intercept := intercept

/-- Linear-in-retry envelope for classical post-processing after quantum
sampling. -/
def linearRetry (coefficient intercept : Nat) : BivariatePolynomialEnvelope where
  bitSizeDegree := 0
  retryDegree := 1
  coefficient := coefficient
  intercept := intercept

@[simp] theorem eval_linearBitSize
    (coefficient intercept bitSize retryUpperBound : Nat) :
    (linearBitSize coefficient intercept).eval bitSize retryUpperBound =
      coefficient * bitSize + intercept := by
  simp [linearBitSize, eval]

@[simp] theorem eval_cubicBitSizeLinearRetry
    (coefficient intercept bitSize retryUpperBound : Nat) :
    (cubicBitSizeLinearRetry coefficient intercept).eval bitSize retryUpperBound =
      coefficient * bitSize ^ 3 * retryUpperBound + intercept := by
  simp [cubicBitSizeLinearRetry, eval]

@[simp] theorem eval_linearRetry
    (coefficient intercept bitSize retryUpperBound : Nat) :
    (linearRetry coefficient intercept).eval bitSize retryUpperBound =
      coefficient * retryUpperBound + intercept := by
  simp [linearRetry, eval]

end BivariatePolynomialEnvelope

/-- Public-facing polynomial envelope fields for ECC scalar recovery.  Each field
is a natural-number polynomial envelope, evaluated at the source bit size and
the chosen retry upper-bound parameter. -/
structure Envelope where
  /-- Field or scalar bit size at which the envelope is evaluated. -/
  bitSize : Nat
  /-- Public retry upper-bound parameter used by success amplification. -/
  retryUpperBound : Nat
  /-- Polynomial envelope for logical qubits. -/
  logicalQubits : BivariatePolynomialEnvelope
  /-- Polynomial envelope for T-gate count. -/
  tGates : BivariatePolynomialEnvelope
  /-- Polynomial envelope for T-depth. -/
  tDepth : BivariatePolynomialEnvelope
  /-- Polynomial envelope for all-gate depth. -/
  allGateDepth : BivariatePolynomialEnvelope
  /-- Polynomial envelope for total gate count. -/
  totalGates : BivariatePolynomialEnvelope
  /-- Polynomial envelope for classical post-processing operations. -/
  classicalOps : BivariatePolynomialEnvelope
deriving DecidableEq

namespace Envelope

/-- The source bit size that this public envelope is evaluated at. -/
def bitSizeMatches
    (params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters)
    (envelope : Envelope) : Prop :=
  envelope.bitSize = params.bitSize

/-- Coarse polynomial shape used by the public ECC resource statement:
logical qubits are linear in the field bit size, quantum work is cubic in the
field bit size and linear in the retry upper-bound parameter, and classical
post-processing is linear in the retry upper-bound parameter. -/
def HasCoarsePolynomialShape (envelope : Envelope) : Prop :=
  envelope.logicalQubits.HasDegreeShape 1 0 ∧
    envelope.tGates.HasDegreeShape 3 1 ∧
    envelope.tDepth.HasDegreeShape 3 1 ∧
    envelope.allGateDepth.HasDegreeShape 3 1 ∧
    envelope.totalGates.HasDegreeShape 3 1 ∧
    envelope.classicalOps.HasDegreeShape 0 1

/-- Evaluated logical-qubit bound. -/
def logicalQubitBound (envelope : Envelope) : Nat :=
  envelope.logicalQubits.eval envelope.bitSize envelope.retryUpperBound

/-- Evaluated T-gate bound. -/
def tGateBound (envelope : Envelope) : Nat :=
  envelope.tGates.eval envelope.bitSize envelope.retryUpperBound

/-- Evaluated T-depth bound. -/
def tDepthBound (envelope : Envelope) : Nat :=
  envelope.tDepth.eval envelope.bitSize envelope.retryUpperBound

/-- Evaluated all-gate-depth bound. -/
def allGateDepthBound (envelope : Envelope) : Nat :=
  envelope.allGateDepth.eval envelope.bitSize envelope.retryUpperBound

/-- Evaluated total-gate bound. -/
def totalGateBound (envelope : Envelope) : Nat :=
  envelope.totalGates.eval envelope.bitSize envelope.retryUpperBound

/-- Evaluated classical post-processing bound. -/
def classicalOperationBound (envelope : Envelope) : Nat :=
  envelope.classicalOps.eval envelope.bitSize envelope.retryUpperBound

end Envelope

/-- The success-accounted exact fields are strong enough for the coarse public
polynomial ECC resource statement when every exact field is bounded by the
corresponding evaluated envelope and the retry/failure certificates are ready. -/
structure SupportsEnvelope
    (resources : SuccessAccountedResourceBounds) (envelope : Envelope) : Prop where
  retryRunCount_le : resources.retryRunCount <= envelope.retryUpperBound
  retryUpperBound_satisfied : resources.RetryUpperBoundSatisfied
  certifiedFailure_within_target : resources.CertifiedFailureWithinTarget
  ready : resources.readyForFinalStatement = true
  logicalQubits_le :
    resources.quantum.logicalQubits <= envelope.logicalQubitBound
  tGates_le : resources.quantum.tGates <= envelope.tGateBound
  tDepth_le : resources.quantum.tDepth <= envelope.tDepthBound
  allGateDepth_le :
    resources.quantum.allGateDepth <= envelope.allGateDepthBound
  totalGates_le : resources.quantum.totalGates <= envelope.totalGateBound
  classicalOps_le :
    resources.classicalOps <= envelope.classicalOperationBound

/-- Public-polynomial ECC support certificate.  This strengthens the raw
field-inequality support by tying the resource record to the requested failure
budget, evaluating the envelope at the source bit size, and requiring the
advertised coarse polynomial degree shape. -/
structure SupportsPublicPolynomial
    (eta : Factoring.FailureBudget)
    (params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters)
    (resources : SuccessAccountedResourceBounds) (envelope : Envelope) :
    Prop where
  targetFailureNumerator_eq :
    resources.targetFailureNumerator = eta.failureNumerator
  targetFailureDenominator_eq :
    resources.targetFailureDenominator = eta.failureDenominator
  targetFailure_wellFormed : eta.WellFormed
  bitSize_matches : envelope.bitSizeMatches params
  coarse_shape : envelope.HasCoarsePolynomialShape
  supports : SupportsEnvelope resources envelope

/-- A proof object packaging the private exact-resource support record and the
coarse public polynomial envelope it discharges. -/
structure StatementSupport (eta : Factoring.FailureBudget) where
  /-- Source bit-size and logarithmic parameters used by the private formula. -/
  params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters
  /-- Success-accounted private resource record being bounded. -/
  resources : SuccessAccountedResourceBounds
  /-- Coarse public polynomial envelope discharged by this support record. -/
  envelope : Envelope
  /-- Proof that the private resources satisfy the public polynomial statement. -/
  supports : SupportsPublicPolynomial eta params resources envelope

/-- Build the public polynomial-envelope certificate directly from
success-accounted resource fields and explicit field inequalities. -/
theorem supportsEnvelope_of_fieldBounds
    {resources : SuccessAccountedResourceBounds}
    {envelope : Envelope}
    (hretryEnvelope : resources.retryRunCount <= envelope.retryUpperBound)
    (hretryInternal : resources.RetryUpperBoundSatisfied)
    (hfailure : resources.CertifiedFailureWithinTarget)
    (hready : resources.readyForFinalStatement = true)
    (hlogical : resources.quantum.logicalQubits <= envelope.logicalQubitBound)
    (htGates : resources.quantum.tGates <= envelope.tGateBound)
    (htDepth : resources.quantum.tDepth <= envelope.tDepthBound)
    (hallDepth :
      resources.quantum.allGateDepth <= envelope.allGateDepthBound)
    (htotal : resources.quantum.totalGates <= envelope.totalGateBound)
    (hclassical : resources.classicalOps <= envelope.classicalOperationBound) :
    SupportsEnvelope resources envelope where
  retryRunCount_le := hretryEnvelope
  retryUpperBound_satisfied := hretryInternal
  certifiedFailure_within_target := hfailure
  ready := hready
  logicalQubits_le := hlogical
  tGates_le := htGates
  tDepth_le := htDepth
  allGateDepth_le := hallDepth
  totalGates_le := htotal
  classicalOps_le := hclassical

/-- Source-shaped implication theorem for the ECC public polynomial statement.
Given an HJN-backed per-run resource choice, an eta retry certificate, and
explicit polynomial envelope inequalities, the private success-accounted fields
support the public coarse polynomial resource claim. -/
theorem bounds_supportsEnvelope
    (target : QuantumAlg.EllipticCurve.Haner2020.OptimizationTarget)
    (params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters)
    (cert : SuccessAmplification.EtaCertificate eta)
    (envelope : Envelope)
    (hretry : cert.logInvEtaUpperBound <= envelope.retryUpperBound)
    (hlogical :
      (SuccessAccountedResources.bounds target params cert).quantum.logicalQubits <=
        envelope.logicalQubitBound)
    (htGates :
      (SuccessAccountedResources.bounds target params cert).quantum.tGates <=
        envelope.tGateBound)
    (htDepth :
      (SuccessAccountedResources.bounds target params cert).quantum.tDepth <=
        envelope.tDepthBound)
    (hallDepth :
      (SuccessAccountedResources.bounds target params cert).quantum.allGateDepth <=
        envelope.allGateDepthBound)
    (htotal :
      (SuccessAccountedResources.bounds target params cert).quantum.totalGates <=
        envelope.totalGateBound)
    (hclassical :
      (SuccessAccountedResources.bounds target params cert).classicalOps <=
        envelope.classicalOperationBound) :
    SupportsEnvelope (SuccessAccountedResources.bounds target params cert)
      envelope := by
  refine supportsEnvelope_of_fieldBounds ?_ ?_ ?_ ?_ hlogical htGates htDepth
    hallDepth htotal hclassical
  · exact le_trans cert.runCount_le_logInvEtaUpperBound hretry
  · simp [SuccessAccountedResources.bounds,
      SuccessAccountedResourceBounds.RetryUpperBoundSatisfied,
      cert.runCount_le_logInvEtaUpperBound]
  · simp [SuccessAccountedResources.bounds,
      SuccessAccountedResourceBounds.CertifiedFailureWithinTarget,
      SuccessAmplification.EtaCertificate.repeatedFailure_le_eta]
  · simp [SuccessAccountedResources.bounds,
      SuccessAmplification.EtaCertificate.retrySpec,
      SuccessAmplification.etaRetrySpec]

/-- Strong public-polynomial support theorem for ECC scalar recovery.  This is
the exported implication: the success-accounted private fields discharge a
source-bit-size public polynomial envelope whose degree shape is the coarse
`O(n)`/`O(n^3)` ECC statement. -/
theorem bounds_supportsPublicPolynomial
    (target : QuantumAlg.EllipticCurve.Haner2020.OptimizationTarget)
    (params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters)
    (cert : SuccessAmplification.EtaCertificate eta)
    (envelope : Envelope)
    (hbitSize : envelope.bitSizeMatches params)
    (hshape : envelope.HasCoarsePolynomialShape)
    (hretry : cert.logInvEtaUpperBound <= envelope.retryUpperBound)
    (hlogical :
      (SuccessAccountedResources.bounds target params cert).quantum.logicalQubits <=
        envelope.logicalQubitBound)
    (htGates :
      (SuccessAccountedResources.bounds target params cert).quantum.tGates <=
        envelope.tGateBound)
    (htDepth :
      (SuccessAccountedResources.bounds target params cert).quantum.tDepth <=
        envelope.tDepthBound)
    (hallDepth :
      (SuccessAccountedResources.bounds target params cert).quantum.allGateDepth <=
        envelope.allGateDepthBound)
    (htotal :
      (SuccessAccountedResources.bounds target params cert).quantum.totalGates <=
        envelope.totalGateBound)
    (hclassical :
      (SuccessAccountedResources.bounds target params cert).classicalOps <=
        envelope.classicalOperationBound) :
    SupportsPublicPolynomial eta params
      (SuccessAccountedResources.bounds target params cert) envelope where
  targetFailureNumerator_eq := rfl
  targetFailureDenominator_eq := rfl
  targetFailure_wellFormed := cert.eta_wellFormed
  bitSize_matches := hbitSize
  coarse_shape := hshape
  supports :=
    bounds_supportsEnvelope target params cert envelope hretry hlogical htGates
      htDepth hallDepth htotal hclassical

/-- Package the HJN-backed success-accounted resources together with the public
polynomial envelope they support. -/
def statementSupport
    (target : QuantumAlg.EllipticCurve.Haner2020.OptimizationTarget)
    (params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters)
    (cert : SuccessAmplification.EtaCertificate eta)
    (envelope : Envelope)
    (hbitSize : envelope.bitSizeMatches params)
    (hshape : envelope.HasCoarsePolynomialShape)
    (hretry : cert.logInvEtaUpperBound <= envelope.retryUpperBound)
    (hlogical :
      (SuccessAccountedResources.bounds target params cert).quantum.logicalQubits <=
        envelope.logicalQubitBound)
    (htGates :
      (SuccessAccountedResources.bounds target params cert).quantum.tGates <=
        envelope.tGateBound)
    (htDepth :
      (SuccessAccountedResources.bounds target params cert).quantum.tDepth <=
        envelope.tDepthBound)
    (hallDepth :
      (SuccessAccountedResources.bounds target params cert).quantum.allGateDepth <=
        envelope.allGateDepthBound)
    (htotal :
      (SuccessAccountedResources.bounds target params cert).quantum.totalGates <=
        envelope.totalGateBound)
    (hclassical :
      (SuccessAccountedResources.bounds target params cert).classicalOps <=
        envelope.classicalOperationBound) :
    StatementSupport eta where
  params := params
  resources := SuccessAccountedResources.bounds target params cert
  envelope := envelope
  supports :=
    bounds_supportsPublicPolynomial target params cert envelope hbitSize hshape
      hretry hlogical htGates htDepth hallDepth htotal hclassical

end PublicPolynomial

/-! ## Public theorem-shape wrapper -/

/-- Public theorem input for elliptic-curve scalar recovery.  The carrier keeps
the field characteristic, subgroup-primality, base point, target point, and
target-in-subgroup promise together through `ECDLPInstance`, while source-route
sampling and circuit certificates stay outside the public theorem boundary. -/
structure PublicInput {p : Nat} (E : PrimeFieldShortWeierstrass p) where
  /-- The elliptic-curve scalar-recovery instance. -/
  problem : ECDLPInstance E
  /-- The source route assumes prime fields with characteristic greater than
  three. -/
  characteristic_gt_three : 3 < p
  /-- The selected cyclic subgroup has prime order. -/
  subgroupOrder_prime : problem.subgroupOrder.Prime

/-- Public resource fields for the coarse polynomial ECC statement.  The
resource variables are public natural-number fields, bounded by an envelope
whose bit-size variable is tied to `ceil(log_2 p)`. Source-shaped formula
parameters and success-accounted support records are used only by private
constructors. -/
structure PublicResourceBounds
    (p : Nat) (eta : Factoring.FailureBudget)
    (envelope : PublicPolynomial.Envelope) where
  /-- Public bit-size variable used by the polynomial envelope. -/
  fieldBitSize : Nat
  /-- The public bit-size variable is `ceil(log_2 p)`. -/
  fieldBitSize_eq_clog : fieldBitSize = Nat.clog 2 p
  /-- The selected envelope is evaluated at the public field bit size. -/
  envelopeBitSize_eq : envelope.bitSize = fieldBitSize
  /-- The public failure budget is well formed. -/
  eta_wellFormed : eta.WellFormed
  /-- The envelope has the coarse polynomial shape in `log p` and the retry
  upper-bound parameter. -/
  coarse_shape : envelope.HasCoarsePolynomialShape
  /-- Logical qubits used by the public endpoint. -/
  logicalQubits : Nat
  /-- Elementary quantum gates used by the public endpoint. -/
  elementaryGates : Nat
  /-- Classical arithmetic operations used by the public endpoint. -/
  classicalOps : Nat
  /-- Logical qubits are bounded by the public envelope. -/
  logicalQubits_le : logicalQubits <= envelope.logicalQubitBound
  /-- Elementary quantum gates are bounded by the public total-gate envelope. -/
  elementaryGates_le : elementaryGates <= envelope.totalGateBound
  /-- Classical operations are bounded by the public classical envelope. -/
  classicalOps_le : classicalOps <= envelope.classicalOperationBound

namespace PublicResourceBounds

variable {p : Nat}
variable {eta : Factoring.FailureBudget}
variable {envelope : PublicPolynomial.Envelope}

/-- Public consequence of a resource-bound record: the resource variables use
`ceil(log_2 p)` as the bit-size parameter, the failure budget is valid, and the
qubit/gate/classical counts are bounded by a coarse polynomial envelope. -/
def Statement (resources : PublicResourceBounds p eta envelope) : Prop :=
  resources.fieldBitSize = Nat.clog 2 p ∧
    envelope.bitSize = resources.fieldBitSize ∧
    eta.WellFormed ∧
    envelope.HasCoarsePolynomialShape ∧
    resources.logicalQubits <= envelope.logicalQubitBound ∧
    resources.elementaryGates <= envelope.totalGateBound ∧
    resources.classicalOps <= envelope.classicalOperationBound

/-- A public resource-bound record exposes the public resource consequence. -/
theorem statement (resources : PublicResourceBounds p eta envelope) :
    resources.Statement :=
  ⟨resources.fieldBitSize_eq_clog, resources.envelopeBitSize_eq,
    resources.eta_wellFormed, resources.coarse_shape,
    resources.logicalQubits_le, resources.elementaryGates_le,
    resources.classicalOps_le⟩

end PublicResourceBounds

/-- Private constructor from source-backed success-accounted support to the
public resource-bound carrier used by the theorem-node endpoint. -/
private def publicResourceBoundsOfStatementSupport
    {p : Nat} {eta : Factoring.FailureBudget}
    (support : PublicPolynomial.StatementSupport eta)
    (hfieldBitSize : support.params.bitSize = Nat.clog 2 p) :
    PublicResourceBounds p eta support.envelope where
  fieldBitSize := support.params.bitSize
  fieldBitSize_eq_clog := hfieldBitSize
  envelopeBitSize_eq := by
    exact support.supports.bitSize_matches
  eta_wellFormed := support.supports.targetFailure_wellFormed
  coarse_shape := support.supports.coarse_shape
  logicalQubits := support.resources.quantum.logicalQubits
  elementaryGates := support.resources.quantum.totalGates
  classicalOps := support.resources.classicalOps
  logicalQubits_le := support.supports.supports.logicalQubits_le
  elementaryGates_le := support.supports.supports.totalGates_le
  classicalOps_le := support.supports.supports.classicalOps_le

/-- Public endpoint witness for the elliptic-curve scalar-recovery theorem.
It records theorem-facing data only: an output scalar, the certified failure
bound for the target `eta`, and a coarse polynomial resource envelope. -/
structure PublicEndpointWitness {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (input : PublicInput E)
    (eta : Factoring.FailureBudget)
    (envelope : PublicPolynomial.Envelope) where
  /-- Coarse public resource envelope witness. -/
  resources : PublicResourceBounds p eta envelope
  /-- Recovered scalar as a natural-number representative. -/
  output : Nat
  /-- The recovered scalar lies in the public subgroup-order range. -/
  output_lt_order : output < input.problem.subgroupOrder
  /-- The recovered scalar solves the public ECDLP instance after reduction
  modulo the subgroup order. -/
  output_candidate :
    input.problem.CandidateScalar
      (output : ZMod input.problem.subgroupOrder)
  /-- Numerator of the certified repeated-run failure probability. -/
  failureNumerator : Nat
  /-- Denominator of the certified repeated-run failure probability. -/
  failureDenominator : Nat
  /-- The certified failure denominator is positive. -/
  failureDenominator_pos : 0 < failureDenominator
  /-- The certified repeated-run failure probability is at most `eta`. -/
  certifiedFailureWithinTarget :
    failureNumerator * eta.failureDenominator <=
      eta.failureNumerator * failureDenominator

namespace PublicEndpointWitness

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
variable {input : PublicInput E}
variable {eta : Factoring.FailureBudget}
variable {envelope : PublicPolynomial.Envelope}

/-- Public consequence predicate for an ECC scalar-recovery endpoint witness. -/
def Statement (witness : PublicEndpointWitness input eta envelope) : Prop :=
  (3 < p) ∧
    input.problem.subgroupOrder.Prime ∧
    witness.output < input.problem.subgroupOrder ∧
    input.problem.CandidateScalar
      (witness.output : ZMod input.problem.subgroupOrder) ∧
    eta.WellFormed ∧
    0 < witness.failureDenominator ∧
    witness.failureNumerator * eta.failureDenominator <=
      eta.failureNumerator * witness.failureDenominator ∧
    envelope.HasCoarsePolynomialShape ∧
    witness.resources.Statement

/-- Any public endpoint witness exposes the public theorem-shape consequence. -/
theorem statement (witness : PublicEndpointWitness input eta envelope) :
    witness.Statement := by
  refine
    ⟨input.characteristic_gt_three, input.subgroupOrder_prime,
      witness.output_lt_order, witness.output_candidate, ?_,
      witness.failureDenominator_pos, witness.certifiedFailureWithinTarget,
      ?_, ?_⟩
  · exact witness.resources.statement.2.2.1
  · exact witness.resources.statement.2.2.2.1
  · exact witness.resources.statement

end PublicEndpointWitness

/-- Public theorem shape for polynomial-time elliptic-curve scalar recovery:
there is an endpoint witness returning a scalar that solves the ECDLP instance,
with certified failure at most `eta` and resources bounded by a coarse
polynomial envelope. -/
def PublicTheoremShape {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (input : PublicInput E)
    (eta : Factoring.FailureBudget)
    (envelope : PublicPolynomial.Envelope) : Prop :=
  ∃ witness : PublicEndpointWitness input eta envelope, witness.Statement

namespace PublicTheoremShape

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Final public theorem wrapper for elliptic-curve scalar recovery.  The
boundary contains only public curve/subgroup input, public failure-budget data,
an output scalar satisfying the ECDLP equation, certified repeated-run failure
data, and a public coarse polynomial resource envelope.  Fourier-sampling
support, finite-cyclic bridge data, and reversible scalar-multiplication
circuit support are internalized by source-route bridge theorems rather than
appearing as inputs to this public endpoint. -/
theorem main
    (input : PublicInput E)
    (eta : Factoring.FailureBudget)
    (envelope : PublicPolynomial.Envelope)
    (resources : PublicResourceBounds p eta envelope)
    (output : Nat)
    (houtput_lt_order : output < input.problem.subgroupOrder)
    (houtput :
      input.problem.CandidateScalar
        (output : ZMod input.problem.subgroupOrder))
    (failureNumerator failureDenominator : Nat)
    (hfailureDenominator : 0 < failureDenominator)
    (hfailure :
      failureNumerator * eta.failureDenominator <=
        eta.failureNumerator * failureDenominator) :
    PublicTheoremShape input eta envelope := by
  refine ⟨?_, ?_⟩
  · exact
      { resources := resources
        output := output
        output_lt_order := houtput_lt_order
        output_candidate := houtput
        failureNumerator := failureNumerator
        failureDenominator := failureDenominator
        failureDenominator_pos := hfailureDenominator
        certifiedFailureWithinTarget := hfailure }
  · exact PublicEndpointWitness.statement _

end PublicTheoremShape

/-- Internal source-route bridge from finite-cyclic Fourier sampling and the
reversible elliptic-curve scalar-oracle resource boundary into the public
polynomial theorem shape. -/
private theorem publicTheoremShape_of_fourierSamplingSupport
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    {G : Type u} [Group G]
    {P : QuantumAlg.FiniteCyclicDLP.KnownOrderProblem G} {Ω : Type v}
    (input : PublicInput E)
    (support : QuantumAlg.FiniteCyclicDLP.FourierSamplingSupport P Ω)
    (bridge : FiniteCyclicBridge input.problem P support.secret)
    (scalarOracle : ScalarOracleResourceCertificate E)
    (params : QuantumAlg.FiniteCyclicDLP.ResourceParameters)
    (bounds : QuantumAlg.FiniteCyclicDLP.PublicBaselineBounds.FormulaParameters)
    (eta : Factoring.FailureBudget)
    (amplification : SuccessAmplification.EtaCertificate eta)
    (resourceSupport : PublicPolynomial.StatementSupport eta)
    (hfieldBitSize : resourceSupport.params.bitSize = Nat.clog 2 p)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    PublicTheoremShape input eta resourceSupport.envelope := by
  rcases
    main_with_eta_amplification_of_fourier_sampling_support
      support bridge scalarOracle params bounds eta amplification horderBits
      hgroup horacleDepth hfourierDepth hclassical with
    ⟨_, _, _, _, _, _, _, hfailure, _, _, _, _, _, _⟩
  let output := bridge.toECDLPScalar support.secret
  haveI : NeZero input.problem.subgroupOrder :=
    ⟨Nat.ne_of_gt input.problem.subgroupOrder_pos⟩
  have houtput_mod : input.problem.CandidateScalar output := by
    simpa [output, FiniteCyclicBridge.toECDLPScalar] using
      bridge.secret_candidate
  have houtput :
      input.problem.CandidateScalar
        (output.val : ZMod input.problem.subgroupOrder) := by
    have hval :
        ((output.val : Nat) : ZMod input.problem.subgroupOrder) =
          output := by
      exact ZMod.natCast_zmod_val output
    simpa [hval] using houtput_mod
  let resources :=
    publicResourceBoundsOfStatementSupport resourceSupport hfieldBitSize
  exact
    PublicTheoremShape.main input eta resourceSupport.envelope resources
      output.val (ZMod.val_lt output) houtput
      amplification.repetitionModel.failureNumerator
      amplification.repetitionModel.failureDenominator
      amplification.repetitionModel.failureDenominator_pos hfailure

end ECDLP
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg
