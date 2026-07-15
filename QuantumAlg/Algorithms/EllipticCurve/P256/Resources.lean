/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
public import QuantumAlg.Algorithms.Factoring.Common

/-!
# P-256 logical-resource baseline

This module packages the Roetteler--Naehrig--Svore--Lauter P-256 baseline row
as Lean-facing resource fields.  The quantum tuple is the source table route:
`2330` logical qubits, `1.26 * 10^11` Toffoli gates, and `1.16 * 10^11`
maximal Toffoli-gate depth [RNSL17, ECDLP.tex:170,712-738].  The success
accounting layer keeps the finite-cyclic DLP classical taxonomy explicit.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve

namespace P256LogicalResources

universe u v

/-- P-256 logical-resource row plus structured classical post-processing. -/
structure BaselineProfile where
  /-- Logical qubits in the RNSL 2017 P-256 baseline row. -/
  logicalQubits : Nat
  /-- Toffoli gates in the RNSL 2017 P-256 baseline row. -/
  toffoliGates : Nat
  /-- Maximal Toffoli-gate depth in the RNSL 2017 P-256 baseline row. -/
  maximalToffoliDepth : Nat
  /-- Structured classical post-processing count from the finite-cyclic DLP
  recovery taxonomy. -/
  classicalPostProcessing : ClassicalArithmeticProfile
deriving DecidableEq

namespace BaselineProfile

/-- Scalar classical operation count obtained from the structured taxonomy. -/
def classicalOps (profile : BaselineProfile) : Nat :=
  profile.classicalPostProcessing.total

/-- Apply a sequential retry/run multiplier.  Logical qubits are live footprint
and are therefore not multiplied; gate, depth, and classical work are. -/
def successAccounted (profile : BaselineProfile) (runCount : Nat) :
    BaselineProfile where
  logicalQubits := profile.logicalQubits
  toffoliGates := runCount * profile.toffoliGates
  maximalToffoliDepth := runCount * profile.maximalToffoliDepth
  classicalPostProcessing :=
    ClassicalArithmeticProfile.scale runCount profile.classicalPostProcessing

@[simp] theorem successAccounted_logicalQubits
    (profile : BaselineProfile) (runCount : Nat) :
    (profile.successAccounted runCount).logicalQubits = profile.logicalQubits :=
  rfl

@[simp] theorem successAccounted_toffoliGates
    (profile : BaselineProfile) (runCount : Nat) :
    (profile.successAccounted runCount).toffoliGates =
      runCount * profile.toffoliGates :=
  rfl

@[simp] theorem successAccounted_maximalToffoliDepth
    (profile : BaselineProfile) (runCount : Nat) :
    (profile.successAccounted runCount).maximalToffoliDepth =
      runCount * profile.maximalToffoliDepth :=
  rfl

@[simp] theorem successAccounted_classicalOps
    (profile : BaselineProfile) (runCount : Nat) :
    (profile.successAccounted runCount).classicalOps =
      runCount * profile.classicalOps := by
  simp [classicalOps, successAccounted, ClassicalArithmeticProfile.total_scale]

end BaselineProfile

/-- Failure budget corresponding to a success probability of at least `2/3`. -/
def successFailureBudget : Factoring.FailureBudget where
  failureNumerator := 1
  failureDenominator := 3

/-- The `2/3` success failure budget is well formed. -/
theorem successFailureBudget_wellFormed :
    successFailureBudget.WellFormed := by
  exact ⟨by decide, by decide⟩

/-- One-run exact success multiplier for an endpoint that already carries a
`>= 2/3` success certificate. -/
def successMultiplierSpec : Factoring.RetryMultiplierSpec :=
  Factoring.RetryMultiplierSpec.exactCount successFailureBudget 1

@[simp] theorem successMultiplierSpec_runCount :
    successMultiplierSpec.runCount = 1 :=
  rfl

@[simp] theorem successMultiplierSpec_ready :
    successMultiplierSpec.readyForFinalStatement = true :=
  rfl

/-- RNSL 2017 P-256 baseline tuple plus the direct finite-cyclic DLP recovery
classical upper-bound profile. -/
def baseline : BaselineProfile where
  logicalQubits := 2330
  toffoliGates := 126000000000
  maximalToffoliDepth := 116000000000
  classicalPostProcessing :=
    QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBound.toProfile

/-- Baseline row after applying the exact one-run success multiplier. -/
def successAccountedBaseline : BaselineProfile :=
  baseline.successAccounted successMultiplierSpec.runCount

/-- Shared direct-recovery classical upper bound reused by the P-256 baseline. -/
def finiteCyclicDirectRecoveryUpperBoundTotal : Nat :=
  FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal

/-- The baseline classical operation count is the finite-cyclic DLP direct
recovery count from the shared classical taxonomy. -/
theorem baseline_classicalOps :
    baseline.classicalOps = finiteCyclicDirectRecoveryUpperBoundTotal := by
  simpa [baseline, BaselineProfile.classicalOps,
    finiteCyclicDirectRecoveryUpperBoundTotal] using
    QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBound_total

/-- The selected direct finite-cyclic recovery profile has seven scalar
classical arithmetic operations. -/
theorem baseline_classicalOps_eq_seven : baseline.classicalOps = 7 := by
  rw [baseline_classicalOps]
  rfl

/-- Source-backed P-256 baseline tuple and classical post-processing count. -/
theorem baseline_tuple :
    baseline.logicalQubits = 2330 ∧
      baseline.toffoliGates = 126000000000 ∧
      baseline.maximalToffoliDepth = 116000000000 ∧
      baseline.classicalOps = 7 := by
  exact ⟨rfl, rfl, rfl, baseline_classicalOps_eq_seven⟩

/-- Source-bound one-run tuple for the `>= 2/3` success route: the success
multiplier is `1`, the RNSL baseline tuple is unchanged, and the classical
post-processing count is `7`. -/
theorem successAccounted_tuple :
    successMultiplierSpec.runCount = 1 ∧
      successMultiplierSpec.readyForFinalStatement = true ∧
      successAccountedBaseline.logicalQubits = 2330 ∧
      successAccountedBaseline.toffoliGates = 126000000000 ∧
      successAccountedBaseline.maximalToffoliDepth = 116000000000 ∧
      successAccountedBaseline.classicalOps = 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rw [successAccountedBaseline, BaselineProfile.successAccounted_classicalOps]
    simpa using baseline_classicalOps_eq_seven

/-- Explicit replacement fields for the public P-256 resource statement.  The
record consumes the named RNSL baseline tuple, the one-run success multiplier,
and the shared finite-cyclic DLP classical post-processing count. -/
structure PublicStatementResources where
  /-- Live logical-qubit footprint. -/
  logicalQubits : Nat
  /-- Success-accounted Toffoli-gate count. -/
  toffoliGates : Nat
  /-- Success-accounted maximal Toffoli-gate depth. -/
  maximalToffoliDepth : Nat
  /-- Classical arithmetic operations in the shared taxonomy. -/
  classicalOps : Nat
  /-- Toffoli-gate run multiplier used to replace the public placeholder. -/
  toffoliRunMultiplier : Nat
  /-- Toffoli-depth run multiplier used to replace the public placeholder. -/
  depthRunMultiplier : Nat
  /-- Whether the retry/success-accounting data is ready for a final statement. -/
  readyForFinalStatement : Bool
deriving DecidableEq

/-- The concrete P-256 resource fields after replacing all resource
placeholders in the RNSL baseline route. -/
def publicStatementResources : PublicStatementResources where
  logicalQubits := successAccountedBaseline.logicalQubits
  toffoliGates := successAccountedBaseline.toffoliGates
  maximalToffoliDepth := successAccountedBaseline.maximalToffoliDepth
  classicalOps := successAccountedBaseline.classicalOps
  toffoliRunMultiplier := successMultiplierSpec.runCount
  depthRunMultiplier := successMultiplierSpec.runCount
  readyForFinalStatement := successMultiplierSpec.readyForFinalStatement

/-- The public P-256 resource fields are concrete and contain no asymptotic or
placeholder resource quantities. -/
theorem publicStatementResources_tuple :
    publicStatementResources.logicalQubits = 2330 ∧
      publicStatementResources.toffoliGates = 126000000000 ∧
      publicStatementResources.maximalToffoliDepth = 116000000000 ∧
      publicStatementResources.classicalOps = 7 ∧
      publicStatementResources.toffoliRunMultiplier = 1 ∧
      publicStatementResources.depthRunMultiplier = 1 ∧
      publicStatementResources.readyForFinalStatement = true := by
  rcases successAccounted_tuple with
    ⟨hrun, hready, hlogical, htoffoli, hdepth, hclassical⟩
  exact ⟨hlogical, htoffoli, hdepth, hclassical, hrun, hrun, hready⟩

/-- Support object connecting a P-256 scalar-recovery instance to the explicit
resource replacements.  It keeps the scalar-candidate and scalar-range facts
separate from the source-bound resource tuple. -/
structure PublicStatementSupport
    (I : P256DomainParameters.ScalarRecoveryInterface) where
  /-- Explicit P-256 resource replacements. -/
  resources : PublicStatementResources
  /-- The range-certified private scalar is a candidate scalar for `Q = [m]P`. -/
  candidateScalar :
    I.toECDLPInstance.CandidateScalar I.privateScalar.toZMod
  /-- The natural-number scalar representative lies below the subgroup order. -/
  scalar_lt_order :
    I.privateScalar.value < P256DomainParameters.subgroupOrder
  /-- Fieldwise resource equalities for the explicit public statement. -/
  resources_tuple :
    resources.logicalQubits = 2330 ∧
      resources.toffoliGates = 126000000000 ∧
      resources.maximalToffoliDepth = 116000000000 ∧
      resources.classicalOps = 7 ∧
      resources.toffoliRunMultiplier = 1 ∧
      resources.depthRunMultiplier = 1 ∧
      resources.readyForFinalStatement = true

/-- Build the P-256 public-statement support record from a scalar-recovery
interface and the exact resource fields supplied by the support layer. -/
def statementSupport (I : P256DomainParameters.ScalarRecoveryInterface) :
    PublicStatementSupport I where
  resources := publicStatementResources
  candidateScalar := I.privateScalar_candidate
  scalar_lt_order := I.privateScalar_lt_order
  resources_tuple := publicStatementResources_tuple

namespace SameCircuitScalarRecovery

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP

variable (I : P256DomainParameters.ScalarRecoveryInterface)
variable [Fact P256DomainParameters.primeModulus.Prime]
variable {G : Type u} [Group G]
variable (P : QuantumAlg.FiniteCyclicDLP.KnownOrderProblem G)
variable (Ω : Type v)
variable (support : QuantumAlg.FiniteCyclicDLP.FourierSamplingSupport P Ω)

/-- Same-Circuit P-256 scalar-recovery witness.  The finite-cyclic sampling
support supplies the `>= 2/3` success certificate; the bridge identifies the
recovered finite-cyclic scalar with the stored P-256 private scalar; and the
resource equalities connect the public P-256 tuple to the same folded scalar
oracle circuit used for encoded-basis correctness. -/
structure Witness where
  /-- Finite-cyclic-to-ECDLP bridge for the P-256 scalar-recovery instance. -/
  bridge : FiniteCyclicBridge I.toECDLPInstance P support.secret
  /-- Decomposed same-Circuit scalar-oracle certificate for the P-256 curve. -/
  scalarOracle :
    SameCircuitScalarOracleCertificate
      (P256DomainParameters.curve I.curveCert)
  /-- Finite-cyclic DLP resource parameters consumed by the terminal route. -/
  params : QuantumAlg.FiniteCyclicDLP.ResourceParameters
  /-- Public finite-cyclic DLP formula bounds consumed by the terminal route. -/
  bounds : QuantumAlg.FiniteCyclicDLP.PublicBaselineBounds.FormulaParameters
  /-- The finite-cyclic group register is exactly the scalar-oracle live
  footprint in the same-Circuit route. -/
  groupRegisterQubits_eq :
    params.groupRegisterQubits = scalarOracle.profile.logicalQubits
  /-- The finite-cyclic oracle depth is exactly the scalar-oracle circuit depth
  projected from the same-Circuit route. -/
  oracleDepth_eq :
    params.oracleDepth = scalarOracle.profile.circuitDepth
  /-- Order-register bound for the finite-cyclic public baseline. -/
  orderRegisterQubits_le :
    params.orderRegisterQubits <= bounds.orderBitUpperBound
  /-- Group-register bound for the finite-cyclic public baseline. -/
  groupRegisterQubits_le :
    params.groupRegisterQubits <= bounds.groupRegisterQubitBound
  /-- Oracle-depth bound for the finite-cyclic public baseline. -/
  oracleDepth_le : params.oracleDepth <= bounds.oracleDepthBound
  /-- Fourier-layer depth bound for the finite-cyclic public baseline. -/
  fourierLayerDepth_le :
    params.fourierLayerDepth <= bounds.fourierLayerDepthBound
  /-- Classical post-processing bound for the finite-cyclic public baseline. -/
  classicalOps_le :
    params.classicalPostProcessing.total <= bounds.classicalOperationBound
  /-- Concrete public P-256 resource fields. -/
  resources : PublicStatementResources
  /-- The concrete public resource tuple remains the accepted P-256 row after
  success accounting. -/
  resources_public_tuple :
    resources.logicalQubits = 2330 ∧
      resources.toffoliGates = 126000000000 ∧
      resources.maximalToffoliDepth = 116000000000 ∧
      resources.classicalOps = 7 ∧
      resources.toffoliRunMultiplier = 1 ∧
      resources.depthRunMultiplier = 1 ∧
      resources.readyForFinalStatement = true
  /-- The public resource tuple is tied to the same finite-cyclic/ECC route:
  logical qubits and classical operations come from the exact finite-cyclic
  profile, while Toffoli count and Toffoli depth are projected from the same
  scalar-oracle circuit profile. -/
  resources_from_sameCircuit_profile :
    resources.logicalQubits =
      2 * params.orderRegisterQubits + scalarOracle.profile.logicalQubits ∧
      resources.toffoliGates = scalarOracle.resourceFields.toffoliGates ∧
      resources.maximalToffoliDepth = scalarOracle.resourceFields.toffoliDepth ∧
      resources.classicalOps = params.classicalPostProcessing.total
  /-- The finite-cyclic hidden scalar transported through the bridge is the
  stored P-256 private scalar. -/
  secret_eq_privateScalar :
    bridge.toECDLPScalar support.secret = I.privateScalar.toZMod
  /-- Every certified finite-cyclic good output transported through the bridge
  is the stored P-256 private scalar. -/
  goodOutput_eq_privateScalar :
    let sampling :
      QuantumAlg.FiniteCyclicDLP.SamplingCertificate P Ω :=
      support.toSamplingCertificate
    ∀ outcome (hgood : outcome ∈ sampling.goodEvents),
      bridge.toECDLPScalar ((sampling.recovery outcome hgood).output) =
        I.privateScalar.toZMod

end SameCircuitScalarRecovery

/-- Same-Circuit P-256 scalar-recovery witness exposed at the P-256 resource
namespace. -/
abbrev SameCircuitScalarRecoveryWitness
    (I : P256DomainParameters.ScalarRecoveryInterface)
    [Fact P256DomainParameters.primeModulus.Prime]
    {G : Type u} [Group G]
    (P : QuantumAlg.FiniteCyclicDLP.KnownOrderProblem G)
    (Ω : Type v)
    (support : QuantumAlg.FiniteCyclicDLP.FourierSamplingSupport P Ω) :=
  SameCircuitScalarRecovery.Witness I P Ω support

namespace SameCircuitScalarRecoveryWitness

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP

variable {I : P256DomainParameters.ScalarRecoveryInterface}
variable [Fact P256DomainParameters.primeModulus.Prime]
variable {G : Type u} [Group G]
variable {P : QuantumAlg.FiniteCyclicDLP.KnownOrderProblem G}
variable {Ω : Type v}
variable {support : QuantumAlg.FiniteCyclicDLP.FourierSamplingSupport P Ω}

/-- Natural-number output of the P-256 scalar-recovery route.  The witness
argument is kept so callers can use dot notation; the scalar is fixed by the
interface. -/
@[nolint unusedArguments]
def output (_w : SameCircuitScalarRecoveryWitness I P Ω support) : Nat :=
  I.privateScalar.value

@[simp] theorem output_eq_privateScalar
    (w : SameCircuitScalarRecoveryWitness I P Ω support) :
    w.output = I.privateScalar.value :=
  rfl

/-- The returned scalar representative lies in the P-256 subgroup range. -/
theorem output_lt_order
    (w : SameCircuitScalarRecoveryWitness I P Ω support) :
    w.output < P256DomainParameters.subgroupOrder :=
  I.privateScalar_lt_order

/-- The returned natural-number representative is a valid ECDLP candidate
scalar for the P-256 instance. -/
theorem output_candidate
    (w : SameCircuitScalarRecoveryWitness I P Ω support) :
    I.toECDLPInstance.CandidateScalar
      (w.output : ZMod I.toECDLPInstance.subgroupOrder) := by
  change I.toECDLPInstance.CandidateScalar I.privateScalar.toZMod
  exact I.privateScalar_candidate

/-- Finite-cyclic good outputs transported through the ECDLP bridge recover the
stored P-256 private scalar. -/
theorem good_output_eq_privateScalar
    (w : SameCircuitScalarRecoveryWitness I P Ω support) :
    let sampling :
      QuantumAlg.FiniteCyclicDLP.SamplingCertificate P Ω :=
      support.toSamplingCertificate
    ∀ outcome (hgood : outcome ∈ sampling.goodEvents),
      w.bridge.toECDLPScalar ((sampling.recovery outcome hgood).output) =
        I.privateScalar.toZMod :=
  w.goodOutput_eq_privateScalar

/-- Exact same-Circuit finite-cyclic/ECDLP evidence consumed by the P-256
terminal witness. -/
def SameCircuitEvidence
    (w : SameCircuitScalarRecoveryWitness I P Ω support) : Prop :=
  let sampling :
    QuantumAlg.FiniteCyclicDLP.SamplingCertificate P Ω :=
    support.toSamplingCertificate
  (∀ outcome (hgood : outcome ∈ sampling.goodEvents),
    I.toECDLPInstance.CandidateScalar
      (w.bridge.toECDLPScalar ((sampling.recovery outcome hgood).output))) ∧
    sampling.SuccessAtLeastTwoThirds ∧
    (2 : ℝ) / 3 ≤ sampling.goodMass ∧
    (sampling.successNumerator : ℝ) /
        (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
    0 ≤ sampling.goodMass ∧
    sampling.goodMass ≤ 1 ∧
    QuantumAlg.FiniteCyclicDLP.ExactResourceProfile.HasExactCounts
      w.params.toExactResourceProfile
      1
      (2 * w.params.orderRegisterQubits +
        w.scalarOracle.profile.logicalQubits)
      (2 * w.params.orderRegisterQubits)
      (w.params.orderRegisterQubits *
        (w.params.orderRegisterQubits - 1))
      (2 * (w.params.orderRegisterQubits / 2))
      (w.scalarOracle.profile.circuitDepth + w.params.fourierLayerDepth)
      w.params.classicalPostProcessing.total ∧
    QuantumAlg.FiniteCyclicDLP.SupportsPublicBaseline
      w.params.toExactResourceProfile w.bounds.toPublicBaselineBounds ∧
    w.scalarOracle.resourceCorrectWitness.circuit =
      w.scalarOracle.circuit ∧
    w.scalarOracle.circuit.history.IsBaseGateStructured ∧
    SameCircuitResourceFields.ExactForProfile
      w.scalarOracle.resourceFields w.scalarOracle.profile ∧
    w.scalarOracle.circuit.resources =
      w.scalarOracle.profile.toResourceProfile ∧
    w.scalarOracle.circuit.depth = w.scalarOracle.profile.circuitDepth ∧
    w.scalarOracle.circuit.queryDepth =
      w.scalarOracle.profile.oracleQueries ∧
    ScalarMultiplication.CertifiedEndpoint.ResourceParameters.SupportsPublicBaseline
      w.scalarOracle.schedule w.scalarOracle.profile
      w.scalarOracle.bounds ∧
    ModularArithmeticResourceProfile.SupportsUpperBound
      w.scalarOracle.profile w.scalarOracle.boundProfile

/-- The P-256 witness satisfies the generic same-Circuit scalar-recovery
endpoint. -/
theorem sameCircuitEvidence
    (w : SameCircuitScalarRecoveryWitness I P Ω support) :
    SameCircuitEvidence w := by
  simpa [SameCircuitEvidence] using
    (main_sameCircuit_exactResource_of_fourier_sampling_support
      support w.bridge w.scalarOracle w.params w.bounds
      w.groupRegisterQubits_eq w.oracleDepth_eq
      w.orderRegisterQubits_le w.groupRegisterQubits_le
      w.oracleDepth_le w.fourierLayerDepth_le w.classicalOps_le)

/-- Good-output equality packaged as a proposition for the terminal statement. -/
def GoodOutputEqPrivateScalar
    (w : SameCircuitScalarRecoveryWitness I P Ω support) : Prop :=
  let sampling :
    QuantumAlg.FiniteCyclicDLP.SamplingCertificate P Ω :=
    support.toSamplingCertificate
  ∀ outcome (hgood : outcome ∈ sampling.goodEvents),
    w.bridge.toECDLPScalar ((sampling.recovery outcome hgood).output) =
      I.privateScalar.toZMod

/-- Terminal P-256 same-Circuit scalar-recovery statement: the route returns
the stored private scalar with a `>= 2/3` success certificate, and its public
resource tuple is tied to the same scalar-oracle circuit profile that supplies
correctness. -/
def Statement
    (I : P256DomainParameters.ScalarRecoveryInterface)
    {G : Type u} [Group G]
    (P : QuantumAlg.FiniteCyclicDLP.KnownOrderProblem G)
    (Ω : Type v)
    (support : QuantumAlg.FiniteCyclicDLP.FourierSamplingSupport P Ω)
    (w : SameCircuitScalarRecoveryWitness I P Ω support) : Prop :=
  w.output = I.privateScalar.value ∧
    w.output < P256DomainParameters.subgroupOrder ∧
    I.toECDLPInstance.CandidateScalar
      (w.output : ZMod I.toECDLPInstance.subgroupOrder) ∧
    GoodOutputEqPrivateScalar w ∧
    SameCircuitEvidence w ∧
    (w.resources.logicalQubits = 2330 ∧
      w.resources.toffoliGates = 126000000000 ∧
      w.resources.maximalToffoliDepth = 116000000000 ∧
      w.resources.classicalOps = 7 ∧
      w.resources.toffoliRunMultiplier = 1 ∧
      w.resources.depthRunMultiplier = 1 ∧
      w.resources.readyForFinalStatement = true) ∧
    (w.resources.logicalQubits =
        2 * w.params.orderRegisterQubits +
          w.scalarOracle.profile.logicalQubits ∧
      w.resources.toffoliGates =
        w.scalarOracle.resourceFields.toffoliGates ∧
      w.resources.maximalToffoliDepth =
        w.scalarOracle.resourceFields.toffoliDepth ∧
      w.resources.classicalOps =
        w.params.classicalPostProcessing.total)

/-- The witness satisfies the terminal P-256 same-Circuit scalar-recovery
statement. -/
theorem statement
    (w : SameCircuitScalarRecoveryWitness I P Ω support) :
    Statement I P Ω support w := by
  exact
    ⟨output_eq_privateScalar w, output_lt_order w, output_candidate w,
      good_output_eq_privateScalar w, sameCircuitEvidence w,
      w.resources_public_tuple, w.resources_from_sameCircuit_profile⟩

end SameCircuitScalarRecoveryWitness

/-- Public P-256 endpoint witness with no source-route support objects in its
signature.  The same-Circuit route is internalized by bridge theorems; this
public carrier exposes the P-256 input, returned scalar, success lower bound,
and accepted concrete resource tuple. -/
structure PublicEndpointWitness
    (I : P256DomainParameters.ScalarRecoveryInterface) where
  /-- Concrete public P-256 resource fields. -/
  resources : PublicStatementResources
  /-- Natural-number scalar returned by the endpoint. -/
  output : Nat
  /-- The returned scalar is the stored P-256 private scalar. -/
  output_eq_privateScalar : output = I.privateScalar.value
  /-- The returned scalar lies below the P-256 subgroup order. -/
  output_lt_order : output < P256DomainParameters.subgroupOrder
  /-- The returned scalar is a valid candidate for the induced ECDLP instance. -/
  output_candidate :
    I.toECDLPInstance.CandidateScalar
      (output : ZMod I.toECDLPInstance.subgroupOrder)
  /-- Numerator of the certified success lower bound. -/
  successNumerator : Nat
  /-- Denominator of the certified success lower bound. -/
  successDenominator : Nat
  /-- The success denominator is positive. -/
  successDenominator_pos : 0 < successDenominator
  /-- The certified success lower bound is at least two thirds. -/
  successAtLeastTwoThirds :
    2 * successDenominator <= 3 * successNumerator
  /-- The concrete resource tuple is the accepted P-256 baseline row after
  one-run success accounting and classical placeholder replacement. -/
  resources_tuple :
    resources.logicalQubits = 2330 ∧
      resources.toffoliGates = 126000000000 ∧
      resources.maximalToffoliDepth = 116000000000 ∧
      resources.classicalOps = 7 ∧
      resources.toffoliRunMultiplier = 1 ∧
      resources.depthRunMultiplier = 1 ∧
      resources.readyForFinalStatement = true

namespace PublicEndpointWitness

/-- Public endpoint statement for the P-256 logical-resource baseline. -/
def Statement (I : P256DomainParameters.ScalarRecoveryInterface)
    (w : PublicEndpointWitness I) : Prop :=
  w.output = I.privateScalar.value ∧
    w.output < P256DomainParameters.subgroupOrder ∧
    I.toECDLPInstance.CandidateScalar
      (w.output : ZMod I.toECDLPInstance.subgroupOrder) ∧
    2 * w.successDenominator <= 3 * w.successNumerator ∧
    0 < w.successDenominator ∧
    w.resources.logicalQubits = 2330 ∧
    w.resources.toffoliGates = 126000000000 ∧
    w.resources.maximalToffoliDepth = 116000000000 ∧
    w.resources.classicalOps = 7 ∧
    w.resources.toffoliRunMultiplier = 1 ∧
    w.resources.depthRunMultiplier = 1 ∧
    w.resources.readyForFinalStatement = true

/-- Every public endpoint witness satisfies the public P-256 statement. -/
theorem statement {I : P256DomainParameters.ScalarRecoveryInterface}
    (w : PublicEndpointWitness I) :
    Statement I w := by
  exact
    ⟨w.output_eq_privateScalar, w.output_lt_order, w.output_candidate,
      w.successAtLeastTwoThirds, w.successDenominator_pos,
      w.resources_tuple.1, w.resources_tuple.2.1,
      w.resources_tuple.2.2.1, w.resources_tuple.2.2.2.1,
      w.resources_tuple.2.2.2.2.1,
      w.resources_tuple.2.2.2.2.2.1,
      w.resources_tuple.2.2.2.2.2.2⟩

end PublicEndpointWitness

/-- Public P-256 theorem shape: there is an endpoint witness returning the
private scalar with success probability at least two thirds and the accepted
P-256 resource tuple. -/
def PublicTheoremShape
    (I : P256DomainParameters.ScalarRecoveryInterface) : Prop :=
  ∃ witness, PublicEndpointWitness.Statement I witness

namespace PublicTheoremShape

/-- Public theorem endpoint for the P-256 logical-resource baseline. -/
theorem main
    (I : P256DomainParameters.ScalarRecoveryInterface)
    (resources : PublicStatementResources)
    (output : Nat)
    (houtput_eq_privateScalar : output = I.privateScalar.value)
    (houtput_lt_order : output < P256DomainParameters.subgroupOrder)
    (houtput_candidate :
      I.toECDLPInstance.CandidateScalar
        (output : ZMod I.toECDLPInstance.subgroupOrder))
    (successNumerator successDenominator : Nat)
    (hsuccessDenominator : 0 < successDenominator)
    (hsuccessAtLeastTwoThirds :
      2 * successDenominator <= 3 * successNumerator)
    (hresources :
      resources.logicalQubits = 2330 ∧
        resources.toffoliGates = 126000000000 ∧
        resources.maximalToffoliDepth = 116000000000 ∧
        resources.classicalOps = 7 ∧
        resources.toffoliRunMultiplier = 1 ∧
        resources.depthRunMultiplier = 1 ∧
        resources.readyForFinalStatement = true) :
    PublicTheoremShape I := by
  refine ⟨?_, ?_⟩
  · exact
      { resources := resources
        output := output
        output_eq_privateScalar := houtput_eq_privateScalar
        output_lt_order := houtput_lt_order
        output_candidate := houtput_candidate
        successNumerator := successNumerator
        successDenominator := successDenominator
        successDenominator_pos := hsuccessDenominator
        successAtLeastTwoThirds := hsuccessAtLeastTwoThirds
        resources_tuple := hresources }
  · exact PublicEndpointWitness.statement _

end PublicTheoremShape

/-- Internal bridge from the same-Circuit P-256 scalar-recovery witness to the
support-free public theorem shape. -/
private theorem publicTheoremShape_of_sameCircuitWitness
    {I : P256DomainParameters.ScalarRecoveryInterface}
    [Fact P256DomainParameters.primeModulus.Prime]
    {G : Type u} [Group G]
    {P : QuantumAlg.FiniteCyclicDLP.KnownOrderProblem G}
    {Ω : Type v}
    {support : QuantumAlg.FiniteCyclicDLP.FourierSamplingSupport P Ω}
    (w : SameCircuitScalarRecoveryWitness I P Ω support) :
    PublicTheoremShape I := by
  let sampling :
    QuantumAlg.FiniteCyclicDLP.SamplingCertificate P Ω :=
    support.toSamplingCertificate
  have hsame := SameCircuitScalarRecoveryWitness.sameCircuitEvidence w
  have hsuccess :
      2 * sampling.successDenominator <= 3 * sampling.successNumerator :=
    hsame.2.1
  rcases SameCircuitScalarRecoveryWitness.statement w with
    ⟨houtput, hlt, hcandidate, _hgood, _hsame, hresources, _hroute⟩
  exact
    PublicTheoremShape.main I w.resources w.output houtput hlt hcandidate
      sampling.successNumerator sampling.successDenominator
      sampling.successDenominator_pos hsuccess hresources

end P256LogicalResources

end EllipticCurve
end QuantumAlg
