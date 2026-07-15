/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.EllipticCurve.DLP
public import QuantumAlg.Algorithms.EllipticCurve.Resources

/-!
# Success-accounted elliptic-curve resource fields

This module keeps the success multiplier separate from the per-run quantum
resource formulas and the classical post-processing taxonomy.  The quantum
fields reuse the signed-windowed ECDLP formulas of Håner--Jaques--Naehrig--
Roetteler--Soeken [HJN+20, numerical-estimates.tex:43-48,
appendix.tex:363-374].  The retry/failure-budget fields follow the repeated
discrete-logarithm sampling route in Shor's analysis [Sho95,
source.tex:1924-1987], while the classical post-processing count is the
finite-cyclic direct-recovery profile used by the DLP endpoint.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ECDLP
namespace SuccessAccountedResources

variable {eta : Factoring.FailureBudget}

/-- The per-run HJN resource tuple used by this success-accounting layer. -/
abbrev PerRunQuantumBounds :=
  QuantumAlg.EllipticCurve.Haner2020.GenericResourceBounds

/-- The explicit finite-cyclic DLP classical recovery profile for one run. -/
def perRunClassicalPostProcessing : ClassicalArithmeticProfile :=
  QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBound.toProfile

/-- The direct-recovery total exported from the finite-cyclic DLP taxonomy. -/
def directRecoveryUpperBoundTotal : Nat :=
  QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal

/-- Scalar projection of the one-run finite-cyclic DLP recovery profile. -/
def perRunClassicalOps : Nat :=
  perRunClassicalPostProcessing.total

@[simp] theorem perRunClassicalPostProcessing_total :
    perRunClassicalPostProcessing.total = directRecoveryUpperBoundTotal := by
  simpa [perRunClassicalPostProcessing, directRecoveryUpperBoundTotal] using
    QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBound_total

@[simp] theorem perRunClassicalOps_eq_directRecoveryUpperBoundTotal :
    perRunClassicalOps = directRecoveryUpperBoundTotal := by
  simp [perRunClassicalOps]

/-- The direct finite-cyclic DLP recovery profile contributes seven classical
arithmetic operations in the shared taxonomy. -/
theorem perRunClassicalOps_eq_seven :
    perRunClassicalOps = 7 := by
  rw [perRunClassicalOps_eq_directRecoveryUpperBoundTotal]
  norm_num [directRecoveryUpperBoundTotal,
    QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal]

/-- Repeat the classical post-processing profile according to the eta retry
certificate. -/
def successAccountedClassicalPostProcessing
    (cert : SuccessAmplification.EtaCertificate eta) :
    ClassicalArithmeticProfile :=
  ClassicalArithmeticProfile.scale cert.runCount perRunClassicalPostProcessing

/-- Scalar classical post-processing count after retry accounting. -/
def successAccountedClassicalOps
    (cert : SuccessAmplification.EtaCertificate eta) : Nat :=
  (successAccountedClassicalPostProcessing cert).total

@[simp] theorem successAccountedClassicalOps_eq_directRecoveryUpperBoundTotal
    (cert : SuccessAmplification.EtaCertificate eta) :
    successAccountedClassicalOps cert =
      cert.runCount * directRecoveryUpperBoundTotal := by
  simp [successAccountedClassicalOps, successAccountedClassicalPostProcessing]

/-- The retry-accounted direct-recovery classical count is exactly
`7 * runCount`, written with the retry multiplier first for resource formulas. -/
theorem successAccountedClassicalOps_eq_seven_mul
    (cert : SuccessAmplification.EtaCertificate eta) :
    successAccountedClassicalOps cert = cert.runCount * 7 := by
  rw [successAccountedClassicalOps_eq_directRecoveryUpperBoundTotal]
  norm_num [directRecoveryUpperBoundTotal,
    QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal]

/-- Scale per-run HJN gate/depth counts by the retry multiplier while keeping
the live logical-qubit footprint unchanged. -/
def successAccountedQuantumBounds
    (cert : SuccessAmplification.EtaCertificate eta)
    (perRun : PerRunQuantumBounds) : PerRunQuantumBounds where
  logicalQubits := perRun.logicalQubits
  tGates := cert.runCount * perRun.tGates
  tDepth := cert.runCount * perRun.tDepth
  allGateDepth := cert.runCount * perRun.allGateDepth
  totalGates := cert.runCount * perRun.totalGates

@[simp] theorem successAccountedQuantumBounds_logicalQubits
    (cert : SuccessAmplification.EtaCertificate eta)
    (perRun : PerRunQuantumBounds) :
    (successAccountedQuantumBounds cert perRun).logicalQubits =
      perRun.logicalQubits :=
  rfl

@[simp] theorem successAccountedQuantumBounds_tGates
    (cert : SuccessAmplification.EtaCertificate eta)
    (perRun : PerRunQuantumBounds) :
    (successAccountedQuantumBounds cert perRun).tGates =
      cert.runCount * perRun.tGates :=
  rfl

@[simp] theorem successAccountedQuantumBounds_tDepth
    (cert : SuccessAmplification.EtaCertificate eta)
    (perRun : PerRunQuantumBounds) :
    (successAccountedQuantumBounds cert perRun).tDepth =
      cert.runCount * perRun.tDepth :=
  rfl

@[simp] theorem successAccountedQuantumBounds_allGateDepth
    (cert : SuccessAmplification.EtaCertificate eta)
    (perRun : PerRunQuantumBounds) :
    (successAccountedQuantumBounds cert perRun).allGateDepth =
      cert.runCount * perRun.allGateDepth :=
  rfl

@[simp] theorem successAccountedQuantumBounds_totalGates
    (cert : SuccessAmplification.EtaCertificate eta)
    (perRun : PerRunQuantumBounds) :
    (successAccountedQuantumBounds cert perRun).totalGates =
      cert.runCount * perRun.totalGates :=
  rfl

/-- Success-accounted resource fields for an ECC scalar-recovery resource
statement.  The record keeps quantum resources, classical post-processing, and
the rational failure certificate as separate fields so downstream theorems do
not need asymptotic placeholders. -/
structure SuccessAccountedResourceBounds where
  /-- Number of quantum sampling runs certified for the failure budget. -/
  retryRunCount : Nat
  /-- Public upper bound on the retry count. -/
  retryUpperBound : Nat
  /-- Numerator of the target failure probability. -/
  targetFailureNumerator : Nat
  /-- Denominator of the target failure probability. -/
  targetFailureDenominator : Nat
  /-- Numerator of the certified achieved failure probability. -/
  certifiedFailureNumerator : Nat
  /-- Denominator of the certified achieved failure probability. -/
  certifiedFailureDenominator : Nat
  /-- Quantum resource bounds after success amplification. -/
  quantum : PerRunQuantumBounds
  /-- Classical post-processing profile paired with the sampling runs. -/
  classicalPostProcessing : ClassicalArithmeticProfile
  /-- Public-release readiness flag for the final statement. -/
  readyForFinalStatement : Bool
deriving DecidableEq

namespace SuccessAccountedResourceBounds

/-- Scalar classical post-processing count exposed by the structured profile. -/
def classicalOps (bounds : SuccessAccountedResourceBounds) : Nat :=
  bounds.classicalPostProcessing.total

/-- The retry multiplier is within the supplied upper-bound parameter. -/
def RetryUpperBoundSatisfied (bounds : SuccessAccountedResourceBounds) : Prop :=
  bounds.retryRunCount <= bounds.retryUpperBound

/-- The certified repeated-run failure rational is within the target rational
failure budget. -/
def CertifiedFailureWithinTarget
    (bounds : SuccessAccountedResourceBounds) : Prop :=
  bounds.certifiedFailureNumerator * bounds.targetFailureDenominator <=
    bounds.targetFailureNumerator * bounds.certifiedFailureDenominator

end SuccessAccountedResourceBounds

/-- Combine an HJN per-run resource choice with an eta retry certificate and the
canonical finite-cyclic DLP classical recovery profile. -/
def bounds
    (target : QuantumAlg.EllipticCurve.Haner2020.OptimizationTarget)
    (params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters)
    (cert : SuccessAmplification.EtaCertificate eta) :
    SuccessAccountedResourceBounds where
  retryRunCount := cert.runCount
  retryUpperBound := cert.logInvEtaUpperBound
  targetFailureNumerator := eta.failureNumerator
  targetFailureDenominator := eta.failureDenominator
  certifiedFailureNumerator := cert.repetitionModel.failureNumerator
  certifiedFailureDenominator := cert.repetitionModel.failureDenominator
  quantum :=
    successAccountedQuantumBounds cert
      (QuantumAlg.EllipticCurve.Haner2020.bounds target params)
  classicalPostProcessing := successAccountedClassicalPostProcessing cert
  readyForFinalStatement := cert.retrySpec.readyForFinalStatement

/-- Fieldwise characterization of the success-accounted ECC resource record. -/
theorem bounds_fields
    (target : QuantumAlg.EllipticCurve.Haner2020.OptimizationTarget)
    (params : QuantumAlg.EllipticCurve.Haner2020.FormulaParameters)
    (cert : SuccessAmplification.EtaCertificate eta) :
    let perRun := QuantumAlg.EllipticCurve.Haner2020.bounds target params
    let accounted := bounds target params cert
    accounted.retryRunCount = cert.runCount /\
      accounted.RetryUpperBoundSatisfied /\
      accounted.targetFailureNumerator = eta.failureNumerator /\
      accounted.targetFailureDenominator = eta.failureDenominator /\
      accounted.certifiedFailureNumerator =
        cert.repetitionModel.failureNumerator /\
      accounted.certifiedFailureDenominator =
        cert.repetitionModel.failureDenominator /\
      accounted.CertifiedFailureWithinTarget /\
      accounted.readyForFinalStatement = true /\
      accounted.quantum.logicalQubits = perRun.logicalQubits /\
      accounted.quantum.tGates = cert.runCount * perRun.tGates /\
      accounted.quantum.tDepth = cert.runCount * perRun.tDepth /\
      accounted.quantum.allGateDepth = cert.runCount * perRun.allGateDepth /\
      accounted.quantum.totalGates = cert.runCount * perRun.totalGates /\
      accounted.classicalOps =
        cert.runCount * directRecoveryUpperBoundTotal /\
      accounted.classicalOps = cert.runCount * 7 := by
  simp [bounds, SuccessAccountedResourceBounds.RetryUpperBoundSatisfied,
    SuccessAccountedResourceBounds.CertifiedFailureWithinTarget,
    SuccessAccountedResourceBounds.classicalOps,
    successAccountedClassicalPostProcessing, perRunClassicalPostProcessing,
    directRecoveryUpperBoundTotal,
    QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBound,
    QuantumAlg.FiniteCyclicDLP.ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal,
    SuccessAmplification.EtaCertificate.retrySpec,
    SuccessAmplification.etaRetrySpec,
    SuccessAmplification.EtaCertificate.repeatedFailure_le_eta,
    cert.runCount_le_logInvEtaUpperBound]

end SuccessAccountedResources
end ECDLP
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg
