/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.ResourceModel

/-!
# Order-finding exact-resource support

This module records the private exact-resource vocabulary for black-box order
finding. It keeps the public theorem's familiar one-query and inverse-QFT gate
counts, while exposing logical footprint, circuit depth, and classical
post-processing as concrete natural-number parameters rather than asymptotic
terms.

The one modular-exponentiation query plus Fourier/readout boundary follows the
black-box period-finding circuit shape in Shor's algorithm [Sho95,
source.tex:1124-1134] [dW19, qcnotes.tex:2155-2203].
-/

@[expose] public section

namespace QuantumAlg
namespace OrderFinding
namespace Resource

/-! ## Exact-resource profile -/

/-- Exact-resource dimensions for black-box order finding. The Fourier gate
families are separated so controlled phases and swaps do not disappear into a
single elementary-gate counter. -/
structure ExactResourceProfile where
  /-- Modular-exponentiation oracle calls. -/
  oracleQueries : ℕ
  /-- Total logical qubits/register footprint. -/
  logicalQubits : ℕ
  /-- Hadamard gates in the phase register. -/
  hadamardGates : ℕ
  /-- Controlled-phase gates in the inverse-QFT layer. -/
  controlledPhaseGates : ℕ
  /-- SWAP gates in the inverse-QFT bit-reversal layer. -/
  swapGates : ℕ
  /-- Maximal circuit depth in the selected exact circuit model. -/
  circuitDepth : ℕ
  /-- Structured classical arithmetic post-processing count. -/
  classicalArithmetic : ClassicalArithmeticProfile
deriving DecidableEq

namespace ExactResourceProfile

/-- Scalar classical operation count obtained from the shared taxonomy. -/
def classicalOps (profile : ExactResourceProfile) : ℕ :=
  profile.classicalArithmetic.total

/-- Projection to the older coarse theorem-resource profile. -/
def toResourceProfile (profile : ExactResourceProfile) : ResourceProfile where
  oracleQueries := profile.oracleQueries
  hadamardGates := profile.hadamardGates
  elementaryGates := profile.controlledPhaseGates + profile.swapGates
  classicalOps := profile.classicalOps

/-- Exact fieldwise count assertion for the private order-finding resource
target. -/
def HasExactCounts (profile : ExactResourceProfile)
    (oracleQueries logicalQubits hadamardGates controlledPhaseGates swapGates
      circuitDepth classicalOps : ℕ) : Prop :=
  profile.oracleQueries = oracleQueries ∧
    profile.logicalQubits = logicalQubits ∧
    profile.hadamardGates = hadamardGates ∧
    profile.controlledPhaseGates = controlledPhaseGates ∧
    profile.swapGates = swapGates ∧
    profile.circuitDepth = circuitDepth ∧
    profile.classicalOps = classicalOps

@[simp] theorem toResourceProfile_oracleQueries (profile : ExactResourceProfile) :
    profile.toResourceProfile.oracleQueries = profile.oracleQueries :=
  rfl

@[simp] theorem toResourceProfile_hadamardGates (profile : ExactResourceProfile) :
    profile.toResourceProfile.hadamardGates = profile.hadamardGates :=
  rfl

@[simp] theorem toResourceProfile_elementaryGates (profile : ExactResourceProfile) :
    profile.toResourceProfile.elementaryGates =
      profile.controlledPhaseGates + profile.swapGates :=
  rfl

@[simp] theorem toResourceProfile_classicalOps (profile : ExactResourceProfile) :
    profile.toResourceProfile.classicalOps = profile.classicalOps :=
  rfl

end ExactResourceProfile

/-! ## Source-count parameters -/

/-- Concrete source-count parameters for a black-box order-finding run. The
oracle query count is fixed at one; the remaining non-QFT dimensions are
supplied by the selected modular-exponentiation and classical-counting passes. -/
structure ResourceParameters where
  /-- Width of the phase register. -/
  phaseRegisterQubits : ℕ
  /-- Live target/oracle footprint outside the phase register. -/
  oracleRegisterQubits : ℕ
  /-- Depth contribution of the modular-exponentiation oracle call. -/
  oracleDepth : ℕ
  /-- Depth contribution of inverse QFT, readout, and any selected scheduling. -/
  fourierReadoutDepth : ℕ
  /-- Structured classical arithmetic post-processing count. -/
  classicalPostProcessing : ClassicalArithmeticProfile
deriving DecidableEq

namespace ResourceParameters

/-- One black-box modular-exponentiation oracle call. -/
def oracleQueryCount : ℕ :=
  1

/-- Total live footprint for the phase register plus oracle target/work
registers. -/
def logicalQubits (params : ResourceParameters) : ℕ :=
  params.phaseRegisterQubits + params.oracleRegisterQubits

/-- Inverse-QFT gate profile on the phase register. -/
def fourierGateProfile (params : ResourceParameters) : CircuitGateProfile where
  hadamardGates := params.phaseRegisterQubits
  controlledPhaseGates := params.phaseRegisterQubits * (params.phaseRegisterQubits - 1) / 2
  swapGates := params.phaseRegisterQubits / 2

/-- Maximal circuit depth in the selected sequential oracle/readout model. -/
def circuitDepth (params : ResourceParameters) : ℕ :=
  params.oracleDepth + params.fourierReadoutDepth

/-- Exact order-finding resource profile determined by the source-count
parameters. -/
def toExactResourceProfile (params : ResourceParameters) : ExactResourceProfile where
  oracleQueries := oracleQueryCount
  logicalQubits := params.logicalQubits
  hadamardGates := params.fourierGateProfile.hadamardGates
  controlledPhaseGates := params.fourierGateProfile.controlledPhaseGates
  swapGates := params.fourierGateProfile.swapGates
  circuitDepth := params.circuitDepth
  classicalArithmetic := params.classicalPostProcessing

@[simp] theorem fourierGateProfile_exact (params : ResourceParameters) :
    CircuitGateProfile.HasExactCounts params.fourierGateProfile
      params.phaseRegisterQubits
      (params.phaseRegisterQubits * (params.phaseRegisterQubits - 1) / 2)
      (params.phaseRegisterQubits / 2) :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem toExactResourceProfile_oracleQueries (params : ResourceParameters) :
    params.toExactResourceProfile.oracleQueries = 1 :=
  rfl

@[simp] theorem toExactResourceProfile_logicalQubits (params : ResourceParameters) :
    params.toExactResourceProfile.logicalQubits =
      params.phaseRegisterQubits + params.oracleRegisterQubits :=
  rfl

@[simp] theorem toExactResourceProfile_hadamardGates (params : ResourceParameters) :
    params.toExactResourceProfile.hadamardGates = params.phaseRegisterQubits :=
  rfl

@[simp] theorem toExactResourceProfile_controlledPhaseGates
    (params : ResourceParameters) :
    params.toExactResourceProfile.controlledPhaseGates =
      params.phaseRegisterQubits * (params.phaseRegisterQubits - 1) / 2 :=
  rfl

@[simp] theorem toExactResourceProfile_swapGates (params : ResourceParameters) :
    params.toExactResourceProfile.swapGates = params.phaseRegisterQubits / 2 :=
  rfl

@[simp] theorem toExactResourceProfile_circuitDepth (params : ResourceParameters) :
    params.toExactResourceProfile.circuitDepth =
      params.oracleDepth + params.fourierReadoutDepth :=
  rfl

@[simp] theorem toExactResourceProfile_classicalOps (params : ResourceParameters) :
    params.toExactResourceProfile.classicalOps =
      params.classicalPostProcessing.total :=
  rfl

/-- Exact fieldwise resource theorem for the profile generated by black-box
order-finding source-count parameters. -/
theorem toExactResourceProfile_hasExactCounts (params : ResourceParameters) :
    ExactResourceProfile.HasExactCounts params.toExactResourceProfile
      1
      (params.phaseRegisterQubits + params.oracleRegisterQubits)
      params.phaseRegisterQubits
      (params.phaseRegisterQubits * (params.phaseRegisterQubits - 1) / 2)
      (params.phaseRegisterQubits / 2)
      (params.oracleDepth + params.fourierReadoutDepth)
      params.classicalPostProcessing.total := by
  simp [ExactResourceProfile.HasExactCounts]

end ResourceParameters

/-! ## Classical post-processing counts -/

/-- Concrete count parameters for the classical post-processing after an
order-finding phase-register sample. Each field is a natural-number exact count
or an explicit upper-bound count supplied by the counting pass; no asymptotic
resource term is represented here. -/
structure PostProcessingCountParameters where
  /-- Continued-fraction iteration steps used to find candidate convergents. -/
  continuedFractionSteps : ℕ
  /-- Rational-reconstruction steps used to recover a numerator/denominator
  pair from the phase estimate. -/
  rationalReconstructionSteps : ℕ
  /-- GCD checks used in denominator recovery or candidate validation. -/
  gcdChecks : ℕ
  /-- Extended-Euclidean runs used by the selected recovery implementation. -/
  extendedEuclideanRuns : ℕ
  /-- Integer comparisons used by the recovery and validation pass. -/
  comparisonOps : ℕ
  /-- Modular multiplications used while validating order candidates. -/
  candidateModularMultiplications : ℕ
  /-- Modular reductions used while validating order candidates. -/
  candidateModularReductions : ℕ
deriving DecidableEq

namespace PostProcessingCountParameters

/-- Structured classical arithmetic profile for order-finding post-processing.
The number-theoretic fields cover continued fractions, rational
reconstruction, gcd, and EEA work; the bit/integer and modular fields cover the
candidate-validation arithmetic that remains after a denominator candidate has
been recovered. -/
def toProfile (params : PostProcessingCountParameters) :
    ClassicalArithmeticProfile where
  bitInteger :=
    { BitIntegerOperationProfile.zero with
      comparisons := params.comparisonOps
      modularReductions := params.candidateModularReductions }
  numberTheoretic :=
    { NumberTheoreticOperationProfile.zero with
      gcds := params.gcdChecks
      extendedEuclidean := params.extendedEuclideanRuns
      continuedFractions := params.continuedFractionSteps
      rationalReconstructions := params.rationalReconstructionSteps }
  modularField :=
    { ModularFieldOperationProfile.zero with
      multiplications := params.candidateModularMultiplications }
  groupControl := GroupControlOperationProfile.zero

@[simp] theorem toProfile_total (params : PostProcessingCountParameters) :
    params.toProfile.total =
      params.comparisonOps +
        params.candidateModularReductions +
        (params.gcdChecks +
          params.extendedEuclideanRuns +
          params.continuedFractionSteps +
          params.rationalReconstructionSteps) +
        params.candidateModularMultiplications := by
  simp [toProfile, ClassicalArithmeticProfile.total,
    BitIntegerOperationProfile.zero, ModularFieldOperationProfile.zero,
    GroupControlOperationProfile.zero,
    BitIntegerOperationProfile.total, NumberTheoreticOperationProfile.total,
    ModularFieldOperationProfile.total, GroupControlOperationProfile.total]

/-- Canonical explicit upper-bound profile for one black-box order-finding
post-processing pass. Shor's source route recovers a denominator by continued
fractions and then validates the candidate order; the selected upper bound
counts at most `phaseRegisterQubits + 1` continued-fraction steps, one
rational reconstruction, one gcd/EEA reduction to lowest terms, and a
square-and-multiply-style validation pass with at most `2 * phaseRegisterQubits`
modular multiplications and reductions. -/
def continuedFractionUpperBound (phaseRegisterQubits : ℕ) :
    PostProcessingCountParameters where
  continuedFractionSteps := phaseRegisterQubits + 1
  rationalReconstructionSteps := 1
  gcdChecks := 1
  extendedEuclideanRuns := 1
  comparisonOps := phaseRegisterQubits + 2
  candidateModularMultiplications := 2 * phaseRegisterQubits
  candidateModularReductions := 2 * phaseRegisterQubits

/-- Scalar form of the canonical order-finding post-processing upper bound. -/
def continuedFractionUpperBoundTotal (phaseRegisterQubits : ℕ) : ℕ :=
  (phaseRegisterQubits + 2) +
    (2 * phaseRegisterQubits) +
    (1 + 1 + (phaseRegisterQubits + 1) + 1) +
    (2 * phaseRegisterQubits)

theorem continuedFractionUpperBound_total (phaseRegisterQubits : ℕ) :
    (continuedFractionUpperBound phaseRegisterQubits).toProfile.total =
      continuedFractionUpperBoundTotal phaseRegisterQubits := by
  simp [continuedFractionUpperBound, continuedFractionUpperBoundTotal]

/-- The canonical order-finding post-processing count is an explicit natural
number upper-bound function, not an asymptotic resource term. -/
def continuedFractionUpperBoundSpec : ClassicalCountSpec ℕ :=
  ClassicalCountSpec.explicitUpperBound continuedFractionUpperBoundTotal

@[simp] theorem continuedFractionUpperBoundSpec_kind :
    continuedFractionUpperBoundSpec.kind = ClassicalCountKind.explicitUpperBound :=
  rfl

@[simp] theorem continuedFractionUpperBoundSpec_count (phaseRegisterQubits : ℕ) :
    continuedFractionUpperBoundSpec.count phaseRegisterQubits =
      continuedFractionUpperBoundTotal phaseRegisterQubits :=
  rfl

end PostProcessingCountParameters

namespace ResourceParameters

/-- Replace the order-finding classical post-processing profile by an explicit
count profile for continued-fraction recovery and candidate validation. -/
def withPostProcessingCounts (params : ResourceParameters)
    (counts : PostProcessingCountParameters) : ResourceParameters :=
  { params with classicalPostProcessing := counts.toProfile }

@[simp] theorem withPostProcessingCounts_classicalPostProcessing
    (params : ResourceParameters) (counts : PostProcessingCountParameters) :
    (params.withPostProcessingCounts counts).classicalPostProcessing =
      counts.toProfile :=
  rfl

@[simp] theorem withPostProcessingCounts_classicalOps
    (params : ResourceParameters) (counts : PostProcessingCountParameters) :
    (params.withPostProcessingCounts counts).classicalPostProcessing.total =
      counts.toProfile.total :=
  rfl

/-- Replace the order-finding classical post-processing profile by the canonical
continued-fraction explicit upper-bound function. -/
def withContinuedFractionUpperBound (params : ResourceParameters) :
    ResourceParameters :=
  params.withPostProcessingCounts
    (PostProcessingCountParameters.continuedFractionUpperBound
      params.phaseRegisterQubits)

@[simp] theorem withContinuedFractionUpperBound_classicalOps
    (params : ResourceParameters) :
    params.withContinuedFractionUpperBound.classicalPostProcessing.total =
      PostProcessingCountParameters.continuedFractionUpperBoundTotal
        params.phaseRegisterQubits := by
  rw [withContinuedFractionUpperBound, withPostProcessingCounts_classicalOps,
    PostProcessingCountParameters.continuedFractionUpperBound_total]

/-- Fieldwise exact-resource profile after selecting explicit classical
post-processing counts for order finding. -/
theorem withPostProcessingCounts_toExactResourceProfile_hasExactCounts
    (params : ResourceParameters) (counts : PostProcessingCountParameters) :
    (params.withPostProcessingCounts counts).toExactResourceProfile.HasExactCounts
      1
      (params.phaseRegisterQubits + params.oracleRegisterQubits)
      params.phaseRegisterQubits
      (params.phaseRegisterQubits * (params.phaseRegisterQubits - 1) / 2)
      (params.phaseRegisterQubits / 2)
      (params.oracleDepth + params.fourierReadoutDepth)
      counts.toProfile.total := by
  simpa [withPostProcessingCounts] using
    (params.withPostProcessingCounts counts).toExactResourceProfile_hasExactCounts

/-- Fieldwise exact-resource theorem after attaching the canonical
continued-fraction post-processing upper bound. -/
theorem withContinuedFractionUpperBound_toExactResourceProfile_hasExactCounts
    (params : ResourceParameters) :
    params.withContinuedFractionUpperBound.toExactResourceProfile.HasExactCounts
      1
      (params.phaseRegisterQubits + params.oracleRegisterQubits)
      params.phaseRegisterQubits
      (params.phaseRegisterQubits * (params.phaseRegisterQubits - 1) / 2)
      (params.phaseRegisterQubits / 2)
      (params.oracleDepth + params.fourierReadoutDepth)
      (PostProcessingCountParameters.continuedFractionUpperBoundTotal
        params.phaseRegisterQubits) := by
  rw [withContinuedFractionUpperBound]
  rw [← PostProcessingCountParameters.continuedFractionUpperBound_total
    params.phaseRegisterQubits]
  exact
    withPostProcessingCounts_toExactResourceProfile_hasExactCounts params
      (PostProcessingCountParameters.continuedFractionUpperBound
        params.phaseRegisterQubits)

end ResourceParameters

end Resource
end OrderFinding
end QuantumAlg
