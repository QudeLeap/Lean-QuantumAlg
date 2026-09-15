/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init

/-!
# Modular-arithmetic source resource models

This module classifies formulas reported by published modular-arithmetic
resource models and maps their resource dimensions to typed accounting fields.
Exact counts and explicit upper-bound functions are distinguished from estimates,
asymptotic formulas, and unsupported dimensions so that only mathematically
admissible formulas enter exact resource claims.

The represented source models cover the elementary arithmetic-network route
[VBE95, 9511018.tex:423-428], the compact Fourier-space Shor circuit [Bea02,
arxivfact.tex:205-213], and the Gidney-Ekera RSA resource estimates [GE19,
main.tex:70-79, 710-733].
-/

section

namespace QuantumAlg

/-- Mathematical status of a resource formula reported by a source. -/
inductive ResourceFormulaStatus where
  /-- The source formula is an exact natural-number count in its stated model. -/
  | exactCount
  /-- The source formula is a concrete natural-number upper-bound function. -/
  | explicitUpperBound
  /-- The source gives a concrete estimate, but not an exact count. -/
  | sourceBackedEstimate
  /-- The source gives only asymptotic notation for this resource. -/
  | asymptoticOnly
  /-- The source does not provide the required formula for this resource. -/
  | unsupported
deriving DecidableEq

namespace ResourceFormulaStatus

/-- A status supports an exact resource claim exactly when it is already an
exact count or a concrete upper-bound function. -/
def admissibleAsExactResource : ResourceFormulaStatus → Bool
  | .exactCount => true
  | .explicitUpperBound => true
  | .sourceBackedEstimate => false
  | .asymptoticOnly => false
  | .unsupported => false

/-- Whether a source-side formula is not admissible as an exact resource value. -/
def requiresPlaceholder (status : ResourceFormulaStatus) : Bool :=
  !status.admissibleAsExactResource

@[simp]
theorem exactCount_admissible :
    admissibleAsExactResource exactCount = true := rfl

@[simp]
theorem explicitUpperBound_admissible :
    admissibleAsExactResource explicitUpperBound = true := rfl

@[simp]
theorem sourceBackedEstimate_requiresPlaceholder :
    requiresPlaceholder sourceBackedEstimate = true := rfl

@[simp]
theorem asymptoticOnly_requiresPlaceholder :
    requiresPlaceholder asymptoticOnly = true := rfl

@[simp]
theorem unsupported_requiresPlaceholder :
    requiresPlaceholder unsupported = true := rfl

end ResourceFormulaStatus

/-- Published modular-arithmetic resource models represented by this module. -/
inductive ModularArithmeticSourceModel where
  /-- Vedral-Barenco-Ekert elementary arithmetic networks. -/
  | vedralBarencoEkert1995
  /-- Beauregard's compact Shor circuit using Fourier-space arithmetic. -/
  | beauregard2002
  /-- Gidney-Ekera abstract RSA resource estimates. -/
  | gidneyEkera2019Abstract
deriving DecidableEq

/-- Resource dimensions that may appear in modular-arithmetic source formulas. -/
inductive ModularArithmeticResourceDimension where
  | logicalQubits
  | dataQubits
  | workQubits
  | oracleQueries
  | hadamardGates
  | toffoliGates
  | tGates
  | cnotGates
  | singleQubitGates
  | elementaryGateCount
  | circuitDepth
  | toffoliDepth
  | classicalArithmeticOps
  | successAccounting
  | runRetryAccounting
deriving DecidableEq

/-- Stable source-accounting fields to which published resource dimensions can
be routed before they are represented by typed ledger units or scalar model
projections. -/
inductive ModularArithmeticProfileField where
  | logicalQubits
  | dataQubits
  | workQubits
  | oracleQueries
  | hadamardGates
  | toffoliGates
  | tGates
  | cnotGates
  | singleQubitGates
  | elementaryGateCount
  | circuitDepth
  | toffoliDepth
  | classicalArithmetic
deriving DecidableEq

namespace ModularArithmeticResourceDimension

/-- Default mapping from a resource dimension to a typed accounting field.
Dimensions outside the resource tuple, such as success accounting, have no
field in this model. -/
def profileField? : ModularArithmeticResourceDimension → Option ModularArithmeticProfileField
  | .logicalQubits => some .logicalQubits
  | .dataQubits => some .dataQubits
  | .workQubits => some .workQubits
  | .oracleQueries => some .oracleQueries
  | .hadamardGates => some .hadamardGates
  | .toffoliGates => some .toffoliGates
  | .tGates => some .tGates
  | .cnotGates => some .cnotGates
  | .singleQubitGates => some .singleQubitGates
  | .elementaryGateCount => some .elementaryGateCount
  | .circuitDepth => some .circuitDepth
  | .toffoliDepth => some .toffoliDepth
  | .classicalArithmeticOps => some .classicalArithmetic
  | .successAccounting => none
  | .runRetryAccounting => none

end ModularArithmeticResourceDimension

/-- Why a source resource decision remains a placeholder. -/
inductive PlaceholderReason where
  | sourceOnlyEstimates
  | sourceOnlyAsymptotic
  | unsupportedBySource
  | targetFieldMissing
deriving DecidableEq

/-- A source decision for one modular-arithmetic resource dimension. -/
structure SourceResourceDecision where
  /-- Formula status assigned to this source resource dimension. -/
  status : ResourceFormulaStatus
  /-- Optional modular-arithmetic profile field supplied by this source decision. -/
  profileField? : Option ModularArithmeticProfileField
  /-- Optional reason why this source field remains outside the exact profile. -/
  placeholderReason? : Option PlaceholderReason
deriving DecidableEq

namespace SourceResourceDecision

/-- A decision supports an exact resource value only when its formula status is
admissible and it maps to a typed accounting field. -/
def canInstantiateExactTarget (decision : SourceResourceDecision) : Bool :=
  decision.status.admissibleAsExactResource && decision.profileField?.isSome

/-- Whether this source decision remains non-exact in the typed accounting model. -/
def needsPlaceholder (decision : SourceResourceDecision) : Bool :=
  !decision.canInstantiateExactTarget

/-- Construct an admissible exact-count decision. -/
def exactFor (dimension : ModularArithmeticResourceDimension) : SourceResourceDecision where
  status := .exactCount
  profileField? := dimension.profileField?
  placeholderReason? := if dimension.profileField?.isSome then none else some .targetFieldMissing

/-- Construct an admissible explicit-upper-bound decision. -/
def upperBoundFor (dimension : ModularArithmeticResourceDimension) : SourceResourceDecision where
  status := .explicitUpperBound
  profileField? := dimension.profileField?
  placeholderReason? := if dimension.profileField?.isSome then none else some .targetFieldMissing

/-- Construct a decision for a concrete source estimate that is not an exact
resource count. -/
def estimateFor (dimension : ModularArithmeticResourceDimension) : SourceResourceDecision where
  status := .sourceBackedEstimate
  profileField? := dimension.profileField?
  placeholderReason? := some .sourceOnlyEstimates

/-- Construct a decision for asymptotic-only source formulas. -/
def asymptoticFor (dimension : ModularArithmeticResourceDimension) : SourceResourceDecision where
  status := .asymptoticOnly
  profileField? := dimension.profileField?
  placeholderReason? := some .sourceOnlyAsymptotic

/-- Construct a decision for dimensions unsupported by a source. -/
def unsupportedFor (dimension : ModularArithmeticResourceDimension) : SourceResourceDecision where
  status := .unsupported
  profileField? := dimension.profileField?
  placeholderReason? := some .unsupportedBySource

private theorem canInstantiateExactTarget_iff (decision : SourceResourceDecision) :
    decision.canInstantiateExactTarget = true ↔
      decision.status.admissibleAsExactResource = true ∧
        decision.profileField?.isSome = true := by
  simp [canInstantiateExactTarget]

@[simp]
theorem exactFor_canInstantiate_of_field
    (dimension : ModularArithmeticResourceDimension) (field : ModularArithmeticProfileField)
    (hfield : dimension.profileField? = some field) :
    (exactFor dimension).canInstantiateExactTarget = true := by
  simp [canInstantiateExactTarget, exactFor, hfield]

@[simp]
theorem upperBoundFor_canInstantiate_of_field
    (dimension : ModularArithmeticResourceDimension) (field : ModularArithmeticProfileField)
    (hfield : dimension.profileField? = some field) :
    (upperBoundFor dimension).canInstantiateExactTarget = true := by
  simp [canInstantiateExactTarget, upperBoundFor, hfield]

@[simp]
theorem estimateFor_needsPlaceholder (dimension : ModularArithmeticResourceDimension) :
    (estimateFor dimension).needsPlaceholder = true := by
  rfl

@[simp]
theorem asymptoticFor_needsPlaceholder (dimension : ModularArithmeticResourceDimension) :
    (asymptoticFor dimension).needsPlaceholder = true := by
  rfl

@[simp]
theorem unsupportedFor_needsPlaceholder (dimension : ModularArithmeticResourceDimension) :
    (unsupportedFor dimension).needsPlaceholder = true := by
  rfl

end SourceResourceDecision

/-- Status and accounting-field mapping for each represented
modular-arithmetic source model. Numerical coefficients are intentionally
outside this classification table. -/
def knownModularArithmeticSourceDecision
    (source : ModularArithmeticSourceModel)
    (dimension : ModularArithmeticResourceDimension) : SourceResourceDecision :=
  match source, dimension with
  | .vedralBarencoEkert1995, .logicalQubits => .upperBoundFor dimension
  | .vedralBarencoEkert1995, .dataQubits => .upperBoundFor dimension
  | .vedralBarencoEkert1995, .workQubits => .upperBoundFor dimension
  | .vedralBarencoEkert1995, .elementaryGateCount => .asymptoticFor dimension
  | .vedralBarencoEkert1995, .circuitDepth => .asymptoticFor dimension
  | .beauregard2002, .logicalQubits => .exactFor dimension
  | .beauregard2002, .dataQubits => .exactFor dimension
  | .beauregard2002, .workQubits => .exactFor dimension
  | .beauregard2002, .elementaryGateCount => .asymptoticFor dimension
  | .beauregard2002, .circuitDepth => .asymptoticFor dimension
  | .gidneyEkera2019Abstract, .logicalQubits => .estimateFor dimension
  | .gidneyEkera2019Abstract, .toffoliGates => .estimateFor dimension
  | .gidneyEkera2019Abstract, .circuitDepth => .estimateFor dimension
  | .gidneyEkera2019Abstract, .toffoliDepth => .estimateFor dimension
  | _, _ => .unsupportedFor dimension

private theorem known_estimate_needsPlaceholder
    (source : ModularArithmeticSourceModel)
    (dimension : ModularArithmeticResourceDimension)
    (hstatus : (knownModularArithmeticSourceDecision source dimension).status =
      ResourceFormulaStatus.sourceBackedEstimate) :
    (knownModularArithmeticSourceDecision source dimension).needsPlaceholder = true := by
  unfold SourceResourceDecision.needsPlaceholder SourceResourceDecision.canInstantiateExactTarget
  rw [hstatus]
  rfl

private theorem known_asymptotic_needsPlaceholder
    (source : ModularArithmeticSourceModel)
    (dimension : ModularArithmeticResourceDimension)
    (hstatus : (knownModularArithmeticSourceDecision source dimension).status =
      ResourceFormulaStatus.asymptoticOnly) :
    (knownModularArithmeticSourceDecision source dimension).needsPlaceholder = true := by
  unfold SourceResourceDecision.needsPlaceholder SourceResourceDecision.canInstantiateExactTarget
  rw [hstatus]
  rfl

end QuantumAlg

end
