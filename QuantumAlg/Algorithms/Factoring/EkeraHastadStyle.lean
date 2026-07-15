/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Primitives.MAU.ModularExponentiation
public import QuantumAlg.Util.FiniteCyclicDLP
public import QuantumAlg.Util.ShorFactoring

/-!
# Ekera-Hastad RSA factoring resource adapters

This module records exact natural-number adapters for the short-DLP route to
RSA-style factoring resource statements.

The route follows the Ekera-Hastad reduction from RSA factoring to short
discrete logarithms [EH17, source.tex:878-953], while its reusable
resource-envelope structure mirrors the modular-exponentiation accounting used
in Gidney-Ekera's RSA estimates [GE19, main.tex:459-522].
-/

@[expose] public section

namespace QuantumAlg
namespace Factoring

/-! ## Ekera-Hastad source-named retry vocabulary -/

namespace RetryMultiplierSpec

/-- Source-named retry multiplier for the Ekera-Hastad short-DLP route. The
count is an explicit upper-bound function for the selected failure budget, as
required by the final exact-resource statement [EH17, source.tex:806-842]. -/
def ekeraHastadShortDLP (budget : FailureBudget) (runCount : ℕ) :
    RetryMultiplierSpec :=
  explicitUpperBound budget runCount

@[simp] theorem ekeraHastadShortDLP_runCount
    (budget : FailureBudget) (runCount : ℕ) :
    (ekeraHastadShortDLP budget runCount).runCount = runCount :=
  rfl

@[simp] theorem ekeraHastadShortDLP_ready
    (budget : FailureBudget) (runCount : ℕ) :
    (ekeraHastadShortDLP budget runCount).readyForFinalStatement = true :=
  rfl

namespace RepetitionModel

/-- Source-named repetition certificate for the Ekera-Hastad short-DLP retry
multiplier. The probability comparison is supplied by the source-facing success
analysis; this constructor only records the exact natural-number fields. -/
def ekeraHastadShortDLP
    (budget : FailureBudget) {runCount failureNumerator failureDenominator : ℕ}
    (failureDenominator_pos : 0 < failureDenominator)
    (failure_le_budget :
      failureNumerator * budget.failureDenominator ≤
        budget.failureNumerator * failureDenominator)
    (runCount_pos : 0 < runCount) :
    RepetitionModel (RetryMultiplierSpec.ekeraHastadShortDLP budget runCount) where
  failureNumerator := failureNumerator
  failureDenominator := failureDenominator
  failureDenominator_pos := failureDenominator_pos
  failure_le_budget := failure_le_budget
  runCount_pos := runCount_pos
  ready := RetryMultiplierSpec.ekeraHastadShortDLP_ready budget runCount

end RepetitionModel

end RetryMultiplierSpec

/-! ## Ekera-Hastad short-DLP route resource adapters -/

namespace EkeraHastadStyle

/-- Route-specific modular-exponentiation parameters for the Ekera-Hastad
short-DLP factoring path. The route uses two reusable modular-exponentiation
blocks, together with any route-level selection, preparation, or cleanup
overhead that is not part of the generic arithmetic primitive. -/
structure RouteParameters where
  /-- Bit width of each RSA prime factor in this route model. -/
  factorBits : ℕ
  /-- Exponent-register width used by the left short-DLP sample. -/
  leftExponentWidth : ℕ
  /-- Exponent-register width used by the right short-DLP sample. -/
  rightExponentWidth : ℕ
  /-- Resource profile for the left modular exponentiation. -/
  leftExponentiation : ModularExponentiation.ResourceParameters
  /-- Resource profile for the right modular exponentiation. -/
  rightExponentiation : ModularExponentiation.ResourceParameters
  /-- Additional route-level overhead not included in either exponentiation. -/
  routeOverhead : ModularArithmeticResourceProfile
deriving DecidableEq

namespace RouteParameters

/-- Source-named constructor for the Ekera-Hastad RSA route. It keeps the
route-level overhead separate from the two reusable modular-exponentiation
components, matching the short-DLP route decomposition [EH17,
source.tex:878-953]. -/
def ekeraHastadRSA
    (factorBits : ℕ)
    (leftExponentiation rightExponentiation :
      ModularExponentiation.ResourceParameters)
    (routeOverhead : ModularArithmeticResourceProfile) : RouteParameters where
  factorBits := factorBits
  leftExponentWidth := leftExponentiation.exponentWidth
  rightExponentWidth := rightExponentiation.exponentWidth
  leftExponentiation := leftExponentiation
  rightExponentiation := rightExponentiation
  routeOverhead := routeOverhead

@[simp] theorem ekeraHastadRSA_leftExponentWidth
    (factorBits : ℕ)
    (leftExponentiation rightExponentiation :
      ModularExponentiation.ResourceParameters)
    (routeOverhead : ModularArithmeticResourceProfile) :
    (ekeraHastadRSA factorBits leftExponentiation rightExponentiation
      routeOverhead).leftExponentWidth =
        leftExponentiation.exponentWidth :=
  rfl

@[simp] theorem ekeraHastadRSA_rightExponentWidth
    (factorBits : ℕ)
    (leftExponentiation rightExponentiation :
      ModularExponentiation.ResourceParameters)
    (routeOverhead : ModularArithmeticResourceProfile) :
    (ekeraHastadRSA factorBits leftExponentiation rightExponentiation
      routeOverhead).rightExponentWidth =
        rightExponentiation.exponentWidth :=
  rfl

/-- Register-shape contract connecting the route parameters to the RSA factor
bit-length convention. The known modulus has at most `2 * factorBits` bits. -/
structure RegisterShape (route : RouteParameters) : Prop where
  leftModulusBits_eq : route.leftExponentiation.modulusBits = 2 * route.factorBits
  rightModulusBits_eq : route.rightExponentiation.modulusBits = 2 * route.factorBits
  leftExponentWidth_eq : route.leftExponentiation.exponentWidth = route.leftExponentWidth
  rightExponentWidth_eq : route.rightExponentiation.exponentWidth = route.rightExponentWidth

/-- Register-shape certificate for the source-named Ekera-Hastad RSA route
constructor. -/
theorem RegisterShape.ekeraHastadRSA
    {factorBits : ℕ}
    {leftExponentiation rightExponentiation :
      ModularExponentiation.ResourceParameters}
    {routeOverhead : ModularArithmeticResourceProfile}
    (hleft : leftExponentiation.modulusBits = 2 * factorBits)
    (hright : rightExponentiation.modulusBits = 2 * factorBits) :
    RegisterShape
      (ekeraHastadRSA factorBits leftExponentiation rightExponentiation
        routeOverhead) where
  leftModulusBits_eq := hleft
  rightModulusBits_eq := hright
  leftExponentWidth_eq := rfl
  rightExponentWidth_eq := rfl

/-- Circuit-shape contract tying the modular-exponentiation circuit registers
back to the route-level exponent widths. The modulus bit-size convention is
carried by `RegisterShape`; the concrete `ZMod N` circuits below carry the
typed accumulator semantics. -/
structure CircuitShape (route : RouteParameters) (leftM rightM : ℕ) : Prop where
  registerShape : RegisterShape route
  leftExponentRegister_eq : leftM = route.leftExponentWidth
  rightExponentRegister_eq : rightM = route.rightExponentWidth

namespace CircuitShape

/-- Circuit-shape certificate for the source-named Ekera-Hastad RSA route. -/
theorem ekeraHastadRSA
    {factorBits : ℕ}
    {leftExponentiation rightExponentiation :
      ModularExponentiation.ResourceParameters}
    {routeOverhead : ModularArithmeticResourceProfile}
    (hleft : leftExponentiation.modulusBits = 2 * factorBits)
    (hright : rightExponentiation.modulusBits = 2 * factorBits) :
    CircuitShape
      (RouteParameters.ekeraHastadRSA factorBits leftExponentiation
        rightExponentiation routeOverhead)
      leftExponentiation.exponentWidth rightExponentiation.exponentWidth where
  registerShape := RegisterShape.ekeraHastadRSA hleft hright
  leftExponentRegister_eq := rfl
  rightExponentRegister_eq := rfl

end CircuitShape

/-- The two modular-exponentiation blocks before route-level overhead is
attached. This reuses the generic modular-arithmetic recurrence rather than
duplicating it in the route-specific layer. -/
def modularExponentiationProfile (route : RouteParameters) :
    ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential route.leftExponentiation.toProfile
    route.rightExponentiation.toProfile

/-- Per-run quantum profile for the Ekera-Hastad route-specific modular
exponentiation work. -/
def perRunQuantumProfile (route : RouteParameters) :
    ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential route.routeOverhead
    route.modularExponentiationProfile

/-- Route-level per-run quantum circuit boundary for the Ekera-Hastad path.
The left and right modular-exponentiation components have concrete circuit
witnesses below; this boundary also carries route overhead in the same typed
`Circuit` object as the composed per-run quantum resource profile. -/
noncomputable def perRunQuantumCircuit (route : RouteParameters) :
    Circuit (Qubits route.perRunQuantumProfile.logicalQubits) :=
  Circuit.abstract (Qubits route.perRunQuantumProfile.logicalQubits)
    "ekera-hastad-route-per-run" route.perRunQuantumProfile.toResourceProfile
    route.perRunQuantumProfile.circuitDepth route.perRunQuantumProfile.oracleQueries

@[simp] theorem perRunQuantumCircuit_resources (route : RouteParameters) :
    route.perRunQuantumCircuit.resources =
      route.perRunQuantumProfile.toResourceProfile :=
  rfl

@[simp] theorem perRunQuantumCircuit_depth (route : RouteParameters) :
    route.perRunQuantumCircuit.depth = route.perRunQuantumProfile.circuitDepth :=
  rfl

@[simp] theorem perRunQuantumCircuit_queryDepth (route : RouteParameters) :
    route.perRunQuantumCircuit.queryDepth = route.perRunQuantumProfile.oracleQueries :=
  rfl

/-- Left modular-exponentiation circuit for one Ekera-Hastad quantum route
run. Route overhead remains a route-level resource profile. -/
noncomputable def leftQuantumCircuit {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    Circuit (ModularExponentiation.register m N) :=
  ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u
    route.leftExponentiation

/-- Right modular-exponentiation circuit for one Ekera-Hastad quantum route
run. Route overhead remains a route-level resource profile. -/
noncomputable def rightQuantumCircuit {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    Circuit (ModularExponentiation.register m N) :=
  ModularExponentiation.ResourceParameters.applyUnitCircuit (m := m) u
    route.rightExponentiation

@[simp] theorem leftQuantumCircuit_resources {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    (route.leftQuantumCircuit (m := m) u).resources =
      route.leftExponentiation.toResourceProfile :=
  rfl

@[simp] theorem leftQuantumCircuit_depth {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    (route.leftQuantumCircuit (m := m) u).depth =
      route.leftExponentiation.toProfile.circuitDepth :=
  rfl

@[simp] theorem leftQuantumCircuit_queryDepth {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    (route.leftQuantumCircuit (m := m) u).queryDepth =
      route.leftExponentiation.toProfile.oracleQueries :=
  rfl

@[simp] theorem rightQuantumCircuit_resources {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    (route.rightQuantumCircuit (m := m) u).resources =
      route.rightExponentiation.toResourceProfile :=
  rfl

@[simp] theorem rightQuantumCircuit_depth {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    (route.rightQuantumCircuit (m := m) u).depth =
      route.rightExponentiation.toProfile.circuitDepth :=
  rfl

@[simp] theorem rightQuantumCircuit_queryDepth {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    (route.rightQuantumCircuit (m := m) u).queryDepth =
      route.rightExponentiation.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for the left per-run quantum circuit. -/
theorem leftQuantumCircuit_apply_ket {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ)
    (x : ModularExponentiation.Data m N) :
    Circuit.apply (route.leftQuantumCircuit (m := m) u)
      (PureState.ket (R := ModularExponentiation.register m N) x :
        StateVector (ModularExponentiation.register m N)) =
      (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
        StateVector (ModularExponentiation.register m N)) :=
  ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_ket
    u route.leftExponentiation x

/-- Basis-state correctness for the right per-run quantum circuit. -/
theorem rightQuantumCircuit_apply_ket {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ)
    (x : ModularExponentiation.Data m N) :
    Circuit.apply (route.rightQuantumCircuit (m := m) u)
      (PureState.ket (R := ModularExponentiation.register m N) x :
        StateVector (ModularExponentiation.register m N)) =
      (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
        StateVector (ModularExponentiation.register m N)) :=
  ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_ket
    u route.rightExponentiation x

/-- Correctness/resource package for the left modular-exponentiation component
of one Ekera-Hastad quantum route run. -/
noncomputable def leftQuantumCircuitResourceCorrectWitness {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    ResourceCorrectWitness (R := ModularExponentiation.register m N)
      (∀ x : ModularExponentiation.Data m N,
        Circuit.apply (route.leftQuantumCircuit (m := m) u)
          (PureState.ket (R := ModularExponentiation.register m N) x :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
            StateVector (ModularExponentiation.register m N)))
      ((route.leftQuantumCircuit (m := m) u).resources =
          route.leftExponentiation.toResourceProfile ∧
        (route.leftQuantumCircuit (m := m) u).depth =
          route.leftExponentiation.toProfile.circuitDepth ∧
        (route.leftQuantumCircuit (m := m) u).queryDepth =
          route.leftExponentiation.toProfile.oracleQueries) := by
  exact
    { circuit := route.leftQuantumCircuit (m := m) u
      correctness := fun x => route.leftQuantumCircuit_apply_ket u x
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Correctness/resource package for the right modular-exponentiation component
of one Ekera-Hastad quantum route run. -/
noncomputable def rightQuantumCircuitResourceCorrectWitness {N m : ℕ} [NeZero N]
    (route : RouteParameters) (u : (ZMod N)ˣ) :
    ResourceCorrectWitness (R := ModularExponentiation.register m N)
      (∀ x : ModularExponentiation.Data m N,
        Circuit.apply (route.rightQuantumCircuit (m := m) u)
          (PureState.ket (R := ModularExponentiation.register m N) x :
            StateVector (ModularExponentiation.register m N)) =
          (PureState.ket (R := ModularExponentiation.register m N) (x.applyUnit u) :
            StateVector (ModularExponentiation.register m N)))
      ((route.rightQuantumCircuit (m := m) u).resources =
          route.rightExponentiation.toResourceProfile ∧
        (route.rightQuantumCircuit (m := m) u).depth =
          route.rightExponentiation.toProfile.circuitDepth ∧
        (route.rightQuantumCircuit (m := m) u).queryDepth =
          route.rightExponentiation.toProfile.oracleQueries) := by
  exact
    { circuit := route.rightQuantumCircuit (m := m) u
      correctness := fun x => route.rightQuantumCircuit_apply_ket u x
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Route-component upper bounds for the Ekera-Hastad per-run quantum profile:
route overhead plus the left and right modular-exponentiation blocks. -/
structure PublicBaselineBounds where
  /-- Explicit upper bound for the route overhead component. -/
  routeOverheadBound : ModularArithmeticResourceProfile
  /-- Explicit upper bound for the left exponentiation component. -/
  leftExponentiationBound : ModularExponentiation.ResourceParameters.PublicBaselineBounds
  /-- Explicit upper bound for the right exponentiation component. -/
  rightExponentiationBound : ModularExponentiation.ResourceParameters.PublicBaselineBounds
deriving DecidableEq

namespace PublicBaselineBounds

/-- Source-named constructor for the Ekera-Hastad route upper-bound record:
route overhead plus left and right modular-exponentiation upper-bound
certificates. -/
def ekeraHastadRSA
    (routeOverheadBound : ModularArithmeticResourceProfile)
    (leftExponentiationBound rightExponentiationBound :
      ModularExponentiation.ResourceParameters.PublicBaselineBounds) :
    PublicBaselineBounds where
  routeOverheadBound := routeOverheadBound
  leftExponentiationBound := leftExponentiationBound
  rightExponentiationBound := rightExponentiationBound

/-- Composed bound for the two modular-exponentiation blocks. -/
def modularExponentiationProfile
    (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.leftExponentiationBound.toProfile
    bounds.rightExponentiationBound.toProfile

/-- Composed route-level bound: overhead followed by the two exponentiation
blocks. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.routeOverheadBound
    bounds.modularExponentiationProfile

end PublicBaselineBounds

/-- Componentwise source-bound certificate for the Ekera-Hastad route quantum
profile. This packages the route overhead and the two reusable
modular-exponentiation component certificates. -/
structure SourceBoundCertificate
    (route : RouteParameters) (bounds : PublicBaselineBounds) : Prop where
  routeOverhead_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      route.routeOverhead bounds.routeOverheadBound
  leftExponentiation_le :
    ModularExponentiation.ResourceParameters.SourceBoundCertificate
      route.leftExponentiation bounds.leftExponentiationBound
  rightExponentiation_le :
    ModularExponentiation.ResourceParameters.SourceBoundCertificate
      route.rightExponentiation bounds.rightExponentiationBound

namespace SourceBoundCertificate

/-- Source-named componentwise certificate for the Ekera-Hastad RSA route. It
keeps the route overhead proof and the two reusable modular-exponentiation
source certificates as separate obligations. -/
theorem ekeraHastadRSA
    {route : RouteParameters}
    {routeOverheadBound : ModularArithmeticResourceProfile}
    {leftExponentiationBound rightExponentiationBound :
      ModularExponentiation.ResourceParameters.PublicBaselineBounds}
    (routeOverhead_le :
      ModularArithmeticResourceProfile.SupportsUpperBound
        route.routeOverhead routeOverheadBound)
    (leftExponentiation_le :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        route.leftExponentiation leftExponentiationBound)
    (rightExponentiation_le :
      ModularExponentiation.ResourceParameters.SourceBoundCertificate
        route.rightExponentiation rightExponentiationBound) :
    SourceBoundCertificate route
      (PublicBaselineBounds.ekeraHastadRSA routeOverheadBound
        leftExponentiationBound rightExponentiationBound) where
  routeOverhead_le := routeOverhead_le
  leftExponentiation_le := leftExponentiation_le
  rightExponentiation_le := rightExponentiation_le

/-- The componentwise certificate bounds the two route modular-exponentiation
blocks. -/
theorem modularExponentiationProfile
    {route : RouteParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate route bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      route.modularExponentiationProfile bounds.modularExponentiationProfile := by
  simpa [RouteParameters.modularExponentiationProfile,
    PublicBaselineBounds.modularExponentiationProfile] using
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential
      cert.leftExponentiation_le.supportsUpperBound
      cert.rightExponentiation_le.supportsUpperBound

/-- The componentwise certificate bounds the full per-run route quantum
profile. -/
theorem supportsUpperBound
    {route : RouteParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate route bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      route.perRunQuantumProfile bounds.toProfile := by
  simpa [RouteParameters.perRunQuantumProfile, PublicBaselineBounds.toProfile] using
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential
      cert.routeOverhead_le cert.modularExponentiationProfile

end SourceBoundCertificate

/-- Leading logical-qubit baseline obtained by converting a `2n`-bit modulus
register convention to factor bit length. Route-specific overhead remains in
the exact profile or in later public-bound inequalities. -/
def baselineLogicalQubits (factorBits : ℕ) : ℕ :=
  6 * factorBits

/-- Exact excess over the leading `6n` logical-qubit baseline. This is an exact
natural-number function, not an asymptotic term. -/
def workspaceAddend (route : RouteParameters) : ℕ :=
  route.perRunQuantumProfile.logicalQubits - baselineLogicalQubits route.factorBits

/-- Route-level source status for the quantum resource dimensions that feed the
private Ekera-Hastad support theorem. -/
structure QuantumResourceStatus where
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ResourceFormulaStatus
  /-- Gate-count component for Toffoli gates. -/
  toffoliGates : ResourceFormulaStatus
  /-- Depth component for circuit depth. -/
  circuitDepth : ResourceFormulaStatus
deriving DecidableEq

namespace QuantumResourceStatus

/-- Whether every route-specific quantum resource count is concrete enough for
a final theorem statement. -/
def readyForFinalStatement (status : QuantumResourceStatus) : Bool :=
  status.logicalQubits.admissibleAsExactResource &&
    status.toffoliGates.admissibleAsExactResource &&
      status.circuitDepth.admissibleAsExactResource

/-- Conservative status while route-specific source constants still need a
separate exact upper-bound instantiation. -/
def placeholder : QuantumResourceStatus where
  logicalQubits := .sourceBackedEstimate
  toffoliGates := .sourceBackedEstimate
  circuitDepth := .sourceBackedEstimate

/-- Route quantum-resource status when every tracked field is an exact count. -/
def exactCounts : QuantumResourceStatus where
  logicalQubits := .exactCount
  toffoliGates := .exactCount
  circuitDepth := .exactCount

/-- Route quantum-resource status when every tracked field is a concrete
upper-bound function. -/
def explicitUpperBounds : QuantumResourceStatus where
  logicalQubits := .explicitUpperBound
  toffoliGates := .explicitUpperBound
  circuitDepth := .explicitUpperBound

@[simp] theorem placeholder_not_ready :
    placeholder.readyForFinalStatement = false :=
  rfl

@[simp] theorem exactCounts_ready :
    exactCounts.readyForFinalStatement = true :=
  rfl

@[simp] theorem explicitUpperBounds_ready :
    explicitUpperBounds.readyForFinalStatement = true :=
  rfl

/-- A route quantum-resource status is final-ready when every tracked field is
an exact count or an explicit upper-bound function. -/
private theorem ready_of_field_status
    {status : QuantumResourceStatus}
    (hlogical : status.logicalQubits.admissibleAsExactResource = true)
    (htoffoli : status.toffoliGates.admissibleAsExactResource = true)
    (hdepth : status.circuitDepth.admissibleAsExactResource = true) :
    status.readyForFinalStatement = true := by
  simp [readyForFinalStatement, hlogical, htoffoli, hdepth]

end QuantumResourceStatus

@[simp] theorem modularExponentiationProfile_logicalQubits
    (route : RouteParameters) :
    route.modularExponentiationProfile.logicalQubits =
      max route.leftExponentiation.toProfile.logicalQubits
        route.rightExponentiation.toProfile.logicalQubits :=
  rfl

@[simp] theorem modularExponentiationProfile_toffoliGates
    (route : RouteParameters) :
    route.modularExponentiationProfile.toffoliGates =
      route.leftExponentiation.toProfile.toffoliGates +
        route.rightExponentiation.toProfile.toffoliGates :=
  rfl

@[simp] theorem modularExponentiationProfile_circuitDepth
    (route : RouteParameters) :
    route.modularExponentiationProfile.circuitDepth =
      route.leftExponentiation.toProfile.circuitDepth +
        route.rightExponentiation.toProfile.circuitDepth :=
  rfl

@[simp] theorem perRunQuantumProfile_logicalQubits
    (route : RouteParameters) :
    route.perRunQuantumProfile.logicalQubits =
      max route.routeOverhead.logicalQubits route.modularExponentiationProfile.logicalQubits :=
  rfl

@[simp] theorem perRunQuantumProfile_toffoliGates
    (route : RouteParameters) :
    route.perRunQuantumProfile.toffoliGates =
      route.routeOverhead.toffoliGates +
        route.modularExponentiationProfile.toffoliGates :=
  rfl

@[simp] theorem perRunQuantumProfile_circuitDepth
    (route : RouteParameters) :
    route.perRunQuantumProfile.circuitDepth =
      route.routeOverhead.circuitDepth +
        route.modularExponentiationProfile.circuitDepth :=
  rfl

/-- Exact decomposition of the route quantum footprint into the leading `6n`
baseline and an exact addend, once the source-backed route profile is known to
dominate the leading baseline. -/
private theorem perRunQuantumProfile_logicalQubits_eq_baseline_plus_addend
    (route : RouteParameters)
    (hbaseline :
      baselineLogicalQubits route.factorBits ≤ route.perRunQuantumProfile.logicalQubits) :
    route.perRunQuantumProfile.logicalQubits =
      baselineLogicalQubits route.factorBits + route.workspaceAddend := by
  unfold workspaceAddend
  omega

end RouteParameters

/-! ### Run and success accounting -/

/-- Run-count parameters for the Ekera-Hastad route. `sampleRunsPerAttempt`
counts quantum sampling circuits per logical attempt, while
`postProcessingRunsPerAttempt` counts classical post-processing passes per
attempt. The retry multiplier accounts for repeating attempts until the target
failure budget is met. -/
structure RunSuccessParameters where
  /-- Number of quantum samples used in one route attempt. -/
  sampleRunsPerAttempt : ℕ
  /-- Number of classical post-processing runs used in one route attempt. -/
  postProcessingRunsPerAttempt : ℕ
  /-- Retry model attached to the route-level success certificate. -/
  retry : RetryMultiplierSpec
  /-- Readiness status for the run-accounting fields. -/
  accountingStatus : ResourceFormulaStatus
deriving DecidableEq

namespace RunSuccessParameters

/-- Total quantum sampling runs after retry accounting. -/
def samplingMultiplier (params : RunSuccessParameters) : ℕ :=
  params.retry.runCount * params.sampleRunsPerAttempt

/-- Total classical post-processing runs after retry accounting. -/
def postProcessingRunCount (params : RunSuccessParameters) : ℕ :=
  params.retry.runCount * params.postProcessingRunsPerAttempt

/-- Whether the run/retry accounting is concrete enough for a final theorem
resource metric. -/
def readyForFinalStatement (params : RunSuccessParameters) : Bool :=
  params.retry.readyForFinalStatement &&
    params.accountingStatus.admissibleAsExactResource

/-- Placeholder accounting record. It specifies the fields that must eventually
be replaced by exact integer-valued functions or explicit upper-bound functions. -/
def placeholder (budget : FailureBudget) : RunSuccessParameters where
  sampleRunsPerAttempt := 1
  postProcessingRunsPerAttempt := 1
  retry :=
    { failureBudget := budget
      runCount := 1
      status := .sourceBackedEstimate }
  accountingStatus := .sourceBackedEstimate

/-- Run-success parameters whose retry multiplier and accounting fields are
exact counts. -/
def exactCounts
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) : RunSuccessParameters where
  sampleRunsPerAttempt := sampleRunsPerAttempt
  postProcessingRunsPerAttempt := postProcessingRunsPerAttempt
  retry := RetryMultiplierSpec.exactCount budget retryRuns
  accountingStatus := .exactCount

/-- Run-success parameters whose retry multiplier and accounting fields are
concrete upper-bound functions. -/
def explicitUpperBounds
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) : RunSuccessParameters where
  sampleRunsPerAttempt := sampleRunsPerAttempt
  postProcessingRunsPerAttempt := postProcessingRunsPerAttempt
  retry := RetryMultiplierSpec.explicitUpperBound budget retryRuns
  accountingStatus := .explicitUpperBound

/-- Source-named run/success record for the Ekera-Hastad RSA route. The retry
multiplier is the short-DLP source-named explicit upper bound, while the two
run-count fields remain ordinary natural-number functions of the final source
parameters. -/
def ekeraHastadRSA
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) : RunSuccessParameters where
  sampleRunsPerAttempt := sampleRunsPerAttempt
  postProcessingRunsPerAttempt := postProcessingRunsPerAttempt
  retry := RetryMultiplierSpec.ekeraHastadShortDLP budget retryRuns
  accountingStatus := .explicitUpperBound

@[simp] theorem placeholder_not_ready (budget : FailureBudget) :
    (placeholder budget).readyForFinalStatement = false :=
  rfl

@[simp] theorem exactCounts_ready
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    (exactCounts budget retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt).readyForFinalStatement = true :=
  rfl

@[simp] theorem explicitUpperBounds_ready
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    (explicitUpperBounds budget retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt).readyForFinalStatement = true :=
  rfl

@[simp] theorem ekeraHastadRSA_samplingMultiplier
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    (ekeraHastadRSA budget retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt).samplingMultiplier =
        retryRuns * sampleRunsPerAttempt :=
  rfl

@[simp] theorem ekeraHastadRSA_postProcessingRunCount
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    (ekeraHastadRSA budget retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt).postProcessingRunCount =
        retryRuns * postProcessingRunsPerAttempt :=
  rfl

@[simp] theorem ekeraHastadRSA_ready
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    (ekeraHastadRSA budget retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt).readyForFinalStatement = true :=
  rfl

/-- Run/retry accounting is final-ready when the retry multiplier and accounting
status are both exact counts or explicit upper-bound functions. -/
private theorem ready_of_status
    {params : RunSuccessParameters}
    (hretry : params.retry.readyForFinalStatement = true)
    (haccounting : params.accountingStatus.admissibleAsExactResource = true) :
    params.readyForFinalStatement = true := by
  simp [readyForFinalStatement, hretry, haccounting]

/-- Success-accounted quantum profile for the route: repeat the per-sample
quantum run by the exact sampling multiplier. -/
def successAccountedQuantumProfile (params : RunSuccessParameters)
    (route : RouteParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.repeatSequential params.samplingMultiplier
    route.perRunQuantumProfile

@[simp] theorem successAccountedQuantumProfile_eq_repeatSequential
    (params : RunSuccessParameters) (route : RouteParameters) :
    params.successAccountedQuantumProfile route =
      ModularArithmeticResourceProfile.repeatSequential params.samplingMultiplier
        route.perRunQuantumProfile :=
  rfl

theorem successAccountedQuantumProfile_toffoliGates
    (params : RunSuccessParameters) (route : RouteParameters) :
    (params.successAccountedQuantumProfile route).toffoliGates =
      params.samplingMultiplier * route.perRunQuantumProfile.toffoliGates := by
  unfold successAccountedQuantumProfile
  generalize params.samplingMultiplier = multiplier
  cases multiplier <;> simp [ModularArithmeticResourceProfile.zero]

theorem successAccountedQuantumProfile_circuitDepth
    (params : RunSuccessParameters) (route : RouteParameters) :
    (params.successAccountedQuantumProfile route).circuitDepth =
      params.samplingMultiplier * route.perRunQuantumProfile.circuitDepth := by
  unfold successAccountedQuantumProfile
  generalize params.samplingMultiplier = multiplier
  cases multiplier <;> simp [ModularArithmeticResourceProfile.zero]

theorem successAccountedQuantumProfile_logicalQubits_of_pos
    (params : RunSuccessParameters) (route : RouteParameters)
    (hpos : 0 < params.samplingMultiplier) :
    (params.successAccountedQuantumProfile route).logicalQubits =
      route.perRunQuantumProfile.logicalQubits := by
  unfold successAccountedQuantumProfile
  generalize hm : params.samplingMultiplier = multiplier at hpos ⊢
  cases multiplier with
  | zero => cases hpos
  | succ _ => rfl

/-- Success-accounted Ekera-Hastad route circuit obtained by repeating the
route-level per-run quantum circuit by the sampling multiplier. -/
noncomputable def successAccountedQuantumCircuit
    (params : RunSuccessParameters) (route : RouteParameters) :
    Circuit (Qubits route.perRunQuantumProfile.logicalQubits) :=
  Circuit.iterate params.samplingMultiplier route.perRunQuantumCircuit

@[simp] theorem successAccountedQuantumCircuit_resources
    (params : RunSuccessParameters) (route : RouteParameters) :
    (params.successAccountedQuantumCircuit route).resources =
      ResourceProfile.scale params.samplingMultiplier
        route.perRunQuantumProfile.toResourceProfile :=
  rfl

@[simp] theorem successAccountedQuantumCircuit_depth
    (params : RunSuccessParameters) (route : RouteParameters) :
    (params.successAccountedQuantumCircuit route).depth =
      params.samplingMultiplier * route.perRunQuantumProfile.circuitDepth :=
  rfl

@[simp] theorem successAccountedQuantumCircuit_queryDepth
    (params : RunSuccessParameters) (route : RouteParameters) :
    (params.successAccountedQuantumCircuit route).queryDepth =
      params.samplingMultiplier * route.perRunQuantumProfile.oracleQueries :=
  rfl

/-- The success-accounted route circuit carries the coarse projection of the
same repeated modular-arithmetic profile used by the exact support theorem. -/
theorem successAccountedQuantumCircuit_resources_eq_profile_projection
    (params : RunSuccessParameters) (route : RouteParameters) :
    (params.successAccountedQuantumCircuit route).resources =
      (params.successAccountedQuantumProfile route).toResourceProfile := by
  rw [successAccountedQuantumCircuit_resources,
    successAccountedQuantumProfile_eq_repeatSequential,
    ModularArithmeticResourceProfile.toResourceProfile_repeatSequential]

/-- Matrix semantics of the success-accounted Ekera-Hastad route circuit: the
same route-level per-run circuit is repeated by the sampling multiplier. -/
theorem successAccountedQuantumCircuit_matrix
    (params : RunSuccessParameters) (route : RouteParameters) :
    ((params.successAccountedQuantumCircuit route).matrix :
        HilbertOperator (Qubits route.perRunQuantumProfile.logicalQubits)) =
      ((route.perRunQuantumCircuit).matrix :
        HilbertOperator (Qubits route.perRunQuantumProfile.logicalQubits)) ^
        params.samplingMultiplier := by
  simpa [successAccountedQuantumCircuit] using
    Circuit.iterate_matrix params.samplingMultiplier route.perRunQuantumCircuit

/-- Resource-correct witness for the retry-scaled Ekera-Hastad route quantum
part. Route correctness beyond this circuit boundary remains represented by
the left/right component witnesses and route-level source certificates. -/
noncomputable def successAccountedQuantumCircuitResourceCorrectWitness
    (params : RunSuccessParameters) (route : RouteParameters) :
    ResourceCorrectWitness (R := Qubits route.perRunQuantumProfile.logicalQubits)
      (((params.successAccountedQuantumCircuit route).matrix :
          HilbertOperator (Qubits route.perRunQuantumProfile.logicalQubits)) =
        ((route.perRunQuantumCircuit).matrix :
          HilbertOperator (Qubits route.perRunQuantumProfile.logicalQubits)) ^
          params.samplingMultiplier)
      ((params.successAccountedQuantumCircuit route).resources =
          (params.successAccountedQuantumProfile route).toResourceProfile ∧
        (params.successAccountedQuantumCircuit route).depth =
          params.samplingMultiplier * route.perRunQuantumProfile.circuitDepth ∧
        (params.successAccountedQuantumCircuit route).queryDepth =
          params.samplingMultiplier * route.perRunQuantumProfile.oracleQueries) := by
  exact
    { circuit := params.successAccountedQuantumCircuit route
      correctness := successAccountedQuantumCircuit_matrix params route
      resources := by
        exact ⟨successAccountedQuantumCircuit_resources_eq_profile_projection
          params route, rfl, rfl⟩ }

end RunSuccessParameters

/-! ### Final-statement readiness -/

/-- Readiness certificate for replacing every Ekera-Hastad private-statement
placeholder by an exact count or explicit upper-bound function. -/
structure FinalResourceReadiness
    (quantum : RouteParameters.QuantumResourceStatus)
    (runs : RunSuccessParameters) : Prop where
  quantumReady : quantum.readyForFinalStatement = true
  runsReady : runs.readyForFinalStatement = true

namespace FinalResourceReadiness

/-- Route-level quantum resources and run/retry accounting together produce the
final readiness certificate once both sub-records are ready. -/
theorem of_ready
    {quantum : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters}
    (hquantum : quantum.readyForFinalStatement = true)
    (hruns : runs.readyForFinalStatement = true) :
    FinalResourceReadiness quantum runs where
  quantumReady := hquantum
  runsReady := hruns

/-- Final readiness when route quantum resources and run accounting are exact
counts. -/
private theorem of_exactCounts
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    FinalResourceReadiness
      RouteParameters.QuantumResourceStatus.exactCounts
      (RunSuccessParameters.exactCounts budget retryRuns sampleRunsPerAttempt
        postProcessingRunsPerAttempt) :=
  of_ready RouteParameters.QuantumResourceStatus.exactCounts_ready
    (RunSuccessParameters.exactCounts_ready budget retryRuns
      sampleRunsPerAttempt postProcessingRunsPerAttempt)

/-- Final readiness when route quantum resources and run accounting are
concrete upper-bound functions. -/
private theorem of_explicitUpperBounds
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    FinalResourceReadiness
      RouteParameters.QuantumResourceStatus.explicitUpperBounds
      (RunSuccessParameters.explicitUpperBounds budget retryRuns
        sampleRunsPerAttempt postProcessingRunsPerAttempt) :=
  of_ready RouteParameters.QuantumResourceStatus.explicitUpperBounds_ready
    (RunSuccessParameters.explicitUpperBounds_ready budget retryRuns
      sampleRunsPerAttempt postProcessingRunsPerAttempt)

/-- Final readiness for the source-named Ekera-Hastad RSA run/success record
when route quantum resources are supplied as explicit upper-bound functions. -/
private theorem of_ekeraHastadRSA
    (budget : FailureBudget) (retryRuns sampleRunsPerAttempt
      postProcessingRunsPerAttempt : ℕ) :
    FinalResourceReadiness
      RouteParameters.QuantumResourceStatus.explicitUpperBounds
      (RunSuccessParameters.ekeraHastadRSA budget retryRuns
        sampleRunsPerAttempt postProcessingRunsPerAttempt) :=
  of_ready RouteParameters.QuantumResourceStatus.explicitUpperBounds_ready
    (RunSuccessParameters.ekeraHastadRSA_ready budget retryRuns
      sampleRunsPerAttempt postProcessingRunsPerAttempt)

/-- The route-level placeholder status cannot be used as a final resource
theorem field. -/
private theorem not_of_quantum_placeholder (runs : RunSuccessParameters) :
    ¬ FinalResourceReadiness RouteParameters.QuantumResourceStatus.placeholder runs := by
  intro h
  simpa using h.quantumReady

/-- The run/retry placeholder record cannot be used as a final resource theorem
field. -/
private theorem not_of_runs_placeholder
    (quantum : RouteParameters.QuantumResourceStatus) (budget : FailureBudget) :
    ¬ FinalResourceReadiness quantum (RunSuccessParameters.placeholder budget) := by
  intro h
  simpa using h.runsReady

end FinalResourceReadiness

/-! ### Classical post-processing operation count -/

/-- Classical operation counts for one Ekera-Hastad post-processing pass,
separated by the shared operation taxonomy. -/
structure ClassicalPostProcessingParameters where
  /-- Classical number-theory work for short-DLP post-processing. -/
  shortDlpNumberTheory : NumberTheoreticOperationProfile
  /-- Classical group/control work for short-DLP post-processing. -/
  shortDlpGroupControl : GroupControlOperationProfile
  /-- Classical modular-consistency checks used by the route. -/
  modularChecks : ModularFieldOperationProfile
  /-- Classical validation work for candidate factors. -/
  factorValidation : BitIntegerOperationProfile
deriving DecidableEq

namespace ClassicalPostProcessingParameters

/-- Structured classical arithmetic profile for one Ekera-Hastad
post-processing pass. -/
def perRunProfile (params : ClassicalPostProcessingParameters) :
    ClassicalArithmeticProfile where
  bitInteger := params.factorValidation
  numberTheoretic := params.shortDlpNumberTheory
  modularField := params.modularChecks
  groupControl := params.shortDlpGroupControl

@[simp] theorem perRunProfile_bitInteger
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.bitInteger = params.factorValidation :=
  rfl

@[simp] theorem perRunProfile_numberTheoretic
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.numberTheoretic = params.shortDlpNumberTheory :=
  rfl

@[simp] theorem perRunProfile_modularField
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.modularField = params.modularChecks :=
  rfl

@[simp] theorem perRunProfile_groupControl
    (params : ClassicalPostProcessingParameters) :
    params.perRunProfile.groupControl = params.shortDlpGroupControl :=
  rfl

/-- Scalar classical operation count for one post-processing pass. -/
def perRunTotal (params : ClassicalPostProcessingParameters) : ℕ :=
  params.perRunProfile.total

@[simp] theorem perRunTotal_eq (params : ClassicalPostProcessingParameters) :
    params.perRunTotal = params.perRunProfile.total :=
  rfl

/-- Success-accounted structured classical profile. The run-success parameters
provide the exact number of post-processing passes. -/
def successAccountedProfile (runs : RunSuccessParameters)
    (params : ClassicalPostProcessingParameters) : ClassicalArithmeticProfile :=
  ClassicalArithmeticProfile.scale runs.postProcessingRunCount params.perRunProfile

@[simp] theorem successAccountedProfile_total
    (runs : RunSuccessParameters) (params : ClassicalPostProcessingParameters) :
    (successAccountedProfile runs params).total =
      runs.postProcessingRunCount * params.perRunTotal := by
  simp [successAccountedProfile, perRunTotal]

/-- Replace the classical component of a quantum profile with the
success-accounted Ekera-Hastad post-processing count. -/
def attachToProfile (runs : RunSuccessParameters)
    (params : ClassicalPostProcessingParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    ModularArithmeticResourceProfile :=
  { quantumProfile with classicalArithmetic := successAccountedProfile runs params }

theorem attachToProfile_classicalOps
    (runs : RunSuccessParameters) (params : ClassicalPostProcessingParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    (attachToProfile runs params quantumProfile).toResourceProfile.classicalOps =
      runs.postProcessingRunCount * params.perRunTotal := by
  simp [attachToProfile, ModularArithmeticResourceProfile.toResourceProfile]

/-- Parameters controlling the explicit short-DLP post-processing upper bound.
`searchSpaceBound` may be instantiated from a source formula such as the
square-root search bound, while `lookupTableBound` accounts for the associated
table construction. -/
structure UpperBoundParameters where
  /-- Bit width of each RSA prime factor in this route model. -/
  factorBits : ℕ
  /-- Explicit search-space bound used by the post-processing certificate. -/
  searchSpaceBound : ℕ
  /-- Explicit lookup-table bound used by the post-processing certificate. -/
  lookupTableBound : ℕ
deriving DecidableEq

/-- Source-named parameter record for the Ekera 2023 short-DLP
post-processing upper-bound pass. The search-space and lookup-table bounds are
explicit natural-number functions supplied by the source-facing counting pass. -/
def UpperBoundParameters.ekera2023
    (factorBits searchSpaceBound lookupTableBound : ℕ) : UpperBoundParameters where
  factorBits := factorBits
  searchSpaceBound := searchSpaceBound
  lookupTableBound := lookupTableBound

/-- Canonical explicit upper-bound profile for one Ekera-Hastad classical
post-processing pass. -/
def upperBoundProfile (params : UpperBoundParameters) :
    ClassicalPostProcessingParameters where
  shortDlpNumberTheory :=
    { NumberTheoreticOperationProfile.zero with
      gcds := 2
      extendedEuclidean := 2
      rationalReconstructions := params.factorBits + 1 }
  shortDlpGroupControl :=
    { GroupControlOperationProfile.zero with
      finiteCyclicGroupOps := params.searchSpaceBound
      lookupTableOps := params.lookupTableBound
      precomputeOps := params.lookupTableBound }
  modularChecks :=
    { ModularFieldOperationProfile.zero with
      multiplications := 2 * params.factorBits
      squarings := 2 * params.factorBits }
  factorValidation :=
    { BitIntegerOperationProfile.zero with
      comparisons := 4
      divisions := 2
      modularReductions := 2 }

/-- Scalar form of the canonical per-pass upper bound. -/
def upperBoundTotal (params : UpperBoundParameters) : ℕ :=
  5 * params.factorBits + params.searchSpaceBound + 2 * params.lookupTableBound + 13

theorem upperBoundProfile_total (params : UpperBoundParameters) :
    (upperBoundProfile params).perRunTotal = upperBoundTotal params := by
  simp [upperBoundProfile, upperBoundTotal, perRunTotal, perRunProfile,
    ClassicalArithmeticProfile.total, BitIntegerOperationProfile.zero,
    NumberTheoreticOperationProfile.zero, ModularFieldOperationProfile.zero,
    GroupControlOperationProfile.zero, NumberTheoreticOperationProfile.total,
    ModularFieldOperationProfile.total, BitIntegerOperationProfile.total,
    GroupControlOperationProfile.total]
  omega

/-- Per-pass upper-bound function packaged for theorem statements. -/
def upperBoundSpec : ClassicalCountSpec UpperBoundParameters :=
  ClassicalCountSpec.explicitUpperBound upperBoundTotal

/-- Source-named Ekera 2023 profile alias for downstream theorem statements. -/
def ekera2023UpperBoundProfile (params : UpperBoundParameters) :
    ClassicalPostProcessingParameters :=
  upperBoundProfile params

/-- Source-named Ekera 2023 scalar upper-bound specification. -/
def ekera2023UpperBoundSpec : ClassicalCountSpec UpperBoundParameters :=
  upperBoundSpec

@[simp] theorem upperBoundSpec_kind :
    upperBoundSpec.kind = ClassicalCountKind.explicitUpperBound :=
  rfl

@[simp] theorem ekera2023UpperBoundSpec_kind :
    ekera2023UpperBoundSpec.kind = ClassicalCountKind.explicitUpperBound :=
  rfl

@[simp] theorem upperBoundSpec_count (params : UpperBoundParameters) :
    upperBoundSpec.count params = upperBoundTotal params :=
  rfl

@[simp] theorem ekera2023UpperBoundSpec_count
    (params : UpperBoundParameters) :
    ekera2023UpperBoundSpec.count params = upperBoundTotal params :=
  rfl

/-- Success-accounted scalar classical upper bound. -/
def successAccountedUpperBoundTotal
    (runs : RunSuccessParameters) (params : UpperBoundParameters) : ℕ :=
  runs.postProcessingRunCount * upperBoundTotal params

/-- Success-accounted upper-bound function packaged for theorem statements. -/
def successAccountedUpperBoundSpec (runs : RunSuccessParameters) :
    ClassicalCountSpec UpperBoundParameters :=
  ClassicalCountSpec.explicitUpperBound
    (fun params => successAccountedUpperBoundTotal runs params)

@[simp] theorem successAccountedUpperBoundSpec_kind
    (runs : RunSuccessParameters) :
    (successAccountedUpperBoundSpec runs).kind = ClassicalCountKind.explicitUpperBound :=
  rfl

@[simp] theorem successAccountedUpperBoundSpec_count
    (runs : RunSuccessParameters) (params : UpperBoundParameters) :
    (successAccountedUpperBoundSpec runs).count params =
      successAccountedUpperBoundTotal runs params :=
  rfl

private theorem successAccountedUpperBound_total
    (runs : RunSuccessParameters) (params : UpperBoundParameters) :
    (successAccountedProfile runs (upperBoundProfile params)).total =
      successAccountedUpperBoundTotal runs params := by
  rw [successAccountedProfile_total, upperBoundProfile_total]
  rfl

/-- Attach the canonical Ekera-Hastad classical upper bound to an existing
success-accounted quantum profile. -/
def attachUpperBound (runs : RunSuccessParameters) (params : UpperBoundParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    ModularArithmeticResourceProfile :=
  attachToProfile runs (upperBoundProfile params) quantumProfile

theorem attachUpperBound_classicalOps
    (runs : RunSuccessParameters) (params : UpperBoundParameters)
    (quantumProfile : ModularArithmeticResourceProfile) :
    (attachUpperBound runs params quantumProfile).toResourceProfile.classicalOps =
      successAccountedUpperBoundTotal runs params := by
  rw [attachUpperBound, attachToProfile_classicalOps, upperBoundProfile_total]
  rfl

end ClassicalPostProcessingParameters

/-! ### Exact-resource support for public baseline fields -/

/-- Exact support profile for the Ekera-Hastad route: apply route run/success
accounting to the quantum route profile, then attach the canonical classical
post-processing upper bound. -/
def exactSupportProfile (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    ModularArithmeticResourceProfile :=
  ClassicalPostProcessingParameters.attachUpperBound runs classical
    (runs.successAccountedQuantumProfile route)

/-- Public-facing baseline fields as concrete natural-number bounds, including
an explicit run/retry accounting field for the private support theorem. -/
structure PublicBaselineBounds where
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ℕ
  /-- Gate-count component for Toffoli gates. -/
  toffoliGates : ℕ
  /-- Depth component for circuit depth. -/
  circuitDepth : ℕ
  /-- Explicit run/retry accounting count. -/
  runRetryAccounting : ℕ
  /-- Classical-operation count component. -/
  classicalOps : ℕ
deriving DecidableEq

namespace PublicBaselineBounds

/-- Public-bound parameters for the Ekera-Hastad resource expression after
replacing `log(2n)` by an explicit natural-number upper bound. -/
structure FormulaParameters where
  /-- Bit width of each RSA prime factor in this route model. -/
  factorBits : ℕ
  /-- Explicit upper bound for the logarithmic `2n` factor. -/
  logDoubleFactorBitsUpperBound : ℕ
deriving DecidableEq

namespace FormulaParameters

/-- Natural-number upper bound for `6n + 0.004 n log(2n)`. -/
def logicalQubitBound (params : FormulaParameters) : ℕ :=
  6 * params.factorBits +
    QuantumAlg.Nat.ceilDiv
      (params.factorBits * params.logDoubleFactorBitsUpperBound) 250

/-- Natural-number upper bound for `2.4n^3 + 0.004n^3 log(2n)`. -/
def toffoliBaseBound (params : FormulaParameters) : ℕ :=
  QuantumAlg.Nat.ceilDiv (12 * params.factorBits ^ 3) 5 +
    QuantumAlg.Nat.ceilDiv
      (params.factorBits ^ 3 * params.logDoubleFactorBitsUpperBound) 250

/-- Natural-number upper bound for `2000n^2 + 4n^2 log(2n)`. -/
def circuitDepthBaseBound (params : FormulaParameters) : ℕ :=
  2000 * params.factorBits ^ 2 +
    4 * params.factorBits ^ 2 * params.logDoubleFactorBitsUpperBound

/-- Success-accounted public bounds obtained by multiplying the per-sample
quantum base bounds by the exact sampling multiplier and attaching the explicit
classical upper-bound function. -/
def toPublicBaselineBounds
    (params : FormulaParameters) (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    PublicBaselineBounds where
  logicalQubits := params.logicalQubitBound
  toffoliGates := runs.samplingMultiplier * params.toffoliBaseBound
  circuitDepth := runs.samplingMultiplier * params.circuitDepthBaseBound
  runRetryAccounting := runs.samplingMultiplier + runs.postProcessingRunCount
  classicalOps :=
    ClassicalPostProcessingParameters.successAccountedUpperBoundTotal runs classical

@[simp] theorem toPublicBaselineBounds_logicalQubits
    (params : FormulaParameters) (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (params.toPublicBaselineBounds runs classical).logicalQubits =
      params.logicalQubitBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_toffoliGates
    (params : FormulaParameters) (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (params.toPublicBaselineBounds runs classical).toffoliGates =
      runs.samplingMultiplier * params.toffoliBaseBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_circuitDepth
    (params : FormulaParameters) (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (params.toPublicBaselineBounds runs classical).circuitDepth =
      runs.samplingMultiplier * params.circuitDepthBaseBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_runRetryAccounting
    (params : FormulaParameters) (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (params.toPublicBaselineBounds runs classical).runRetryAccounting =
      runs.samplingMultiplier + runs.postProcessingRunCount :=
  rfl

@[simp] theorem toPublicBaselineBounds_classicalOps
    (params : FormulaParameters) (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (params.toPublicBaselineBounds runs classical).classicalOps =
      ClassicalPostProcessingParameters.successAccountedUpperBoundTotal runs classical :=
  rfl

end FormulaParameters

end PublicBaselineBounds

/-- Exact support implies the public baseline when each exact field is bounded
by the corresponding public-facing bound. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile)
    (runs : RunSuccessParameters) (bounds : PublicBaselineBounds) : Prop where
  logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits
  toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates
  circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth
  runRetryAccounting_le :
    runs.samplingMultiplier + runs.postProcessingRunCount ≤ bounds.runRetryAccounting
  classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps

/-- Source-backed certificate for the private Ekera-Hastad exact-resource
support theorem. It records both that no placeholder status remains and that
the exact support profile is bounded by the public-facing fields. -/
structure SourceBoundCertificate
    (quantumStatus : RouteParameters.QuantumResourceStatus)
    (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters)
    (bounds : PublicBaselineBounds) : Prop where
  readiness : FinalResourceReadiness quantumStatus runs
  sampling_pos : 0 < runs.samplingMultiplier
  logicalQubits_le : route.perRunQuantumProfile.logicalQubits ≤ bounds.logicalQubits
  toffoliGates_le :
    runs.samplingMultiplier * route.perRunQuantumProfile.toffoliGates ≤ bounds.toffoliGates
  circuitDepth_le :
    runs.samplingMultiplier * route.perRunQuantumProfile.circuitDepth ≤ bounds.circuitDepth
  runRetryAccounting_le :
    runs.samplingMultiplier + runs.postProcessingRunCount ≤ bounds.runRetryAccounting
  classicalOps_le :
    ClassicalPostProcessingParameters.successAccountedUpperBoundTotal runs classical ≤
      bounds.classicalOps

@[simp] theorem exactSupportProfile_logicalQubits_of_pos
    (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters)
    (hpos : 0 < runs.samplingMultiplier) :
    (exactSupportProfile runs route classical).logicalQubits =
      route.perRunQuantumProfile.logicalQubits := by
  rw [exactSupportProfile,
    ClassicalPostProcessingParameters.attachUpperBound,
    ClassicalPostProcessingParameters.attachToProfile,
    RunSuccessParameters.successAccountedQuantumProfile_logicalQubits_of_pos
      runs route hpos]

@[simp] theorem exactSupportProfile_toffoliGates
    (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (exactSupportProfile runs route classical).toffoliGates =
      runs.samplingMultiplier * route.perRunQuantumProfile.toffoliGates := by
  rw [exactSupportProfile,
    ClassicalPostProcessingParameters.attachUpperBound,
    ClassicalPostProcessingParameters.attachToProfile,
    RunSuccessParameters.successAccountedQuantumProfile_toffoliGates]

@[simp] theorem exactSupportProfile_circuitDepth
    (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (exactSupportProfile runs route classical).circuitDepth =
      runs.samplingMultiplier * route.perRunQuantumProfile.circuitDepth := by
  rw [exactSupportProfile,
    ClassicalPostProcessingParameters.attachUpperBound,
    ClassicalPostProcessingParameters.attachToProfile,
    RunSuccessParameters.successAccountedQuantumProfile_circuitDepth]

theorem exactSupportProfile_classicalOps
    (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (exactSupportProfile runs route classical).toResourceProfile.classicalOps =
      ClassicalPostProcessingParameters.successAccountedUpperBoundTotal runs classical := by
  rw [exactSupportProfile, ClassicalPostProcessingParameters.attachUpperBound_classicalOps]

/-- Bridge theorem from the Ekera-Hastad exact-resource support profile to
public baseline fields. The public coefficients and logarithmic expressions are
instantiated outside this bridge as concrete natural-number upper bounds. -/
theorem exactSupportProfile_supportsPublicBaseline
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {bounds : PublicBaselineBounds}
    (hpos : 0 < runs.samplingMultiplier)
    (hlogical : route.perRunQuantumProfile.logicalQubits ≤ bounds.logicalQubits)
    (htoffoli :
      runs.samplingMultiplier * route.perRunQuantumProfile.toffoliGates ≤
        bounds.toffoliGates)
    (hdepth :
      runs.samplingMultiplier * route.perRunQuantumProfile.circuitDepth ≤
        bounds.circuitDepth)
    (hruns :
      runs.samplingMultiplier + runs.postProcessingRunCount ≤ bounds.runRetryAccounting)
    (hclassical :
      ClassicalPostProcessingParameters.successAccountedUpperBoundTotal runs classical ≤
        bounds.classicalOps) :
    SupportsPublicBaseline (exactSupportProfile runs route classical) runs bounds where
  logicalQubits_le := by
    rw [exactSupportProfile_logicalQubits_of_pos runs route classical hpos]
    exact hlogical
  toffoliGates_le := by
    rw [exactSupportProfile_toffoliGates]
    exact htoffoli
  circuitDepth_le := by
    rw [exactSupportProfile_circuitDepth]
    exact hdepth
  runRetryAccounting_le := hruns
  classicalOps_le := by
    rw [exactSupportProfile_classicalOps]
    exact hclassical

/-- A source-bound certificate discharges the private exact-resource support
obligations for the public Ekera-Hastad baseline fields. -/
theorem SourceBoundCertificate.supportsPublicBaseline
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate quantumStatus runs route classical bounds) :
    SupportsPublicBaseline (exactSupportProfile runs route classical) runs bounds :=
  exactSupportProfile_supportsPublicBaseline cert.sampling_pos cert.logicalQubits_le
    cert.toffoliGates_le cert.circuitDepth_le cert.runRetryAccounting_le cert.classicalOps_le

namespace SourceBoundCertificate

/-- An Ekera-Hastad source-bound certificate exposes that the route-level
quantum resource placeholders have been resolved before the final private
resource statement can use them. -/
private theorem finalQuantumResourceReady
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate quantumStatus runs route classical bounds) :
    quantumStatus.readyForFinalStatement = true :=
  cert.readiness.quantumReady

/-- An Ekera-Hastad source-bound certificate exposes that run/retry accounting
has been resolved before the final private resource statement can use it. -/
private theorem finalRunResourceReady
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate quantumStatus runs route classical bounds) :
    runs.readyForFinalStatement = true :=
  cert.readiness.runsReady

end SourceBoundCertificate

/-- Named private support endpoint for the exact-resource Ekera-Hastad RSA
factoring statement. It packages the final-status checks together with the
fieldwise exact-profile support for the public baseline formulas following the
short-DLP factoring route [EH17, source.tex:878-953] and the modular
exponentiation resource envelope [GE19, main.tex:459-522]. -/
structure PrivateResourceStatementWitness
    (quantumStatus : RouteParameters.QuantumResourceStatus)
    (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters)
    (params : PublicBaselineBounds.FormulaParameters) : Prop where
  readiness : FinalResourceReadiness quantumStatus runs
  supportsPublicBaseline :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical)

/-- Build the source-bound certificate from explicit natural-number public
baseline functions. The logarithmic source term has already been replaced by
`logDoubleFactorBitsUpperBound`, so the remaining hypotheses are ordinary
fieldwise natural-number upper bounds for one quantum sample. -/
theorem SourceBoundCertificate.of_formulaBounds
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hlogical : route.perRunQuantumProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      route.perRunQuantumProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      route.perRunQuantumProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SourceBoundCertificate quantumStatus runs route classical
      (params.toPublicBaselineBounds runs classical) where
  readiness := readiness
  sampling_pos := hpos
  logicalQubits_le := hlogical
  toffoliGates_le := Nat.mul_le_mul_left runs.samplingMultiplier htoffoli
  circuitDepth_le := Nat.mul_le_mul_left runs.samplingMultiplier hdepth
  runRetryAccounting_le := le_rfl
  classicalOps_le := le_rfl

/-- Direct endpoint from explicit Ekera-Hastad public formula bounds to support
of the public baseline record. This packages the source-bound certificate and
the exact support-profile bridge into one theorem for later theorem-node
realization. -/
theorem exactSupportProfile_supportsPublicBaseline_of_formulaBounds
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hlogical : route.perRunQuantumProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      route.perRunQuantumProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      route.perRunQuantumProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical) := by
  have cert :
      SourceBoundCertificate quantumStatus runs route classical
        (params.toPublicBaselineBounds runs classical) :=
    SourceBoundCertificate.of_formulaBounds readiness hpos hlogical htoffoli hdepth
  exact cert.supportsPublicBaseline

/-- Private endpoint from explicit Ekera-Hastad public formula bounds. The
result keeps the resolved route-resource and run/retry statuses next to the
exact support-profile comparison. -/
theorem PrivateResourceStatementWitness.of_formulaBounds
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hlogical : route.perRunQuantumProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli :
      route.perRunQuantumProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth :
      route.perRunQuantumProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params where
  readiness := readiness
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_of_formulaBounds readiness hpos
      hlogical htoffoli hdepth

/-- Direct Ekera-Hastad support from a route-level quantum upper-bound profile.
The route upper bound can be built from modular-exponentiation component
certificates and route overhead; this theorem only connects that composed route
bound to the public formula fields. -/
theorem exactSupportProfile_supportsPublicBaseline_of_routeUpperBound
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBound : ModularArithmeticResourceProfile}
    {params : PublicBaselineBounds.FormulaParameters}
    (_readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute :
      ModularArithmeticResourceProfile.SupportsUpperBound
        route.perRunQuantumProfile routeBound)
    (hlogical : routeBound.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBound.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBound.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical) :=
  exactSupportProfile_supportsPublicBaseline_of_formulaBounds
    (FinalResourceReadiness.of_ready _readiness.quantumReady _readiness.runsReady)
    hpos
    (hroute.logicalQubits_le.trans hlogical)
    (hroute.toffoliGates_le.trans htoffoli)
    (hroute.circuitDepth_le.trans hdepth)

/-- Private endpoint from a route-level quantum upper-bound profile. -/
theorem PrivateResourceStatementWitness.of_routeUpperBound
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBound : ModularArithmeticResourceProfile}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute :
      ModularArithmeticResourceProfile.SupportsUpperBound
        route.perRunQuantumProfile routeBound)
    (hlogical : routeBound.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBound.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBound.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params where
  readiness := readiness
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_of_routeUpperBound readiness hpos
      hroute hlogical htoffoli hdepth

/-- Direct Ekera-Hastad support from a componentwise route certificate:
route overhead plus left and right modular-exponentiation source certificates
are composed into the route upper bound consumed by the public formula bridge. -/
theorem exactSupportProfile_supportsPublicBaseline_of_routeCertificate
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical) :=
  exactSupportProfile_supportsPublicBaseline_of_routeUpperBound
    readiness hpos hroute.supportsUpperBound hlogical htoffoli hdepth

/-- Private endpoint from a componentwise route certificate. -/
theorem PrivateResourceStatementWitness.of_routeCertificate
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params where
  readiness := readiness
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_of_routeCertificate readiness hpos
      hroute hlogical htoffoli hdepth

/-- Circuit-aware Ekera-Hastad support from componentwise route certificates.
The left and right modular-exponentiation components expose typed circuit
witnesses, while route overhead, retry accounting, and classical
post-processing remain explicit route-level certificates. -/
theorem exactSupportProfile_supportsPublicBaseline_of_routeCircuitCertificates
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {leftN leftM rightN rightM : ℕ} [NeZero leftN] [NeZero rightN]
    (leftUnit : (ZMod leftN)ˣ) (rightUnit : (ZMod rightN)ˣ)
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical) ∧
      (∀ x : ModularExponentiation.Data leftM leftN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := leftM) leftUnit route.leftExponentiation)
          (PureState.ket (R := ModularExponentiation.register leftM leftN) x :
            StateVector (ModularExponentiation.register leftM leftN)) =
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            (x.applyUnit leftUnit) :
            StateVector (ModularExponentiation.register leftM leftN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).resources =
        route.leftExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).depth =
        route.leftExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).queryDepth =
        route.leftExponentiation.toProfile.oracleQueries ∧
      (∀ x : ModularExponentiation.Data rightM rightN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := rightM) rightUnit route.rightExponentiation)
          (PureState.ket (R := ModularExponentiation.register rightM rightN) x :
            StateVector (ModularExponentiation.register rightM rightN)) =
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            (x.applyUnit rightUnit) :
            StateVector (ModularExponentiation.register rightM rightN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).resources =
        route.rightExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).depth =
        route.rightExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).queryDepth =
        route.rightExponentiation.toProfile.oracleQueries := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exactSupportProfile_supportsPublicBaseline_of_routeCertificate
      readiness hpos hroute hlogical htoffoli hdepth
  · intro x
    exact ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_ket
      leftUnit route.leftExponentiation x
  · rfl
  · rfl
  · rfl
  · intro x
    exact ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_ket
      rightUnit route.rightExponentiation x
  · rfl
  · rfl
  · rfl

/-- Circuit-aware private Ekera-Hastad endpoint from componentwise route
certificates. -/
theorem PrivateResourceStatementWitness.of_routeCircuitCertificates
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {leftN leftM rightN rightM : ℕ} [NeZero leftN] [NeZero rightN]
    (leftUnit : (ZMod leftN)ˣ) (rightUnit : (ZMod rightN)ˣ)
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params ∧
      (∀ x : ModularExponentiation.Data leftM leftN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := leftM) leftUnit route.leftExponentiation)
          (PureState.ket (R := ModularExponentiation.register leftM leftN) x :
            StateVector (ModularExponentiation.register leftM leftN)) =
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            (x.applyUnit leftUnit) :
            StateVector (ModularExponentiation.register leftM leftN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).resources =
        route.leftExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).depth =
        route.leftExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).queryDepth =
        route.leftExponentiation.toProfile.oracleQueries ∧
      (∀ x : ModularExponentiation.Data rightM rightN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := rightM) rightUnit route.rightExponentiation)
          (PureState.ket (R := ModularExponentiation.register rightM rightN) x :
            StateVector (ModularExponentiation.register rightM rightN)) =
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            (x.applyUnit rightUnit) :
            StateVector (ModularExponentiation.register rightM rightN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).resources =
        route.rightExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).depth =
        route.rightExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).queryDepth =
        route.rightExponentiation.toProfile.oracleQueries := by
  rcases exactSupportProfile_supportsPublicBaseline_of_routeCircuitCertificates
      leftUnit rightUnit readiness hpos hroute hlogical htoffoli hdepth with
    ⟨hsupport, hleftCorrect, hleftResources, hleftDepth, hleftQuery,
      hrightCorrect, hrightResources, hrightDepth, hrightQuery⟩
  exact
    ⟨⟨readiness, hsupport⟩, hleftCorrect, hleftResources, hleftDepth, hleftQuery,
      hrightCorrect, hrightResources, hrightDepth, hrightQuery⟩

/-- Clean-circuit form of the componentwise Ekera-Hastad support theorem.
Both modular-exponentiation components are exposed in accumulator form on clean
flags, so the same typed circuits can carry correctness and resource
certificates through the route-level public baseline bridge. -/
theorem exactSupportProfile_supportsPublicBaseline_of_routeCleanCircuitCertificates
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {leftN leftM rightN rightM : ℕ} [NeZero leftN] [NeZero rightN]
    (leftUnit : (ZMod leftN)ˣ) (rightUnit : (ZMod rightN)ˣ)
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical) ∧
      (∀ exponent : Fin (2 ^ leftM), ∀ target : ZMod leftN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := leftM) leftUnit route.leftExponentiation)
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data leftM leftN) :
            StateVector (ModularExponentiation.register leftM leftN)) =
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            ({ exponent := exponent
               target := target * ((leftUnit ^ exponent.val : (ZMod leftN)ˣ) : ZMod leftN)
               flag := false } : ModularExponentiation.Data leftM leftN) :
            StateVector (ModularExponentiation.register leftM leftN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).resources =
        route.leftExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).depth =
        route.leftExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).queryDepth =
        route.leftExponentiation.toProfile.oracleQueries ∧
      (∀ exponent : Fin (2 ^ rightM), ∀ target : ZMod rightN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := rightM) rightUnit route.rightExponentiation)
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data rightM rightN) :
            StateVector (ModularExponentiation.register rightM rightN)) =
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            ({ exponent := exponent
               target :=
                target * ((rightUnit ^ exponent.val : (ZMod rightN)ˣ) : ZMod rightN)
               flag := false } : ModularExponentiation.Data rightM rightN) :
            StateVector (ModularExponentiation.register rightM rightN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).resources =
        route.rightExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).depth =
        route.rightExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).queryDepth =
        route.rightExponentiation.toProfile.oracleQueries := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exactSupportProfile_supportsPublicBaseline_of_routeCertificate
      readiness hpos hroute hlogical htoffoli hdepth
  · intro exponent target
    exact ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_clean_ket
      leftUnit route.leftExponentiation exponent target
  · rfl
  · rfl
  · rfl
  · intro exponent target
    exact ModularExponentiation.ResourceParameters.applyUnitCircuit_apply_clean_ket
      rightUnit route.rightExponentiation exponent target
  · rfl
  · rfl
  · rfl

/-- Clean-circuit private Ekera-Hastad endpoint from componentwise route
certificates. The first conjunct is the named private resource statement
witness; the remaining conjuncts keep both typed modular-exponentiation
circuits aligned with their clean accumulator actions and resource equalities. -/
theorem PrivateResourceStatementWitness.of_routeCleanCircuitCertificates
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {leftN leftM rightN rightM : ℕ} [NeZero leftN] [NeZero rightN]
    (leftUnit : (ZMod leftN)ˣ) (rightUnit : (ZMod rightN)ˣ)
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params ∧
      (∀ exponent : Fin (2 ^ leftM), ∀ target : ZMod leftN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := leftM) leftUnit route.leftExponentiation)
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data leftM leftN) :
            StateVector (ModularExponentiation.register leftM leftN)) =
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            ({ exponent := exponent
               target := target * ((leftUnit ^ exponent.val : (ZMod leftN)ˣ) : ZMod leftN)
               flag := false } : ModularExponentiation.Data leftM leftN) :
            StateVector (ModularExponentiation.register leftM leftN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).resources =
        route.leftExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).depth =
        route.leftExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).queryDepth =
        route.leftExponentiation.toProfile.oracleQueries ∧
      (∀ exponent : Fin (2 ^ rightM), ∀ target : ZMod rightN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := rightM) rightUnit route.rightExponentiation)
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data rightM rightN) :
            StateVector (ModularExponentiation.register rightM rightN)) =
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            ({ exponent := exponent
               target :=
                target * ((rightUnit ^ exponent.val : (ZMod rightN)ˣ) : ZMod rightN)
               flag := false } : ModularExponentiation.Data rightM rightN) :
            StateVector (ModularExponentiation.register rightM rightN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).resources =
        route.rightExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).depth =
        route.rightExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).queryDepth =
        route.rightExponentiation.toProfile.oracleQueries := by
  rcases exactSupportProfile_supportsPublicBaseline_of_routeCleanCircuitCertificates
      leftUnit rightUnit readiness hpos hroute hlogical htoffoli hdepth with
    ⟨hsupport, hleftCorrect, hleftResources, hleftDepth, hleftQuery,
      hrightCorrect, hrightResources, hrightDepth, hrightQuery⟩
  exact
    ⟨⟨readiness, hsupport⟩, hleftCorrect, hleftResources, hleftDepth, hleftQuery,
      hrightCorrect, hrightResources, hrightDepth, hrightQuery⟩

/-! ### Public-baseline theorem endpoints -/

/-- Source-named Ekera-Hastad RSA support theorem: componentwise route
certificates imply the public baseline fields through exact natural-number
upper bounds. The RSA route is the short-DLP reduction, and the resource fields
mirror the GE19 RSA estimate envelope [EH17, source.tex:878-953] [GE19,
main.tex:70-79, 1100-1108, 1785-1788]. -/
theorem exactSupportProfile_supportsPublicBaseline_ekeraHastadRSA
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical) :=
  exactSupportProfile_supportsPublicBaseline_of_routeCertificate readiness hpos
    hroute hlogical htoffoli hdepth

/-- Source-named private Ekera-Hastad RSA witness. It packages final readiness
with the exact-resource support implication for the public baseline [EH17,
source.tex:878-953] [GE19, main.tex:70-79, 1100-1108, 1785-1788]. -/
theorem PrivateResourceStatementWitness.ekeraHastadRSA
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params where
  readiness := readiness
  supportsPublicBaseline :=
    exactSupportProfile_supportsPublicBaseline_ekeraHastadRSA readiness hpos hroute
      hlogical htoffoli hdepth

/-- Public-baseline endpoint for the Ekera-Hastad exact support profile [EH17,
source.tex:878-953] [GE19, main.tex:70-79, 1100-1108, 1785-1788]. -/
theorem main_supportsPublicBaseline
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical) :=
  exactSupportProfile_supportsPublicBaseline_ekeraHastadRSA readiness hpos hroute
    hlogical htoffoli hdepth

/-- Private exact-resource endpoint for the Ekera-Hastad public baseline [EH17,
source.tex:878-953] [GE19, main.tex:70-79, 1100-1108, 1785-1788]. -/
theorem main_with_public_baseline
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params :=
  PrivateResourceStatementWitness.ekeraHastadRSA readiness hpos hroute hlogical
    htoffoli hdepth

/-- Circuit-aware Ekera-Hastad endpoint: the source-named private witness and
the left/right modular-exponentiation clean accumulator circuits are exposed
together, with the route circuit-shape contract tying the circuit exponents
back to the route parameters [EH17, source.tex:878-953] [GE19,
main.tex:70-79, 1100-1108, 1785-1788]. -/
theorem main_with_public_baseline_cleanCircuit
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {routeBounds : RouteParameters.PublicBaselineBounds}
    {params : PublicBaselineBounds.FormulaParameters}
    {leftN leftM rightN rightM : ℕ} [NeZero leftN] [NeZero rightN]
    (leftUnit : (ZMod leftN)ˣ) (rightUnit : (ZMod rightN)ˣ)
    (_shape : RouteParameters.CircuitShape route leftM rightM)
    (readiness : FinalResourceReadiness quantumStatus runs)
    (hpos : 0 < runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PrivateResourceStatementWitness quantumStatus runs route classical params ∧
      (∀ exponent : Fin (2 ^ leftM), ∀ target : ZMod leftN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := leftM) leftUnit route.leftExponentiation)
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data leftM leftN) :
            StateVector (ModularExponentiation.register leftM leftN)) =
          (PureState.ket (R := ModularExponentiation.register leftM leftN)
            ({ exponent := exponent
               target := target * ((leftUnit ^ exponent.val : (ZMod leftN)ˣ) : ZMod leftN)
               flag := false } : ModularExponentiation.Data leftM leftN) :
            StateVector (ModularExponentiation.register leftM leftN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).resources =
        route.leftExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).depth =
        route.leftExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := leftM) leftUnit route.leftExponentiation).queryDepth =
        route.leftExponentiation.toProfile.oracleQueries ∧
      (∀ exponent : Fin (2 ^ rightM), ∀ target : ZMod rightN,
        Circuit.apply
          (ModularExponentiation.ResourceParameters.applyUnitCircuit
            (m := rightM) rightUnit route.rightExponentiation)
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            ({ exponent := exponent, target := target, flag := false } :
              ModularExponentiation.Data rightM rightN) :
            StateVector (ModularExponentiation.register rightM rightN)) =
          (PureState.ket (R := ModularExponentiation.register rightM rightN)
            ({ exponent := exponent
               target :=
                target * ((rightUnit ^ exponent.val : (ZMod rightN)ˣ) : ZMod rightN)
               flag := false } : ModularExponentiation.Data rightM rightN) :
            StateVector (ModularExponentiation.register rightM rightN))) ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).resources =
        route.rightExponentiation.toResourceProfile ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).depth =
        route.rightExponentiation.toProfile.circuitDepth ∧
      (ModularExponentiation.ResourceParameters.applyUnitCircuit
          (m := rightM) rightUnit route.rightExponentiation).queryDepth =
        route.rightExponentiation.toProfile.oracleQueries :=
  PrivateResourceStatementWitness.of_routeCleanCircuitCertificates leftUnit rightUnit
    readiness hpos hroute hlogical htoffoli hdepth

/-! ## Correctness bridge from short DLP to factor return -/

/-- Source route data tying the Ekerå-Håstad short-DLP secret to the RSA
half-sum.  In the RSA route the short discrete logarithm is
`d = (p + q - 2) / 2`, so the half-sum is `d + 1` and satisfies
`2(d+1)=p+q` [EH17, source.tex:908-923]. -/
@[nolint simpNF]
structure ShortDLPHalfSumSource
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    (inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params)
    (model : ShorFactoring.SemiprimeFactorModel N) where
  /-- Source half-sum `c = d + 1`. -/
  halfSum : ℕ
  /-- The source half-sum is the recovered short-DLP secret plus one. -/
  halfSum_eq_secret_succ : halfSum = inst.secret + 1
  /-- The RSA source equation `2c = p + q`. -/
  two_mul_halfSum_eq_factor_sum :
    2 * halfSum = model.leftFactor + model.rightFactor

-- Generated structure lemma; expanding this source-route package as `[simp]`
-- would expose route fields rather than the half-sum API used below.
attribute [-simp] ShortDLPHalfSumSource.mk.injEq
attribute [nolint simpNF] ShortDLPHalfSumSource.mk.injEq

namespace ShortDLPHalfSumSource

/-- The Ekerå-Håstad short-DLP source data imply the half-sum relation consumed
by the RSA quadratic recovery step [EH17, source.tex:912-923]. -/
theorem secret_succ_half_sum_relation
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (source : ShortDLPHalfSumSource inst model) :
    2 * (inst.secret + 1) = model.leftFactor + model.rightFactor := by
  rw [← source.halfSum_eq_secret_succ]
  exact source.two_mul_halfSum_eq_factor_sum

end ShortDLPHalfSumSource

/-- Source data for the Ekerå-Håstad quadratic-root recovery step.  Given the
half-sum `c=d+1`, the recovered root candidate is accepted through the source
quadratic `N = 2cq - q^2`; the candidate is kept as route data rather than
selected from the declared factors [EH17, source.tex:915-925]. -/
structure QuadraticRootCandidateSource {N : ℕ}
    (model : ShorFactoring.SemiprimeFactorModel N)
    (halfSum candidate : ℕ) where
  /-- Source quadratic equation `N = 2c q - q^2`, written as a product. -/
  quadratic_product_eq :
    candidate * (2 * halfSum - candidate) = N

namespace QuadraticRootCandidateSource

/-- For distinct prime factors `p,q ≥ 2`, the predecessor of their sum is
strictly smaller than their product. This arithmetic contradiction rejects the
trivial roots in the Ekerå-Hastad quadratic recovery step [EH17,
source.tex:915-925]. -/
theorem factor_sum_pred_lt_product
    {N : ℕ}
    (model : ShorFactoring.SemiprimeFactorModel N) :
    model.leftFactor + model.rightFactor - 1 <
      model.leftFactor * model.rightFactor := by
  have hleft : 2 ≤ model.leftFactor := model.left_prime.two_le
  have hright : 2 ≤ model.rightFactor := model.right_prime.two_le
  have hright_le_twice_pred :
      model.rightFactor ≤ 2 * (model.rightFactor - 1) := by
    omega
  have htwice_pred_le_left_mul :
      2 * (model.rightFactor - 1) ≤
        model.leftFactor * (model.rightFactor - 1) :=
    Nat.mul_le_mul_right _ hleft
  have hright_le_left_mul_pred :
      model.rightFactor ≤
        model.leftFactor * (model.rightFactor - 1) :=
    le_trans hright_le_twice_pred htwice_pred_le_left_mul
  have hsum_le_product :
      model.leftFactor + model.rightFactor ≤
        model.leftFactor * model.rightFactor := by
    have hsum_le :
        model.leftFactor + model.rightFactor ≤
          model.leftFactor + model.leftFactor * (model.rightFactor - 1) :=
      Nat.add_le_add_left hright_le_left_mul_pred _
    have hprod_decomp :
        model.leftFactor * (model.rightFactor - 1) + model.leftFactor =
          model.leftFactor * model.rightFactor := by
      rw [← Nat.mul_succ]
      have hsucc :
          (model.rightFactor - 1).succ = model.rightFactor :=
        Nat.succ_pred_eq_of_pos model.right_prime.pos
      rw [hsucc]
    calc
      model.leftFactor + model.rightFactor ≤
          model.leftFactor + model.leftFactor * (model.rightFactor - 1) := hsum_le
      _ = model.leftFactor * (model.rightFactor - 1) + model.leftFactor := by
        rw [Nat.add_comm]
      _ = model.leftFactor * model.rightFactor := hprod_decomp
  have hpred_lt_sum :
      model.leftFactor + model.rightFactor - 1 <
        model.leftFactor + model.rightFactor := by
    omega
  exact lt_of_lt_of_le hpred_lt_sum hsum_le_product

/-- The candidate recovered from the Ekerå-Håstad source quadratic divides the
RSA modulus [EH17, source.tex:915-925]. -/
theorem candidate_dvd_modulus
    {N halfSum candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (source : QuadraticRootCandidateSource model halfSum candidate) :
    candidate ∣ N :=
  ⟨2 * halfSum - candidate, source.quadratic_product_eq.symm⟩

/-- The recovered quadratic root is positive because it divides the nonzero RSA
modulus [EH17, source.tex:915-925]. -/
theorem candidate_pos
    {N halfSum candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (source : QuadraticRootCandidateSource model halfSum candidate) :
    0 < candidate := by
  by_contra hnot
  have hzero : candidate = 0 := Nat.eq_zero_of_not_pos hnot
  rcases source.candidate_dvd_modulus with ⟨witness, hwitness⟩
  have hNzero : N = 0 := by
    simpa [hzero] using hwitness
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one
  omega

/-- The recovered quadratic root cannot be the trivial root `1`; otherwise the
source half-sum equation would force `pq = p + q - 1`, contradicting
`p,q ≥ 2` [EH17, source.tex:915-925]. -/
theorem candidate_ne_one
    {N halfSum candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (source : QuadraticRootCandidateSource model halfSum candidate)
    (half_sum_relation :
      2 * halfSum = model.leftFactor + model.rightFactor) :
    candidate ≠ 1 := by
  intro hcandidate
  have hN_eq_half_pred : N = 2 * halfSum - 1 := by
    simpa [hcandidate] using source.quadratic_product_eq.symm
  have hN_eq_sum_pred :
      N = model.leftFactor + model.rightFactor - 1 := by
    omega
  have hprod_eq :
      model.leftFactor * model.rightFactor =
        model.leftFactor + model.rightFactor - 1 := by
    rw [← model.product_eq]
    exact hN_eq_sum_pred
  have hlt := factor_sum_pred_lt_product model
  rw [hprod_eq] at hlt
  exact (lt_irrefl _) hlt

/-- The recovered quadratic root cannot be the whole RSA modulus. If it were,
the quadratic equation would again collapse to `pq = p + q - 1`, contradicting
the semiprime source model [EH17, source.tex:915-925]. -/
theorem candidate_ne_modulus
    {N halfSum candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (source : QuadraticRootCandidateSource model halfSum candidate)
    (half_sum_relation :
      2 * halfSum = model.leftFactor + model.rightFactor) :
    candidate ≠ N := by
  intro hcandidate
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one
  have hfactor : 2 * halfSum - N = 1 := by
    apply Nat.mul_left_cancel hNpos
    simpa [hcandidate] using source.quadratic_product_eq
  have hN_eq_sum_pred :
      N = model.leftFactor + model.rightFactor - 1 := by
    omega
  have hprod_eq :
      model.leftFactor * model.rightFactor =
        model.leftFactor + model.rightFactor - 1 := by
    rw [← model.product_eq]
    exact hN_eq_sum_pred
  have hlt := factor_sum_pred_lt_product model
  rw [hprod_eq] at hlt
  exact (lt_irrefl _) hlt

/-- The recovered quadratic root is nontrivial. -/
theorem candidate_gt_one
    {N halfSum candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (source : QuadraticRootCandidateSource model halfSum candidate)
    (half_sum_relation :
      2 * halfSum = model.leftFactor + model.rightFactor) :
    1 < candidate := by
  have hpos := source.candidate_pos
  exact lt_of_le_of_ne (Nat.succ_le_of_lt hpos)
    (Ne.symm (source.candidate_ne_one half_sum_relation))

/-- The recovered quadratic root is a proper divisor candidate. -/
theorem candidate_lt_modulus
    {N halfSum candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (source : QuadraticRootCandidateSource model halfSum candidate)
    (half_sum_relation :
      2 * halfSum = model.leftFactor + model.rightFactor) :
    candidate < N := by
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one
  have hle : candidate ≤ N :=
    Nat.le_of_dvd hNpos source.candidate_dvd_modulus
  exact lt_of_le_of_ne hle (source.candidate_ne_modulus half_sum_relation)

end QuadraticRootCandidateSource

/-- Source-shaped deterministic recovery input for the Ekera-Hastad RSA route.
The recovered short-DLP secret `d` determines the half-sum `d + 1`; a recovered
candidate factor is accepted only when it is a nontrivial natural-number root
of the source quadratic `q * (2(d+1)-q) = N`. The half-sum relation records the
source equation `2(d+1)=p+q` [EH17, source.tex:878-925]. -/
structure HalfSumQuadraticRecoveryInput {N : ℕ}
    (model : ShorFactoring.SemiprimeFactorModel N)
    (recoveredSecret candidate : ℕ) : Prop where
  half_sum_relation :
    2 * (recoveredSecret + 1) = model.leftFactor + model.rightFactor
  candidate_gt_one : 1 < candidate
  candidate_lt_modulus : candidate < N
  quadratic_product_eq :
    candidate * (2 * (recoveredSecret + 1) - candidate) = N

namespace HalfSumQuadraticRecoveryInput

/-- Assemble the half-sum quadratic recovery input from the EH17 half-sum
source data and the recovered quadratic-root candidate.  This constructor keeps
the factor route tied to the recovered root of the source quadratic, not to a
direct declared-factor shortcut [EH17, source.tex:915-925]. -/
theorem ofSourceRoot
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (halfSum : ShortDLPHalfSumSource inst model)
    {candidate : ℕ}
    (root : QuadraticRootCandidateSource model halfSum.halfSum candidate) :
    HalfSumQuadraticRecoveryInput model inst.secret candidate := by
  exact
    { half_sum_relation := halfSum.secret_succ_half_sum_relation
      candidate_gt_one :=
        root.candidate_gt_one halfSum.two_mul_halfSum_eq_factor_sum
      candidate_lt_modulus :=
        root.candidate_lt_modulus halfSum.two_mul_halfSum_eq_factor_sum
      quadratic_product_eq := by
        rw [← halfSum.halfSum_eq_secret_succ]
        exact root.quadratic_product_eq }

/-- The source quadratic relation makes the recovered candidate divide the RSA
modulus [EH17, source.tex:915-925]. -/
theorem candidate_dvd_modulus
    {N recoveredSecret candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (h : HalfSumQuadraticRecoveryInput model recoveredSecret candidate) :
    candidate ∣ N :=
  ⟨2 * (recoveredSecret + 1) - candidate, h.quadratic_product_eq.symm⟩

/-- Turn the recovered half-sum quadratic root into a factor-return
certificate. Unlike a trivial declared-factor wrapper, the output is the
candidate certified by the source quadratic relation [EH17,
source.tex:915-925]. -/
def factorReturnCertificate
    {N recoveredSecret candidate : ℕ}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (h : HalfSumQuadraticRecoveryInput model recoveredSecret candidate) :
    ShorFactoring.FactorReturnCertificate model :=
  ShorFactoring.FactorReturnCertificate.ofNontrivialDivisor model
    h.candidate_dvd_modulus h.candidate_gt_one h.candidate_lt_modulus

end HalfSumQuadraticRecoveryInput

/-- Source-level bridge from a recovered short-DLP secret to an RSA factor
certificate. The number-theoretic route proof is supplied as data here so the
resource adapter can consume the short-DLP post-processing result without
claiming that the resource theorem itself proves the Ekera-Hastad reduction
[EH17, source.tex:878-953]. -/
structure ShortDLPToFactorBridge
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    (inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params)
    (model : ShorFactoring.SemiprimeFactorModel N) where
  /-- Bridge from a recovered short-DLP secret to a factor-return certificate. -/
  factorOfRecoveredSecret :
    ∀ {d : ℕ}, d = inst.secret → ShorFactoring.FactorReturnCertificate model

/-- Source-shaped RSA route side conditions for the Ekera-Hastad short-DLP
factoring path. The route keeps the recovered candidate factor and the
half-sum quadratic recovery proof together, so the short-DLP post-processing
secret can feed the factor-return bridge without an unexplained external
certificate [EH17, source.tex:878-953]. -/
structure ShortDLPRSARouteSideConditions
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    (inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params)
    (model : ShorFactoring.SemiprimeFactorModel N) where
  /-- Candidate factor or secret produced by post-processing. -/
  candidate : ℕ
  recovery :
    HalfSumQuadraticRecoveryInput model inst.secret candidate

namespace ShortDLPRSARouteSideConditions

/-- Factor-return certificate obtained from the source half-sum quadratic
recovery data [EH17, source.tex:915-925]. -/
def factorReturnCertificate
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (route : ShortDLPRSARouteSideConditions inst model) :
    ShorFactoring.FactorReturnCertificate model :=
  route.recovery.factorReturnCertificate

/-- Convert source-shaped Ekera-Hastad RSA route side conditions into the
short-DLP-to-factor bridge consumed by the public factor-return certificate
[EH17, source.tex:878-953]. -/
def toShortDLPToFactorBridge
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (route : ShortDLPRSARouteSideConditions inst model) :
    ShortDLPToFactorBridge inst model where
  factorOfRecoveredSecret := by
    intro d hd
    cases hd
    exact route.factorReturnCertificate

end ShortDLPRSARouteSideConditions

namespace ShortDLPToFactorBridge

/-- Build the short-DLP-to-factor bridge directly from the EH17 half-sum source
data and the quadratic-root certificate. This avoids exposing the older
side-condition record at bridge call sites while still routing through the
recovered quadratic root, not through a declared-factor shortcut [EH17,
source.tex:908-925]. -/
def ofHalfSumRoot
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (halfSum : ShortDLPHalfSumSource inst model)
    {candidate : ℕ}
    (root : QuadraticRootCandidateSource model halfSum.halfSum candidate) :
    ShortDLPToFactorBridge inst model where
  factorOfRecoveredSecret := by
    intro d hd
    cases hd
    exact
      (HalfSumQuadraticRecoveryInput.ofSourceRoot halfSum root)
        |>.factorReturnCertificate

end ShortDLPToFactorBridge

/-- Ekera-Hastad route correctness certificate: a successful short-DLP
post-processing certificate, plus the RSA-specific bridge that turns its
recovered secret into one of the declared semiprime factors [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128]. -/
structure ShortDLPFactorReturnCertificate
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    (model : ShorFactoring.SemiprimeFactorModel N) where
  /-- Classical post-processing certificate for the short-DLP route. -/
  postprocessing :
    FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst
  /-- Bridge certificate connecting the short-DLP output to factor recovery. -/
  bridge : ShortDLPToFactorBridge inst model

namespace ShortDLPFactorReturnCertificate

/-- Assemble the Ekera-Hastad short-DLP factor-return certificate from the
source post-processing certificate and the RSA route side conditions. This is
the route constructor used to avoid taking `ShortDLPToFactorBridge` as an
unexplained external field [EH17, source.tex:878-953] [E23,
arxiv-v5.tex:162-164]. -/
def ofSourceRoute
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (route : ShortDLPRSARouteSideConditions inst model) :
    ShortDLPFactorReturnCertificate (inst := inst) model where
  postprocessing := postprocessing
  bridge := route.toShortDLPToFactorBridge

/-- Assemble the Ekera-Hastad short-DLP factor-return certificate directly
from the EH17 half-sum source data and quadratic-root certificate. Unlike
`ofSourceRoute`, this constructor does not expose `ShortDLPRSARouteSideConditions`
at the call site [EH17, source.tex:908-925] [E23, arxiv-v5.tex:162-164]. -/
def ofHalfSumRoot
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (halfSum : ShortDLPHalfSumSource inst model)
    {candidate : ℕ}
    (root : QuadraticRootCandidateSource model halfSum.halfSum candidate) :
    ShortDLPFactorReturnCertificate (inst := inst) model where
  postprocessing := postprocessing
  bridge := ShortDLPToFactorBridge.ofHalfSumRoot halfSum root

/-- Factor-return certificate obtained by applying the RSA bridge to the
post-processing output [EH17, source.tex:878-953]. -/
def factorReturn
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model) :
    ShorFactoring.FactorReturnCertificate model :=
  cert.bridge.factorOfRecoveredSecret cert.postprocessing.recovers_secret

/-- The Ekera-Hastad route output is one of the two declared semiprime factors. -/
theorem output_mem_declared_factors
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model) :
    (factorReturn (inst := inst) cert).output = model.leftFactor ∨
      (factorReturn (inst := inst) cert).output = model.rightFactor :=
  (factorReturn (inst := inst) cert).output_mem_declared_factors

/-- The route's post-processing success probability is bounded below by the
Ekera short-DLP source expression [E23, arxiv-v5.tex:1103-1128]. -/
theorem successProbability_ge_sourceLowerBound
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model) :
    params.successLowerBound ≤ cert.postprocessing.successProbability :=
  cert.postprocessing.successProbability_ge_sourceLowerBound

/-- The route's classical group-operation count is bounded by the Ekera
short-DLP source expression [E23, arxiv-v5.tex:1103-1128]. -/
theorem groupOperations_le_sourceBound
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model) :
    (cert.postprocessing.groupOperations : ℝ) ≤ params.groupOperationBound :=
  cert.postprocessing.groupOperations_le_sourceBound

/-- The route's lookup-table size is bounded by the Ekera short-DLP source
expression [E23, arxiv-v5.tex:1103-1128]. -/
theorem lookupTableSize_le_sourceBound
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model) :
    (cert.postprocessing.lookupTableSize : ℝ) ≤ params.lookupTableBound :=
  cert.postprocessing.lookupTableSize_le_sourceBound

/-- Classical upper-bound parameters obtained from a source-certified
short-DLP post-processing certificate. The group-operation count fills the
search-space slot, and the lookup-table size fills the table slot used by the
RSA public classical-count field [E23, arxiv-v5.tex:1103-1128]. -/
def classicalUpperBoundParameters
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model)
    (factorBits : ℕ) :
    ClassicalPostProcessingParameters.UpperBoundParameters where
  factorBits := factorBits
  searchSpaceBound := cert.postprocessing.groupOperations
  lookupTableBound := cert.postprocessing.lookupTableSize

@[simp] theorem classicalUpperBoundParameters_factorBits
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model)
    (factorBits : ℕ) :
    (classicalUpperBoundParameters cert factorBits).factorBits = factorBits :=
  rfl

@[simp] theorem classicalUpperBoundParameters_searchSpaceBound
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model)
    (factorBits : ℕ) :
    (classicalUpperBoundParameters cert factorBits).searchSpaceBound =
      cert.postprocessing.groupOperations :=
  rfl

@[simp] theorem classicalUpperBoundParameters_lookupTableBound
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model)
    (factorBits : ℕ) :
    (classicalUpperBoundParameters cert factorBits).lookupTableBound =
      cert.postprocessing.lookupTableSize :=
  rfl

/-- The RSA classical upper-bound parameters inherit the Ekerå source bounds
on group operations and lookup-table size [E23, arxiv-v5.tex:1103-1128]. -/
theorem classicalUpperBoundParameters_sourceBounds
    {N : ℕ} {G : Type*} [Group G]
    {params : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst : FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G params}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model)
    (factorBits : ℕ) :
    ((classicalUpperBoundParameters cert factorBits).searchSpaceBound : ℝ) ≤
        params.groupOperationBound ∧
      ((classicalUpperBoundParameters cert factorBits).lookupTableBound : ℝ) ≤
        params.lookupTableBound :=
  ⟨cert.postprocessing.groupOperations_le_sourceBound,
    cert.postprocessing.lookupTableSize_le_sourceBound⟩

/-- The public classical-count field is the success-accounted natural-number
function obtained from the source-certified group-operation and lookup-table
quantities [E23, arxiv-v5.tex:1103-1128]. -/
theorem publicClassicalOps_eq_sourceQuantities
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model)
    (runs : RunSuccessParameters)
    (formula : PublicBaselineBounds.FormulaParameters)
    (factorBits : ℕ) :
    (formula.toPublicBaselineBounds runs
        (classicalUpperBoundParameters cert factorBits)).classicalOps =
      runs.postProcessingRunCount *
        (5 * factorBits + cert.postprocessing.groupOperations +
          2 * cert.postprocessing.lookupTableSize + 13) := by
  simp [classicalUpperBoundParameters,
    PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds,
    ClassicalPostProcessingParameters.successAccountedUpperBoundTotal,
    ClassicalPostProcessingParameters.upperBoundTotal]

/-- Source-to-public binding for the RSA classical count: the parameters fed
to the public baseline field are exactly the certified Ekerå post-processing
group-operation and lookup-table quantities, together with their source bounds
[E23, arxiv-v5.tex:1103-1128]. -/
theorem publicClassicalOps_sourceBinding
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    (cert : ShortDLPFactorReturnCertificate (inst := inst) model)
    (runs : RunSuccessParameters)
    (formula : PublicBaselineBounds.FormulaParameters)
    (factorBits : ℕ) :
    ((classicalUpperBoundParameters cert factorBits).searchSpaceBound : ℝ) ≤
        shortParams.groupOperationBound ∧
      ((classicalUpperBoundParameters cert factorBits).lookupTableBound : ℝ) ≤
        shortParams.lookupTableBound ∧
      (formula.toPublicBaselineBounds runs
          (classicalUpperBoundParameters cert factorBits)).classicalOps =
        runs.postProcessingRunCount *
          (5 * factorBits + cert.postprocessing.groupOperations +
            2 * cert.postprocessing.lookupTableSize + 13) := by
  exact
    ⟨cert.postprocessing.groupOperations_le_sourceBound,
      cert.postprocessing.lookupTableSize_le_sourceBound,
      publicClassicalOps_eq_sourceQuantities cert runs formula factorBits⟩

end ShortDLPFactorReturnCertificate

/-! ## Public factor-return endpoint -/

/-- Public input carrier for the Ekera-Hastad RSA factorization theorem.  The
factor-size window is the Lean-side exact carrier for the statement's
`2^(n-1) < p,q < 2^n` premise, while the semiprime model records the public
modulus equation and the declared prime factors [EH17, source.tex:878-953]. -/
structure PublicInput (N n : ℕ) where
  /-- Declared semiprime model for the known public modulus. -/
  model : ShorFactoring.SemiprimeFactorModel N
  /-- Lower bit-window bound for the left prime factor. -/
  leftFactor_lower : 2 ^ (n - 1) < model.leftFactor
  /-- Upper bit-window bound for the left prime factor. -/
  leftFactor_upper : model.leftFactor < 2 ^ n
  /-- Lower bit-window bound for the right prime factor. -/
  rightFactor_lower : 2 ^ (n - 1) < model.rightFactor
  /-- Upper bit-window bound for the right prime factor. -/
  rightFactor_upper : model.rightFactor < 2 ^ n

namespace PublicInput

/-- The public factor-size window implies that the factor bit length is
positive. -/
theorem factorBits_pos {N n : ℕ} (input : PublicInput N n) : 0 < n := by
  by_contra hnot
  have hn : n = 0 := Nat.eq_zero_of_not_pos hnot
  have hlt : input.model.leftFactor < 1 := by
    simpa [hn] using input.leftFactor_upper
  exact (not_lt_of_ge (Nat.le_of_lt input.model.left_prime.one_lt)) hlt

/-- Formula parameters bound to the public RSA input.  The factor-bit field is
the public exponent `n` from the input window; the logarithmic field remains an
explicit public natural-number upper bound for the `log(2n)` source term
[EH17, source.tex:878-953] [GE19, main.tex:459-522]. -/
def formulaParameters (factorBits logDoubleFactorBitsUpperBound : ℕ) :
    PublicBaselineBounds.FormulaParameters where
  factorBits := factorBits
  logDoubleFactorBitsUpperBound := logDoubleFactorBitsUpperBound

@[simp] theorem formulaParameters_factorBits
    (factorBits logDoubleFactorBitsUpperBound : ℕ) :
    (formulaParameters factorBits logDoubleFactorBitsUpperBound).factorBits =
      factorBits :=
  rfl

@[simp] theorem formulaParameters_logDoubleFactorBitsUpperBound
    (factorBits logDoubleFactorBitsUpperBound : ℕ) :
    (formulaParameters factorBits logDoubleFactorBitsUpperBound).logDoubleFactorBitsUpperBound =
      logDoubleFactorBitsUpperBound :=
  rfl

/-- The formula-parameter factor-bit field inherits positivity from the public
RSA factor-size window. -/
private theorem formulaParameters_factorBits_pos {N n : ℕ}
    (input : PublicInput N n) (logDoubleFactorBitsUpperBound : ℕ) :
    0 < (formulaParameters n logDoubleFactorBitsUpperBound).factorBits := by
  simpa using input.factorBits_pos

/-- Public baseline bounds obtained from formula parameters bound to the public
RSA input, public run-success data, and public classical upper-bound data. -/
def publicBaselineBounds (factorBits logDoubleFactorBitsUpperBound : ℕ)
    (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    PublicBaselineBounds :=
  (formulaParameters factorBits logDoubleFactorBitsUpperBound).toPublicBaselineBounds
    runs classical

@[simp] theorem publicBaselineBounds_logicalQubits {N n : ℕ}
    (_input : PublicInput N n) (logDoubleFactorBitsUpperBound : ℕ)
    (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (publicBaselineBounds n logDoubleFactorBitsUpperBound runs classical).logicalQubits =
      (formulaParameters n logDoubleFactorBitsUpperBound).logicalQubitBound :=
  rfl

@[simp] theorem publicBaselineBounds_toffoliGates {N n : ℕ}
    (_input : PublicInput N n) (logDoubleFactorBitsUpperBound : ℕ)
    (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (publicBaselineBounds n logDoubleFactorBitsUpperBound runs classical).toffoliGates =
      runs.samplingMultiplier *
        (formulaParameters n logDoubleFactorBitsUpperBound).toffoliBaseBound :=
  rfl

@[simp] theorem publicBaselineBounds_circuitDepth {N n : ℕ}
    (_input : PublicInput N n) (logDoubleFactorBitsUpperBound : ℕ)
    (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (publicBaselineBounds n logDoubleFactorBitsUpperBound runs classical).circuitDepth =
      runs.samplingMultiplier *
        (formulaParameters n logDoubleFactorBitsUpperBound).circuitDepthBaseBound :=
  rfl

@[simp] theorem publicBaselineBounds_runRetryAccounting {N n : ℕ}
    (_input : PublicInput N n) (logDoubleFactorBitsUpperBound : ℕ)
    (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (publicBaselineBounds n logDoubleFactorBitsUpperBound runs classical).runRetryAccounting =
      runs.samplingMultiplier + runs.postProcessingRunCount :=
  rfl

@[simp] theorem publicBaselineBounds_classicalOps {N n : ℕ}
    (_input : PublicInput N n) (logDoubleFactorBitsUpperBound : ℕ)
    (runs : RunSuccessParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters) :
    (publicBaselineBounds n logDoubleFactorBitsUpperBound runs classical).classicalOps =
      ClassicalPostProcessingParameters.successAccountedUpperBoundTotal runs classical :=
  rfl

end PublicInput

/-- Public failure-budget carrier for the Ekera-Hastad RSA theorem shape.  The
retry and short-DLP success certificates are internal support objects; the
public endpoint receives only a well-formed target failure budget [E23,
arxiv-v5.tex:1103-1128]. -/
structure PublicFailureBudget (budget : FailureBudget) : Prop where
  wellFormed : budget.WellFormed

/-- Public-facing success and retry certificate for the Ekera-Hastad RSA route.
It stores explicit natural-number retry/run fields and the exact rational
success comparison to the public failure budget. The repetition model is
constructed internally from these fields rather than being exposed as a public
endpoint input [E23, arxiv-v5.tex:1103-1128]. -/
structure PublicSuccessCertificate (budget : FailureBudget) where
  /-- Explicit upper bound for repeated route attempts. -/
  retryRuns : ℕ
  /-- Number of quantum samples used in one route attempt. -/
  sampleRunsPerAttempt : ℕ
  /-- Number of classical post-processing passes used in one route attempt. -/
  postProcessingRunsPerAttempt : ℕ
  retryRuns_pos : 0 < retryRuns
  sampleRunsPerAttempt_pos : 0 < sampleRunsPerAttempt
  /-- Numerator of the certified retry failure probability. -/
  failureNumerator : ℕ
  /-- Denominator of the certified retry failure probability. -/
  failureDenominator : ℕ
  failureDenominator_pos : 0 < failureDenominator
  failure_le_budget :
    failureNumerator * budget.failureDenominator ≤
      budget.failureNumerator * failureDenominator
  /-- Numerator of the certified endpoint success probability. -/
  successNumerator : ℕ
  /-- Denominator of the certified endpoint success probability. -/
  successDenominator : ℕ
  successDenominator_pos : 0 < successDenominator
  successAtLeastOneMinusFailureBudget :
    (budget.failureDenominator - budget.failureNumerator) *
        successDenominator ≤
      budget.failureDenominator * successNumerator

namespace PublicSuccessCertificate

/-- Explicit run-success parameters represented by a public success
certificate. -/
def runs {budget : FailureBudget} (cert : PublicSuccessCertificate budget) :
    RunSuccessParameters :=
  RunSuccessParameters.ekeraHastadRSA budget cert.retryRuns
    cert.sampleRunsPerAttempt cert.postProcessingRunsPerAttempt

@[simp] theorem runs_samplingMultiplier {budget : FailureBudget}
    (cert : PublicSuccessCertificate budget) :
    cert.runs.samplingMultiplier =
      cert.retryRuns * cert.sampleRunsPerAttempt :=
  rfl

/-- Public success data implies that the sampling multiplier is positive; the
final public endpoint can use this instead of taking a private positivity proof
as an input [E23, arxiv-v5.tex:1103-1128]. -/
theorem runs_samplingMultiplier_pos {budget : FailureBudget}
    (cert : PublicSuccessCertificate budget) :
    0 < cert.runs.samplingMultiplier := by
  rw [runs_samplingMultiplier]
  exact Nat.mul_pos cert.retryRuns_pos cert.sampleRunsPerAttempt_pos

@[simp] theorem runs_postProcessingRunCount {budget : FailureBudget}
    (cert : PublicSuccessCertificate budget) :
    cert.runs.postProcessingRunCount =
      cert.retryRuns * cert.postProcessingRunsPerAttempt :=
  rfl

@[simp] theorem runs_ready {budget : FailureBudget}
    (cert : PublicSuccessCertificate budget) :
    cert.runs.readyForFinalStatement = true :=
  RunSuccessParameters.ekeraHastadRSA_ready budget cert.retryRuns
    cert.sampleRunsPerAttempt cert.postProcessingRunsPerAttempt

/-- The public success certificate internally builds the source-named
Ekera-Hastad repetition model. Endpoint theorem statements should consume the
certificate, not this repetition model directly [E23, arxiv-v5.tex:1103-1128]. -/
def repetitionModel {budget : FailureBudget}
    (cert : PublicSuccessCertificate budget) :
    RetryMultiplierSpec.RepetitionModel cert.runs.retry :=
  RetryMultiplierSpec.RepetitionModel.ekeraHastadShortDLP budget
    cert.failureDenominator_pos cert.failure_le_budget cert.retryRuns_pos

/-- Projection of the exact eta-parametric success comparison represented by
the public success certificate. -/
private theorem success_ge_one_minus_failureBudget {budget : FailureBudget}
    (cert : PublicSuccessCertificate budget) :
    (budget.failureDenominator - budget.failureNumerator) *
        cert.successDenominator ≤
      budget.failureDenominator * cert.successNumerator :=
  cert.successAtLeastOneMinusFailureBudget

end PublicSuccessCertificate

/-- Public-facing resource certificate for the Ekera-Hastad endpoint. It
contains only the concrete resource profile, run/retry accounting, and public
fieldwise upper bounds; private exact-resource witnesses and route certificates
are intentionally absent [E23, arxiv-v5.tex:1103-1128] [GE19,
main.tex:459-522]. -/
structure PublicResourceCertificate
    (runs : RunSuccessParameters) (bounds : PublicBaselineBounds) where
  /-- Resource profile represented by the public endpoint. -/
  profile : ModularArithmeticResourceProfile
  /-- Explicit run/retry accounting count represented by the public endpoint. -/
  runRetryAccounting : ℕ
  /-- Logical-qubit field is bounded by the public baseline. -/
  logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits
  /-- Toffoli field is bounded by the public baseline. -/
  toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates
  /-- Circuit-depth field is bounded by the public baseline. -/
  circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth
  /-- Run/retry accounting field is bounded by the public baseline. -/
  runRetryAccounting_le : runRetryAccounting ≤ bounds.runRetryAccounting
  /-- Classical-operation field is bounded by the public baseline. -/
  classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps

/-- Public endpoint witness for the Ekera-Hastad RSA factorization theorem.
It contains only public-facing output, success, and resource-bound fields. The
short-DLP post-processing certificate, RSA route side conditions, repetition
model, and private exact-resource witness are intentionally absent from this
type; source-route constructors must build this witness internally [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128] [GE19,
main.tex:459-522]. -/
structure PublicEndpointWitness {N n : ℕ} (input : PublicInput N n)
    (budget : FailureBudget) (bounds : PublicBaselineBounds) where
  /-- Returned factor candidate. -/
  output : ℕ
  /-- Resource profile for the represented algorithm. -/
  profile : ModularArithmeticResourceProfile
  /-- Explicit run/retry accounting count exposed to the public bounds. -/
  runRetryAccounting : ℕ
  /-- The returned factor is one of the two declared semiprime factors. -/
  output_mem_declared_factors :
    output = input.model.leftFactor ∨ output = input.model.rightFactor
  /-- Numerator of the certified success-probability lower bound. -/
  successNumerator : ℕ
  /-- Denominator of the certified success-probability lower bound. -/
  successDenominator : ℕ
  successDenominator_pos : 0 < successDenominator
  /-- Eta-parametric success lower bound in exact rational form. -/
  successAtLeastOneMinusFailureBudget :
    (budget.failureDenominator - budget.failureNumerator) *
        successDenominator ≤
      budget.failureDenominator * successNumerator
  /-- Logical-qubit field is bounded by the public baseline. -/
  logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits
  /-- Toffoli field is bounded by the public baseline. -/
  toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates
  /-- Circuit-depth field is bounded by the public baseline. -/
  circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth
  /-- Run/retry accounting field is bounded by the public baseline. -/
  runRetryAccounting_le : runRetryAccounting ≤ bounds.runRetryAccounting
  /-- Classical-operation field is bounded by the public baseline. -/
  classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps

namespace PublicEndpointWitness

/-- Public consequence predicate for the Ekera-Hastad RSA factorization
endpoint.  This is the statement-shape carrier consumed by the final endpoint:
factor membership, eta-parametric success, and public resource bounds, without
exposing short-DLP source-route certificates as public inputs [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128] [GE19,
main.tex:459-522]. -/
def Statement {N n : ℕ} {input : PublicInput N n}
    {budget : FailureBudget} {bounds : PublicBaselineBounds}
    (witness : PublicEndpointWitness input budget bounds) : Prop :=
  (witness.output = input.model.leftFactor ∨
      witness.output = input.model.rightFactor) ∧
    (budget.failureDenominator - budget.failureNumerator) *
        witness.successDenominator ≤
      budget.failureDenominator * witness.successNumerator ∧
    witness.profile.logicalQubits ≤ bounds.logicalQubits ∧
    witness.profile.toffoliGates ≤ bounds.toffoliGates ∧
    witness.profile.circuitDepth ≤ bounds.circuitDepth ∧
    witness.runRetryAccounting ≤ bounds.runRetryAccounting ∧
    witness.profile.toResourceProfile.classicalOps ≤ bounds.classicalOps

/-- A public endpoint witness discharges the public consequence predicate. -/
theorem statement {N n : ℕ} {input : PublicInput N n}
    {budget : FailureBudget} {bounds : PublicBaselineBounds}
    (witness : PublicEndpointWitness input budget bounds) :
    Statement witness :=
  ⟨witness.output_mem_declared_factors,
    witness.successAtLeastOneMinusFailureBudget,
    witness.logicalQubits_le,
    witness.toffoliGates_le,
    witness.circuitDepth_le,
    witness.runRetryAccounting_le,
    witness.classicalOps_le⟩

/-- Build a public endpoint witness from a public factor-return certificate and
separately supplied public success/resource fields. This bridge is deliberately
agnostic about how the factor-return certificate was obtained, so later
source-route constructors can consume EH17/E23 support internally without
exposing route certificates as public endpoint inputs [EH17,
source.tex:878-953]. -/
def ofFactorReturnCertificate {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (factorReturn : ShorFactoring.FactorReturnCertificate input.model)
    (profile : ModularArithmeticResourceProfile)
    (runRetryAccounting successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (successAtLeastOneMinusFailureBudget :
      (budget.failureDenominator - budget.failureNumerator) *
          successDenominator ≤
        budget.failureDenominator * successNumerator)
    (logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits)
    (toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates)
    (circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth)
    (runRetryAccounting_le : runRetryAccounting ≤ bounds.runRetryAccounting)
    (classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps) :
    PublicEndpointWitness input budget bounds where
  output := factorReturn.output
  profile := profile
  runRetryAccounting := runRetryAccounting
  output_mem_declared_factors := factorReturn.output_mem_declared_factors
  successNumerator := successNumerator
  successDenominator := successDenominator
  successDenominator_pos := successDenominator_pos
  successAtLeastOneMinusFailureBudget := successAtLeastOneMinusFailureBudget
  logicalQubits_le := logicalQubits_le
  toffoliGates_le := toffoliGates_le
  circuitDepth_le := circuitDepth_le
  runRetryAccounting_le := runRetryAccounting_le
  classicalOps_le := classicalOps_le

/-- Build a public endpoint witness from a factor-return certificate and a
public success/retry certificate. Resource fields remain explicit so the
resource-bound bridge can be discharged separately [EH17, source.tex:878-953]
[E23, arxiv-v5.tex:1103-1128]. -/
def ofFactorReturnCertificateAndSuccess {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (factorReturn : ShorFactoring.FactorReturnCertificate input.model)
    (success : PublicSuccessCertificate budget)
    (profile : ModularArithmeticResourceProfile)
    (logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits)
    (toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates)
    (circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth)
    (runRetryAccounting_le :
      success.runs.samplingMultiplier + success.runs.postProcessingRunCount ≤
        bounds.runRetryAccounting)
    (classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps) :
    PublicEndpointWitness input budget bounds :=
  ofFactorReturnCertificate input budget bounds factorReturn profile
    (success.runs.samplingMultiplier + success.runs.postProcessingRunCount)
    success.successNumerator success.successDenominator
    success.successDenominator_pos success.successAtLeastOneMinusFailureBudget
    logicalQubits_le toffoliGates_le circuitDepth_le runRetryAccounting_le
    classicalOps_le

/-- Build a public endpoint witness from a factor-return certificate, a public
success/retry certificate, and a public resource certificate. This is the
theorem-node-facing resource path: no private exact-resource witness, route
source-bound certificate, or route resource certificate is exposed [E23,
arxiv-v5.tex:1103-1128] [GE19, main.tex:459-522]. -/
def ofFactorReturnSuccessAndPublicResources {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (factorReturn : ShorFactoring.FactorReturnCertificate input.model)
    (success : PublicSuccessCertificate budget)
    (resources : PublicResourceCertificate success.runs bounds) :
    PublicEndpointWitness input budget bounds :=
  ofFactorReturnCertificate input budget bounds factorReturn resources.profile
    resources.runRetryAccounting success.successNumerator success.successDenominator
    success.successDenominator_pos success.successAtLeastOneMinusFailureBudget
    resources.logicalQubits_le resources.toffoliGates_le resources.circuitDepth_le
    resources.runRetryAccounting_le resources.classicalOps_le

/-- Build the public endpoint witness from public carriers only: a returned
candidate, its membership in the declared semiprime factors, a public success
certificate, and a public resource certificate. This constructor is the clean
boundary for the public theorem wrapper; source-route certificates are not
inputs [EH17, source.tex:878-953] [E23, arxiv-v5.tex:1103-1128] [GE19,
main.tex:459-522]. -/
def ofPublicCarriers {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (output : ℕ)
    (output_mem_declared_factors :
      output = input.model.leftFactor ∨ output = input.model.rightFactor)
    (success : PublicSuccessCertificate budget)
    (resources : PublicResourceCertificate success.runs bounds) :
    PublicEndpointWitness input budget bounds where
  output := output
  profile := resources.profile
  runRetryAccounting := resources.runRetryAccounting
  output_mem_declared_factors := output_mem_declared_factors
  successNumerator := success.successNumerator
  successDenominator := success.successDenominator
  successDenominator_pos := success.successDenominator_pos
  successAtLeastOneMinusFailureBudget :=
    success.successAtLeastOneMinusFailureBudget
  logicalQubits_le := resources.logicalQubits_le
  toffoliGates_le := resources.toffoliGates_le
  circuitDepth_le := resources.circuitDepth_le
  runRetryAccounting_le := resources.runRetryAccounting_le
  classicalOps_le := resources.classicalOps_le

/-- Build a public endpoint witness from a factor-return certificate, public
success/retry certificate, and componentwise route-resource certificate. The
private exact-resource witness is not an input: the public baseline support is
derived internally from the route certificate and explicit formula bounds
[EH17, source.tex:878-953] [GE19, main.tex:459-522]. -/
def ofFactorReturnSuccessAndRouteCertificate {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (factorReturn : ShorFactoring.FactorReturnCertificate input.model)
    (success : PublicSuccessCertificate budget)
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {route : RouteParameters}
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters)
    {routeBounds : RouteParameters.PublicBaselineBounds}
    (params : PublicBaselineBounds.FormulaParameters)
    (readiness : FinalResourceReadiness quantumStatus success.runs)
    (hpos : 0 < success.runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input budget
      (params.toPublicBaselineBounds success.runs classical) := by
  let profile := exactSupportProfile success.runs route classical
  let bounds := params.toPublicBaselineBounds success.runs classical
  have hsupport :
      SupportsPublicBaseline profile success.runs bounds :=
    exactSupportProfile_supportsPublicBaseline_ekeraHastadRSA readiness hpos
      hroute hlogical htoffoli hdepth
  exact
    ofFactorReturnCertificateAndSuccess input budget bounds factorReturn success
      profile hsupport.logicalQubits_le hsupport.toffoliGates_le
      hsupport.circuitDepth_le hsupport.runRetryAccounting_le
      hsupport.classicalOps_le

/-- Source-route support constructor for the public endpoint witness. It uses
the EH17 short-DLP-to-RSA bridge only to obtain the ordinary factor-return
certificate, then immediately projects to the public witness shape. Success
and resource fields remain explicit inputs for the later retry/resource bridge
issues [EH17, source.tex:878-953] [E23, arxiv-v5.tex:162-164]. -/
def ofSourceRouteFactorReturnAndBounds {N n : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (rsaRoute : ShortDLPRSARouteSideConditions inst input.model)
    (profile : ModularArithmeticResourceProfile)
    (runRetryAccounting successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (successAtLeastOneMinusFailureBudget :
      (budget.failureDenominator - budget.failureNumerator) *
          successDenominator ≤
        budget.failureDenominator * successNumerator)
    (logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits)
    (toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates)
    (circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth)
    (runRetryAccounting_le : runRetryAccounting ≤ bounds.runRetryAccounting)
    (classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps) :
    PublicEndpointWitness input budget bounds :=
  ofFactorReturnCertificate input budget bounds
    (ShortDLPFactorReturnCertificate.factorReturn
      (ShortDLPFactorReturnCertificate.ofSourceRoute postprocessing rsaRoute))
    profile runRetryAccounting successNumerator successDenominator
    successDenominator_pos successAtLeastOneMinusFailureBudget logicalQubits_le
    toffoliGates_le circuitDepth_le runRetryAccounting_le classicalOps_le

/-- Direct EH17 half-sum/quadratic-root support constructor for the public
endpoint witness. It has the same public fields as
`ofSourceRouteFactorReturnAndBounds`, but obtains the factor-return certificate
without taking `ShortDLPRSARouteSideConditions` as an input [EH17,
source.tex:908-925] [E23, arxiv-v5.tex:162-164]. -/
def ofHalfSumRootFactorReturnAndBounds {N n : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (halfSum : ShortDLPHalfSumSource inst input.model)
    {candidate : ℕ}
    (root : QuadraticRootCandidateSource input.model halfSum.halfSum candidate)
    (profile : ModularArithmeticResourceProfile)
    (runRetryAccounting successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (successAtLeastOneMinusFailureBudget :
      (budget.failureDenominator - budget.failureNumerator) *
          successDenominator ≤
        budget.failureDenominator * successNumerator)
    (logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits)
    (toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates)
    (circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth)
    (runRetryAccounting_le : runRetryAccounting ≤ bounds.runRetryAccounting)
    (classicalOps_le : profile.toResourceProfile.classicalOps ≤ bounds.classicalOps) :
    PublicEndpointWitness input budget bounds :=
  ofFactorReturnCertificate input budget bounds
    (ShortDLPFactorReturnCertificate.factorReturn
      (ShortDLPFactorReturnCertificate.ofHalfSumRoot postprocessing halfSum root))
    profile runRetryAccounting successNumerator successDenominator
    successDenominator_pos successAtLeastOneMinusFailureBudget logicalQubits_le
    toffoliGates_le circuitDepth_le runRetryAccounting_le classicalOps_le

/-- Direct EH17 half-sum/quadratic-root support constructor using only public
success and public resource certificates at the endpoint boundary. This is the
public-facing resource path for the later theorem-node assembly [EH17,
source.tex:908-925] [E23, arxiv-v5.tex:1103-1128] [GE19, main.tex:459-522]. -/
def ofHalfSumRootSuccessAndPublicResources
    {N n : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (halfSum : ShortDLPHalfSumSource inst input.model)
    {candidate : ℕ}
    (root : QuadraticRootCandidateSource input.model halfSum.halfSum candidate)
    (success : PublicSuccessCertificate budget)
    (resources : PublicResourceCertificate success.runs bounds) :
    PublicEndpointWitness input budget bounds :=
  ofFactorReturnSuccessAndPublicResources input budget bounds
    (ShortDLPFactorReturnCertificate.factorReturn
      (ShortDLPFactorReturnCertificate.ofHalfSumRoot postprocessing halfSum root))
    success resources

/-- Source-route and route-resource support constructor for the public endpoint
witness.  The source route supplies only the internal factor-return certificate;
the success and public resource fields are provided by explicit public-support
certificates before projecting to the public witness shape [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128] [GE19, main.tex:459-522]. -/
def ofSourceRouteSuccessAndRouteCertificate
    {N n : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    (input : PublicInput N n) (budget : FailureBudget)
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (rsaRoute : ShortDLPRSARouteSideConditions inst input.model)
    (success : PublicSuccessCertificate budget)
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {route : RouteParameters}
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters)
    {routeBounds : RouteParameters.PublicBaselineBounds}
    (params : PublicBaselineBounds.FormulaParameters)
    (readiness : FinalResourceReadiness quantumStatus success.runs)
    (hpos : 0 < success.runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input budget
      (params.toPublicBaselineBounds success.runs classical) :=
  ofFactorReturnSuccessAndRouteCertificate input budget
    (ShortDLPFactorReturnCertificate.factorReturn
      (ShortDLPFactorReturnCertificate.ofSourceRoute postprocessing rsaRoute))
    success classical params readiness hpos hroute hlogical htoffoli hdepth

/-- Direct EH17 half-sum/quadratic-root and route-resource support constructor
for the public endpoint witness. This variant keeps the factor-return bridge
free of `ShortDLPRSARouteSideConditions`; resource and success fields are still
handled by their explicit public-support certificates [EH17,
source.tex:908-925] [E23, arxiv-v5.tex:1103-1128] [GE19, main.tex:459-522]. -/
def ofHalfSumRootSuccessAndRouteCertificate
    {N n : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    (input : PublicInput N n) (budget : FailureBudget)
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (halfSum : ShortDLPHalfSumSource inst input.model)
    {candidate : ℕ}
    (root : QuadraticRootCandidateSource input.model halfSum.halfSum candidate)
    (success : PublicSuccessCertificate budget)
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {route : RouteParameters}
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters)
    {routeBounds : RouteParameters.PublicBaselineBounds}
    (params : PublicBaselineBounds.FormulaParameters)
    (readiness : FinalResourceReadiness quantumStatus success.runs)
    (hpos : 0 < success.runs.samplingMultiplier)
    (hroute : RouteParameters.SourceBoundCertificate route routeBounds)
    (hlogical : routeBounds.toProfile.logicalQubits ≤ params.logicalQubitBound)
    (htoffoli : routeBounds.toProfile.toffoliGates ≤ params.toffoliBaseBound)
    (hdepth : routeBounds.toProfile.circuitDepth ≤ params.circuitDepthBaseBound) :
    PublicEndpointWitness input budget
      (params.toPublicBaselineBounds success.runs classical) :=
  ofFactorReturnSuccessAndRouteCertificate input budget
    (ShortDLPFactorReturnCertificate.factorReturn
      (ShortDLPFactorReturnCertificate.ofHalfSumRoot postprocessing halfSum root))
    success classical params readiness hpos hroute hlogical htoffoli hdepth

end PublicEndpointWitness

/-- Public theorem-shape predicate for the Ekera-Hastad RSA endpoint.  The
endpoint-facing assumptions are public RSA input, a public failure budget, and
public resource bounds; all route certificates are internal to later bridge
constructors. -/
@[nolint unusedArguments]
def PublicTheoremShape {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds) :
    Prop :=
  ∃ witness : PublicEndpointWitness input budget bounds,
    PublicEndpointWitness.Statement witness

namespace PublicTheoremShape

/-- Final public theorem wrapper for the Ekera-Hastad endpoint. The boundary
contains only public RSA input, public failure budget, public bounds, the
returned factor candidate with its declared-factor membership certificate,
public success data, and public resource data. Source-route certificates and
private support records are not inputs to this theorem [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128] [GE19, main.tex:459-522]. -/
theorem ofPublicCarriers
    {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (output : ℕ)
    (output_mem_declared_factors :
      output = input.model.leftFactor ∨ output = input.model.rightFactor)
    (success : PublicSuccessCertificate budget)
    (resources : PublicResourceCertificate success.runs bounds) :
    PublicTheoremShape input budget bounds := by
  refine ⟨?_, ?_⟩
  · exact
      PublicEndpointWitness.ofPublicCarriers input budget bounds output
        output_mem_declared_factors success resources
  · exact PublicEndpointWitness.statement _

/-- Final public theorem wrapper from raw public endpoint fields.  The boundary
contains public RSA input, public failure budget, public resource bounds, a
returned factor candidate, exact rational success data, and fieldwise resource
upper bounds.  It does not expose EH17/E23 source-route objects,
post-processing records, or internal resource packages as theorem inputs [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128] [GE19, main.tex:459-522]. -/
theorem main
    {N n : ℕ}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (output : ℕ)
    (output_mem_declared_factors :
      output = input.model.leftFactor ∨ output = input.model.rightFactor)
    (profile : ModularArithmeticResourceProfile)
    (runRetryAccounting successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (successAtLeastOneMinusFailureBudget :
      (budget.failureDenominator - budget.failureNumerator) *
          successDenominator ≤
        budget.failureDenominator * successNumerator)
    (logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits)
    (toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates)
    (circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth)
    (runRetryAccounting_le : runRetryAccounting ≤ bounds.runRetryAccounting)
    (classicalOps_le : profile.toResourceProfile.classicalOps ≤
      bounds.classicalOps) :
    PublicTheoremShape input budget bounds := by
  refine ⟨?_, ?_⟩
  · exact
      { output := output
        profile := profile
        runRetryAccounting := runRetryAccounting
        output_mem_declared_factors := output_mem_declared_factors
        successNumerator := successNumerator
        successDenominator := successDenominator
        successDenominator_pos := successDenominator_pos
        successAtLeastOneMinusFailureBudget :=
          successAtLeastOneMinusFailureBudget
        logicalQubits_le := logicalQubits_le
        toffoliGates_le := toffoliGates_le
        circuitDepth_le := circuitDepth_le
        runRetryAccounting_le := runRetryAccounting_le
        classicalOps_le := classicalOps_le }
  · exact PublicEndpointWitness.statement _

/-- Source-route support wrapper for the Ekera-Hastad public theorem shape.
This remains useful for internal route assembly, but it is not the final public
theorem boundary because it consumes EH17/E23 source-route certificates
[EH17, source.tex:878-953] [E23, arxiv-v5.tex:1103-1128] [GE19,
main.tex:459-522]. -/
theorem ofHalfSumRootSuccessAndPublicResources
    {N n : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    (input : PublicInput N n) (budget : FailureBudget)
    (bounds : PublicBaselineBounds)
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (halfSum : ShortDLPHalfSumSource inst input.model)
    {candidate : ℕ}
    (root : QuadraticRootCandidateSource input.model halfSum.halfSum candidate)
    (success : PublicSuccessCertificate budget)
    (resources : PublicResourceCertificate success.runs bounds) :
    PublicTheoremShape input budget bounds := by
  refine ⟨?_, ?_⟩
  · exact
      PublicEndpointWitness.ofHalfSumRootSuccessAndPublicResources input budget
        bounds postprocessing halfSum root success resources
  · exact PublicEndpointWitness.statement _

end PublicTheoremShape

/-- Public Ekera-Hastad RSA factor-recovery certificate. It combines the
short-DLP-to-factor bridge, the source-certified retry/failure model, and the
exact-resource support witness for the public baseline fields [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128]. -/
structure PublicFactorizationCertificate
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    (model : ShorFactoring.SemiprimeFactorModel N)
    (quantumStatus : RouteParameters.QuantumResourceStatus)
    (runs : RunSuccessParameters) (route : RouteParameters)
    (classical : ClassicalPostProcessingParameters.UpperBoundParameters)
    (params : PublicBaselineBounds.FormulaParameters) where
  /-- Factor-return certificate supplied to the public endpoint. -/
  factorReturn : ShortDLPFactorReturnCertificate (inst := inst) model
  /-- Repetition model or certificate used for success amplification. -/
  repetition : RetryMultiplierSpec.RepetitionModel runs.retry
  resources : PrivateResourceStatementWitness quantumStatus runs route classical params

namespace PublicFactorizationCertificate

/-- Public consequence predicate for the Ekera-Hastad RSA factor-recovery
certificate. It packages the factor-return event, short-DLP post-processing
success and classical-work bounds, retry/failure accounting, final-statement
readiness, and public resource-baseline support in one theorem-node-facing
proposition [EH17, source.tex:878-953] [E23, arxiv-v5.tex:1103-1128]. -/
def Statement
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (cert :
      PublicFactorizationCertificate (inst := inst) model quantumStatus runs route
        classical params) : Prop :=
  ((cert.factorReturn.factorReturn).output = model.leftFactor ∨
      (cert.factorReturn.factorReturn).output = model.rightFactor) ∧
    shortParams.successLowerBound ≤
      cert.factorReturn.postprocessing.successProbability ∧
    (cert.factorReturn.postprocessing.groupOperations : ℝ) ≤
      shortParams.groupOperationBound ∧
    (cert.factorReturn.postprocessing.lookupTableSize : ℝ) ≤
      shortParams.lookupTableBound ∧
    cert.repetition.failureNumerator *
        runs.retry.failureBudget.failureDenominator ≤
      runs.retry.failureBudget.failureNumerator *
        cert.repetition.failureDenominator ∧
    quantumStatus.readyForFinalStatement = true ∧
    runs.readyForFinalStatement = true ∧
    SupportsPublicBaseline
      (exactSupportProfile runs route classical)
      runs
      (params.toPublicBaselineBounds runs classical)

/-- Assemble the public Ekera-Hastad factorization certificate from the
source short-DLP post-processing certificate, RSA route side conditions,
retry/failure model, and exact-resource witness. This prevents the public
endpoint from depending on an unexplained external short-DLP-to-factor bridge
[EH17, source.tex:878-953] [E23, arxiv-v5.tex:162-164]. -/
def ofSourceRoute
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (rsaRoute : ShortDLPRSARouteSideConditions inst model)
    (repetition : RetryMultiplierSpec.RepetitionModel runs.retry)
    (resources :
      PrivateResourceStatementWitness quantumStatus runs route classical params) :
    PublicFactorizationCertificate (inst := inst) model quantumStatus runs route
      classical params where
  factorReturn :=
    ShortDLPFactorReturnCertificate.ofSourceRoute postprocessing rsaRoute
  repetition := repetition
  resources := resources

end PublicFactorizationCertificate

/-- Public endpoint for the Ekera-Hastad RSA factor-recovery statement. The
source route supplies the short-DLP post-processing bridge and retry/failure
certificate; the exact-resource support witness then projects to the public
natural-number baseline fields without asymptotic metrics [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128]. -/
theorem main_factorization
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (cert :
      PublicFactorizationCertificate (inst := inst) model quantumStatus runs route
        classical params) :
    ((cert.factorReturn.factorReturn).output = model.leftFactor ∨
        (cert.factorReturn.factorReturn).output = model.rightFactor) ∧
      shortParams.successLowerBound ≤
        cert.factorReturn.postprocessing.successProbability ∧
      (cert.factorReturn.postprocessing.groupOperations : ℝ) ≤
        shortParams.groupOperationBound ∧
      (cert.factorReturn.postprocessing.lookupTableSize : ℝ) ≤
        shortParams.lookupTableBound ∧
      cert.repetition.failureNumerator *
          runs.retry.failureBudget.failureDenominator ≤
        runs.retry.failureBudget.failureNumerator *
          cert.repetition.failureDenominator ∧
      quantumStatus.readyForFinalStatement = true ∧
      runs.readyForFinalStatement = true ∧
      SupportsPublicBaseline
        (exactSupportProfile runs route classical)
        runs
        (params.toPublicBaselineBounds runs classical) :=
  ⟨cert.factorReturn.output_mem_declared_factors,
    cert.factorReturn.successProbability_ge_sourceLowerBound,
    cert.factorReturn.groupOperations_le_sourceBound,
    cert.factorReturn.lookupTableSize_le_sourceBound,
    cert.repetition.satisfies_failureBudget,
    cert.resources.readiness.quantumReady,
    cert.resources.readiness.runsReady,
    cert.resources.supportsPublicBaseline⟩

/-- The expanded public endpoint proves the packaged public consequence
predicate used by the existential theorem-node wrapper [EH17,
source.tex:878-953] [E23, arxiv-v5.tex:1103-1128]. -/
theorem main_factorization_statement
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (cert :
      PublicFactorizationCertificate (inst := inst) model quantumStatus runs route
        classical params) :
    PublicFactorizationCertificate.Statement cert := by
  simpa [PublicFactorizationCertificate.Statement] using main_factorization cert

/-- Source-route projection into the Ekera-Hastad factorization consequence.
This support theorem still consumes the source post-processing certificate, RSA
route side conditions, retry/failure model, and exact-resource witness; it is
not the public theorem-node endpoint [EH17, source.tex:878-953] [E23,
arxiv-v5.tex:162-164, 1103-1128]. -/
theorem sourceRoute_factorization_statement
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (rsaRoute : ShortDLPRSARouteSideConditions inst model)
    (repetition : RetryMultiplierSpec.RepetitionModel runs.retry)
    (resources :
      PrivateResourceStatementWitness quantumStatus runs route classical params) :
    let cert :=
      PublicFactorizationCertificate.ofSourceRoute postprocessing rsaRoute
        repetition resources
    ((cert.factorReturn.factorReturn).output = model.leftFactor ∨
        (cert.factorReturn.factorReturn).output = model.rightFactor) ∧
      shortParams.successLowerBound ≤
        cert.factorReturn.postprocessing.successProbability ∧
      (cert.factorReturn.postprocessing.groupOperations : ℝ) ≤
        shortParams.groupOperationBound ∧
      (cert.factorReturn.postprocessing.lookupTableSize : ℝ) ≤
        shortParams.lookupTableBound ∧
      cert.repetition.failureNumerator *
          runs.retry.failureBudget.failureDenominator ≤
        runs.retry.failureBudget.failureNumerator *
          cert.repetition.failureDenominator ∧
      quantumStatus.readyForFinalStatement = true ∧
      runs.readyForFinalStatement = true ∧
      SupportsPublicBaseline
        (exactSupportProfile runs route classical)
        runs
        (params.toPublicBaselineBounds runs classical) :=
  main_factorization
    (PublicFactorizationCertificate.ofSourceRoute postprocessing rsaRoute
      repetition resources)

/-- Existential source-route bridge for the Ekera-Hastad route. The theorem
constructs a public factorization certificate from short-DLP post-processing,
RSA route side conditions, repetition, and exact-resource support pieces, then
exposes the packaged consequence predicate. It remains a support bridge because
it consumes source-route witnesses [EH17, source.tex:878-953] [E23,
arxiv-v5.tex:162-164, 1103-1128]. -/
theorem sourceRoute_factorization_exists_statement
    {N : ℕ} {G : Type*} [Group G]
    {shortParams : FiniteCyclicDLP.ShortDLPPostprocessing.Parameters}
    {inst :
      FiniteCyclicDLP.ShortDLPPostprocessing.SourceInstance G shortParams}
    {model : ShorFactoring.SemiprimeFactorModel N}
    {quantumStatus : RouteParameters.QuantumResourceStatus}
    {runs : RunSuccessParameters} {route : RouteParameters}
    {classical : ClassicalPostProcessingParameters.UpperBoundParameters}
    {params : PublicBaselineBounds.FormulaParameters}
    (postprocessing :
      FiniteCyclicDLP.ShortDLPPostprocessing.PostProcessingCertificate inst)
    (rsaRoute : ShortDLPRSARouteSideConditions inst model)
    (repetition : RetryMultiplierSpec.RepetitionModel runs.retry)
    (resources :
      PrivateResourceStatementWitness quantumStatus runs route classical params) :
    ∃ cert :
      PublicFactorizationCertificate (inst := inst) model quantumStatus runs route
        classical params,
      PublicFactorizationCertificate.Statement cert := by
  let cert :=
    PublicFactorizationCertificate.ofSourceRoute postprocessing rsaRoute
      repetition resources
  exact ⟨cert, main_factorization_statement cert⟩

end EkeraHastadStyle
end Factoring
end QuantumAlg
