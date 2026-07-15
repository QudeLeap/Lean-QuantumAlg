/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularMultiplication

/-!
# Reversible modular exponentiation

The selected oracle shape is the multiplicative-accumulator convention:
`|x,y> ↦ |x, y * a^x mod N>`.  The exponent register is a finite binary range
`Fin (2^m)`, and the target register is a residue modulo `N`.

The exponentiation circuit interface follows the elementary square-and-multiply
route of controlled powers and modular multiplications [VBE95,
9511018.tex:372-401]. Gidney--Ekerå are cited for the RSA resource envelope that
uses this modular-exponentiation vocabulary [GE19, main.tex:425-522].
Beauregard's Fourier-space construction is recorded as a compact source route
but is not promoted to an exact-count theorem until its approximate-QFT policy
is resolved [Bea02, arxivfact.tex:167-207].
-/

@[expose] public section

namespace QuantumAlg
namespace ModularExponentiation

/-! ### Source route and QFT policy -/

/-- Construction route selected for modular exponentiation. -/
inductive ConstructionRoute where
  /-- Elementary reversible arithmetic networks. -/
  | vedralBarencoEkertNetworks
  /-- Compact Fourier-space arithmetic construction. -/
  | beauregardFourierSpace
deriving DecidableEq

/-- Policy for QFT usage in a modular-exponentiation construction. -/
inductive QFTPolicy where
  /-- Use exact QFT blocks already represented by exact resource profiles. -/
  | exactQFT
  /-- Approximate QFT formulas remain placeholders until exact bounds are supplied. -/
  | approximateQFTPlaceholder
deriving DecidableEq

/-- Source-policy record for modular exponentiation. -/
structure ConstructionPolicy where
  /-- Route component of this record. -/
  route : ConstructionRoute
  /-- Qft policy component of this record. -/
  qftPolicy : QFTPolicy
  /-- Resource status component of this record. -/
  resourceStatus : ResourceFormulaStatus
deriving DecidableEq

namespace ConstructionPolicy

/-- Whether this policy can directly instantiate exact resource fields. -/
def canInstantiateExactResources (policy : ConstructionPolicy) : Bool :=
  policy.resourceStatus.admissibleAsExactResource &&
    (policy.qftPolicy == QFTPolicy.exactQFT)

/-- Conservative source policy for the elementary-network route: construction
semantics are usable, while exact counts must be supplied separately. -/
def elementaryNetworkPlaceholder : ConstructionPolicy where
  route := .vedralBarencoEkertNetworks
  qftPolicy := .exactQFT
  resourceStatus := .asymptoticOnly

/-- Conservative policy for Fourier-space compact constructions when approximate
QFT formulas have not yet been converted to exact upper-bound functions. -/
def beauregardApproximatePlaceholder : ConstructionPolicy where
  route := .beauregardFourierSpace
  qftPolicy := .approximateQFTPlaceholder
  resourceStatus := .sourceBackedEstimate

@[simp] theorem elementaryNetworkPlaceholder_notExact :
    elementaryNetworkPlaceholder.canInstantiateExactResources = false :=
  rfl

@[simp] theorem beauregardApproximatePlaceholder_notExact :
    beauregardApproximatePlaceholder.canInstantiateExactResources = false :=
  rfl

end ConstructionPolicy

/-- Data registers for modular exponentiation in multiplicative-accumulator form. -/
structure Data (m N : ℕ) where
  /-- Exponent-register value carried by the modular-exponentiation data state. -/
  exponent : Fin (2 ^ m)
  /-- Target-register value carried by the modular-exponentiation data state. -/
  target : ZMod N
  /-- Clean control or comparison flag component. -/
  flag : Bool
deriving DecidableEq

instance instFintypeData (m N : ℕ) [NeZero N] : Fintype (Data m N) := by
  classical
  let e : Data m N ≃ (Fin (2 ^ m) × ZMod N × Bool) := {
    toFun := fun x => (x.exponent, (x.target, x.flag))
    invFun := fun x => { exponent := x.1, target := x.2.1, flag := x.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨exponent, rest⟩
      rcases rest with ⟨target, flag⟩
      rfl
  }
  exact Fintype.ofEquiv (Fin (2 ^ m) × ZMod N × Bool) e.symm

namespace Data

/-- Extensionality for modular-exponentiation data registers. -/
@[ext] theorem ext {m N : ℕ} {x y : Data m N}
    (hexponent : x.exponent = y.exponent)
    (htarget : x.target = y.target)
    (hflag : x.flag = y.flag) : x = y := by
  cases x
  cases y
  simp_all

/-- The clean flag convention for modular exponentiation. -/
def FlagClean {m N : ℕ} (x : Data m N) : Prop :=
  x.flag = false

/-- Apply the selected modular-exponentiation accumulator action. -/
def applyUnit {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) : Data m N where
  exponent := x.exponent
  target := x.target * ((u ^ x.exponent.val : (ZMod N)ˣ) : ZMod N)
  flag := x.flag

/-- Inverse accumulator action. -/
def inverseApplyUnit {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) : Data m N where
  exponent := x.exponent
  target := x.target * (((u⁻¹ : (ZMod N)ˣ) ^ x.exponent.val : (ZMod N)ˣ) : ZMod N)
  flag := x.flag

@[simp] theorem applyUnit_exponent {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) :
    (x.applyUnit u).exponent = x.exponent :=
  rfl

@[simp] theorem applyUnit_target {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) :
    (x.applyUnit u).target =
      x.target * ((u ^ x.exponent.val : (ZMod N)ˣ) : ZMod N) :=
  rfl

@[simp] theorem applyUnit_flag {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) :
    (x.applyUnit u).flag = x.flag :=
  rfl

@[simp] theorem inverseApplyUnit_exponent {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) :
    (x.inverseApplyUnit u).exponent = x.exponent :=
  rfl

@[simp] theorem inverseApplyUnit_target {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) :
    (x.inverseApplyUnit u).target =
      x.target * (((u⁻¹ : (ZMod N)ˣ) ^ x.exponent.val : (ZMod N)ˣ) : ZMod N) :=
  rfl

@[simp] theorem inverseApplyUnit_flag {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) :
    (x.inverseApplyUnit u).flag = x.flag :=
  rfl

/-- Clean flags remain clean after the selected accumulator action. -/
private theorem applyUnit_preserves_clean {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N)
    (h : x.FlagClean) : (x.applyUnit u).FlagClean :=
  h

/-- A unit power cancels the corresponding inverse-unit power after coercion
to the target residue ring. -/
theorem unit_pow_mul_inv_pow_coe {N : ℕ} (u : (ZMod N)ˣ) (e : ℕ) :
    ((u : ZMod N) ^ e) * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) ^ e) = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  simp [inv_pow]

/-- The inverse-unit power also cancels on the left after coercion. -/
theorem inv_pow_mul_unit_pow_coe {N : ℕ} (u : (ZMod N)ˣ) (e : ℕ) :
    (((u⁻¹ : (ZMod N)ˣ) : ZMod N) ^ e) * ((u : ZMod N) ^ e) = 1 := by
  rw [mul_comm]
  exact unit_pow_mul_inv_pow_coe u e

/-- The selected modular-exponentiation accumulator action as a reversible
permutation. -/
def applyUnitEquiv {m N : ℕ} (u : (ZMod N)ˣ) : Equiv.Perm (Data m N) where
  toFun := applyUnit u
  invFun := inverseApplyUnit u
  left_inv := by
    intro x
    ext <;> simp [applyUnit, inverseApplyUnit, mul_assoc,
      unit_pow_mul_inv_pow_coe]
  right_inv := by
    intro x
    ext <;> simp [applyUnit, inverseApplyUnit, mul_assoc,
      inv_pow_mul_unit_pow_coe]

@[simp] theorem applyUnitEquiv_apply {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) :
    applyUnitEquiv u x = x.applyUnit u :=
  rfl

/-- Modular exponentiation with an external work register, leaving work
untouched. -/
def withWorkEquiv {m N : ℕ} (u : (ZMod N)ˣ) (Work : Type) :
    Equiv.Perm (Data m N × Work) :=
  Equiv.prodCongr (applyUnitEquiv u) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {m N : ℕ} (u : (ZMod N)ˣ) {Work : Type}
    (x : Data m N) (w : Work) :
    withWorkEquiv u Work (x, w) = (x.applyUnit u, w) :=
  rfl

/-- The modular-exponentiation accumulator action leaves the external work
register clean. -/
theorem withWorkEquiv_preserves_work {m N : ℕ} (u : (ZMod N)ˣ) {Work : Type} :
    WorkRegister.Preserves (Data := Data m N) (Work := Work) (withWorkEquiv u Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for modular exponentiation with an external
work register. -/
def withWorkCleanMap {m N : ℕ} (u : (ZMod N)ˣ) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data m N) Work where
  perm := withWorkEquiv u Work
  preservesWork := withWorkEquiv_preserves_work u

@[simp] theorem withWorkCleanMap_perm_apply {m N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type} (x : Data m N) (w : Work) :
    (withWorkCleanMap u Work).perm (x, w) = (x.applyUnit u, w) :=
  rfl

/-- Clean multiplicative-accumulator input for modular exponentiation. -/
def cleanInput {m N : ℕ} (exponent : Fin (2 ^ m)) : Data m N where
  exponent := exponent
  target := 1
  flag := false

/-- Clean multiplicative-accumulator output for modular exponentiation. -/
def cleanOutput {m N : ℕ} (u : (ZMod N)ˣ) (exponent : Fin (2 ^ m)) :
    Data m N where
  exponent := exponent
  target := ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
  flag := false

@[simp] theorem applyUnit_cleanInput {m N : ℕ}
    (u : (ZMod N)ˣ) (exponent : Fin (2 ^ m)) :
    (cleanInput exponent).applyUnit u = cleanOutput u exponent := by
  ext <;> simp [cleanInput, cleanOutput, applyUnit]

private theorem withWorkCleanMap_perm_cleanInput {m N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type} (exponent : Fin (2 ^ m)) (w : Work) :
    (withWorkCleanMap u Work).perm (cleanInput exponent, w) =
      (cleanOutput u exponent, w) := by
  simp [withWorkCleanMap]

end Data

/-! ### Gate and circuit witness -/

/-- Register whose basis labels are modular-exponentiation accumulator states. -/
def register (m N : ℕ) [NeZero N] : Register where
  Index := Data m N
  fintype := inferInstance
  decEq := inferInstance

/-- Modular exponentiation accumulator gate `|e,y> ↦ |e,y*u^e>`. -/
noncomputable def applyUnitGate {m N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    Gate (register m N) :=
  Gate.ofPerm (Data.applyUnitEquiv (m := m) u).symm

/-- The modular-exponentiation accumulator gate is unitary by construction. -/
private theorem applyUnitGate_mem_unitaryGroup {m N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    ((applyUnitGate (m := m) u : Gate (register m N)) : HilbertOperator (register m N))
      ∈ Matrix.unitaryGroup (register m N).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Basis action of modular exponentiation: `|e,y> ↦ |e,y*u^e>`. -/
theorem applyUnitGate_apply_ket {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (x : Data m N) :
    (applyUnitGate u).apply (PureState.ket (R := register m N) x) =
      PureState.ket (R := register m N) (x.applyUnit u) := by
  rw [applyUnitGate, Gate.ofPerm_apply_ket]
  rfl

/-! ### Controlled-power schedule -/

/-- One controlled modular-multiplication step for exponentiation. -/
structure ControlledPowerStep (N : ℕ) where
  /-- Classical control bit selecting whether this scheduled step is active. -/
  control : Bool
  /-- Modular multiplier applied by this controlled-power step. -/
  multiplier : (ZMod N)ˣ
deriving DecidableEq

namespace ControlledPowerStep

/-- Unit contribution of a controlled-power step. -/
def contribution {N : ℕ} (step : ControlledPowerStep N) : (ZMod N)ˣ :=
  if step.control then step.multiplier else 1

/-- Apply one controlled-power step to the exponentiation target register. -/
def apply {m N : ℕ} (step : ControlledPowerStep N) (x : Data m N) : Data m N where
  exponent := x.exponent
  target := x.target * (step.contribution : ZMod N)
  flag := x.flag

@[simp] theorem apply_exponent {m N : ℕ} (step : ControlledPowerStep N) (x : Data m N) :
    (step.apply x).exponent = x.exponent :=
  rfl

@[simp] theorem apply_target {m N : ℕ} (step : ControlledPowerStep N) (x : Data m N) :
    (step.apply x).target = x.target * (step.contribution : ZMod N) :=
  rfl

@[simp] theorem apply_flag {m N : ℕ} (step : ControlledPowerStep N) (x : Data m N) :
    (step.apply x).flag = x.flag :=
  rfl

/-- Build the conventional step for bit `i`, controlled by that bit, with
multiplier `u^(2^i)`. -/
def powerBitStep {N : ℕ} (u : (ZMod N)ˣ) (i : ℕ) (control : Bool) :
    ControlledPowerStep N where
  control := control
  multiplier := u ^ (2 ^ i)

/-- Inverse controlled-power step. -/
def inverse {N : ℕ} (step : ControlledPowerStep N) : ControlledPowerStep N where
  control := step.control
  multiplier := step.multiplier⁻¹

@[simp] theorem inverse_control {N : ℕ} (step : ControlledPowerStep N) :
    step.inverse.control = step.control :=
  rfl

@[simp] theorem inverse_multiplier {N : ℕ} (step : ControlledPowerStep N) :
    step.inverse.multiplier = step.multiplier⁻¹ :=
  rfl

@[simp] theorem inverse_contribution {N : ℕ} (step : ControlledPowerStep N) :
    step.inverse.contribution = step.contribution⁻¹ := by
  rcases step with ⟨control, multiplier⟩
  cases control <;> simp [contribution, inverse]

@[simp] theorem inverse_apply_apply {m N : ℕ}
    (step : ControlledPowerStep N) (x : Data m N) :
    step.inverse.apply (step.apply x) = x := by
  ext <;> simp [apply, mul_assoc]

@[simp] theorem apply_inverse_apply {m N : ℕ}
    (step : ControlledPowerStep N) (x : Data m N) :
    step.apply (step.inverse.apply x) = x := by
  ext <;> simp [apply, mul_assoc]

/-- Controlled-power step as a reversible permutation on exponentiation data. -/
def applyEquiv {m N : ℕ} (step : ControlledPowerStep N) : Equiv.Perm (Data m N) where
  toFun := step.apply
  invFun := step.inverse.apply
  left_inv := by
    intro x
    exact inverse_apply_apply step x
  right_inv := by
    intro x
    exact apply_inverse_apply step x

@[simp] theorem applyEquiv_apply {m N : ℕ}
    (step : ControlledPowerStep N) (x : Data m N) :
    step.applyEquiv x = step.apply x :=
  rfl

/-- Controlled-power step with an external work register, leaving work
untouched. -/
def withWorkEquiv {m N : ℕ} (step : ControlledPowerStep N) (Work : Type) :
    Equiv.Perm (Data m N × Work) :=
  Equiv.prodCongr step.applyEquiv (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {m N : ℕ}
    (step : ControlledPowerStep N) {Work : Type} (x : Data m N) (w : Work) :
    step.withWorkEquiv Work (x, w) = (step.apply x, w) :=
  rfl

/-- A controlled-power step leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {m N : ℕ}
    (step : ControlledPowerStep N) {Work : Type} :
    WorkRegister.Preserves (Data := Data m N) (Work := Work) (step.withWorkEquiv Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for one controlled-power step. -/
def withWorkCleanMap {m N : ℕ} (step : ControlledPowerStep N) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data m N) Work where
  perm := step.withWorkEquiv Work
  preservesWork := step.withWorkEquiv_preserves_work

@[simp] theorem withWorkCleanMap_perm_apply {m N : ℕ}
    (step : ControlledPowerStep N) {Work : Type} (x : Data m N) (w : Work) :
    (step.withWorkCleanMap Work).perm (x, w) = (step.apply x, w) :=
  rfl

end ControlledPowerStep

/-- Product of the controlled unit contributions in a schedule. -/
def scheduleMultiplier {N : ℕ} : List (ControlledPowerStep N) → (ZMod N)ˣ
  | [] => 1
  | step :: rest => step.contribution * scheduleMultiplier rest

/-- Apply a controlled-power schedule. -/
def applySchedule {m N : ℕ} : List (ControlledPowerStep N) → Data m N → Data m N
  | [], x => x
  | step :: rest, x => applySchedule rest (step.apply x)

/-- Clean reversible map for the controlled-power schedule used in elementary
modular exponentiation [VBE95, 9511018.tex:372-416]. -/
def scheduleCleanMap {m N : ℕ} (steps : List (ControlledPowerStep N)) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data m N) Work :=
  match steps with
  | [] => WorkRegister.CleanReversibleMap.identity (Data m N) Work
  | step :: rest =>
      WorkRegister.CleanReversibleMap.sequential
        (ControlledPowerStep.withWorkCleanMap (m := m) step Work)
        (scheduleCleanMap (m := m) rest Work)

@[simp] theorem scheduleMultiplier_nil {N : ℕ} :
    scheduleMultiplier ([] : List (ControlledPowerStep N)) = 1 := rfl

@[simp] theorem scheduleMultiplier_cons {N : ℕ}
    (step : ControlledPowerStep N) (rest : List (ControlledPowerStep N)) :
    scheduleMultiplier (step :: rest) = step.contribution * scheduleMultiplier rest := rfl

theorem applySchedule_exponent {m N : ℕ}
    (steps : List (ControlledPowerStep N)) (x : Data m N) :
    (applySchedule steps x).exponent = x.exponent := by
  induction steps generalizing x with
  | nil => rfl
  | cons step rest ih =>
      simp [applySchedule, ih]

theorem applySchedule_flag {m N : ℕ}
    (steps : List (ControlledPowerStep N)) (x : Data m N) :
    (applySchedule steps x).flag = x.flag := by
  induction steps generalizing x with
  | nil => rfl
  | cons step rest ih =>
      simp [applySchedule, ih]

theorem applySchedule_target {m N : ℕ}
    (steps : List (ControlledPowerStep N)) (x : Data m N) :
    (applySchedule steps x).target =
      x.target * (scheduleMultiplier steps : ZMod N) := by
  induction steps generalizing x with
  | nil =>
      simp [applySchedule, scheduleMultiplier]
  | cons step rest ih =>
      rw [applySchedule, ih, scheduleMultiplier_cons, ControlledPowerStep.apply_target]
      simp [mul_assoc]

@[simp] theorem scheduleCleanMap_perm_apply {m N : ℕ}
    (steps : List (ControlledPowerStep N)) {Work : Type}
    (x : Data m N) (w : Work) :
    (scheduleCleanMap steps Work).perm (x, w) =
      (applySchedule steps x, w) := by
  induction steps generalizing x with
  | nil =>
      rfl
  | cons step rest ih =>
      simp [scheduleCleanMap, applySchedule,
        WorkRegister.CleanReversibleMap.sequential_perm, ih]

/-- Certificate that a controlled-power schedule realizes the selected
exponentiation multiplier for the given input. -/
structure CompositionCertificate {m N : ℕ} (u : (ZMod N)ˣ) (x : Data m N) where
  /-- Ordered schedule of reversible primitive steps used by the composition certificate. -/
  steps : List (ControlledPowerStep N)
  multiplier_eq : scheduleMultiplier steps = u ^ x.exponent.val

namespace CompositionCertificate

/-- Correctness of a controlled-power schedule whose product is `u^x`. -/
theorem applySchedule_eq_applyUnit {m N : ℕ} {u : (ZMod N)ˣ} {x : Data m N}
    (certificate : CompositionCertificate u x) :
    applySchedule certificate.steps x = x.applyUnit u := by
  ext <;>
    simp [applySchedule_exponent, applySchedule_flag, applySchedule_target,
      certificate.multiplier_eq, Data.applyUnit]

/-- Clean reversible map selected by a schedule-composition certificate. -/
def cleanMap {m N : ℕ} {u : (ZMod N)ˣ} {x : Data m N}
    (certificate : CompositionCertificate u x) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data m N) Work :=
  scheduleCleanMap certificate.steps Work

/-- The certified schedule clean map realizes the same accumulator action as
the modular-exponentiation unit on its certified input. -/
@[simp] theorem cleanMap_perm_applyUnit {m N : ℕ} {u : (ZMod N)ˣ} {x : Data m N}
    (certificate : CompositionCertificate u x) {Work : Type} (w : Work) :
    (certificate.cleanMap Work).perm (x, w) = (x.applyUnit u, w) := by
  simp [cleanMap, certificate.applySchedule_eq_applyUnit]

end CompositionCertificate

/-! ### Exact-resource recurrence -/

/-- Concrete parameters for modular-exponentiation resource recurrence. The
lower-level profiles are exact counts or explicit upper-bound functions supplied
by source-backed counting passes; the recurrence itself is finite and contains
no asymptotic notation. -/
structure ResourceParameters where
  /-- Bit width used for the modulus/register footprint. -/
  modulusBits : ℕ
  /-- Number of exponent bits, equivalently the number of controlled
  multiplication slots in the binary-power schedule. -/
  exponentWidth : ℕ
  /-- Extra control qubits live with the exponent and target registers. -/
  controlQubits : ℕ
  /-- Clean work qubits reserved by the chosen construction. -/
  workQubits : ℕ
  /-- One-time precomputation or lookup-generation profile for powers of the
  base used by the schedule. -/
  powerPrecomputeProfile : ModularArithmeticResourceProfile
  /-- Profile for one modular multiplication by a selected power of the base. -/
  multiplicationProfile : ModularArithmeticResourceProfile
  /-- Per-bit overhead for selecting/controlling the corresponding modular
  multiplication block. -/
  controlOverhead : ModularArithmeticResourceProfile
deriving DecidableEq

namespace ResourceParameters

/-- Register-only footprint for the exponent, target, controls, and clean work
registers. It carries no gate or classical-operation counts. -/
def registerFootprint (params : ResourceParameters) : ModularArithmeticResourceProfile where
  logicalQubits :=
    params.exponentWidth + params.modulusBits + params.controlQubits + params.workQubits
  dataQubits := params.exponentWidth + params.modulusBits + params.controlQubits
  workQubits := params.workQubits
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := 0
  tGates := 0
  cnotGates := 0
  singleQubitGates := 0
  circuitDepth := 0
  toffoliDepth := 0
  classicalArithmetic := ClassicalArithmeticProfile.zero

/-- One controlled modular-multiplication slot in the binary-power schedule. -/
def controlledMultiplicationStep (params : ResourceParameters) :
    ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential params.controlOverhead
    params.multiplicationProfile

/-- Sequential recurrence over the exponent bit width. The same live footprint
is reused while counted work and depth scale with the number of bits. -/
def scheduledMultiplications (params : ResourceParameters) :
    ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.repeatSequential params.exponentWidth
    params.controlledMultiplicationStep

/-- Full modular-exponentiation recurrence: keep the register footprint live,
perform one source-backed precomputation pass, then run the controlled
multiplication schedule. -/
def toProfile (params : ResourceParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential params.registerFootprint
    (ModularArithmeticResourceProfile.sequential params.powerPrecomputeProfile
      params.scheduledMultiplications)

/-- Coarse projection used by existing circuit-level resource statements. -/
def toResourceProfile (params : ResourceParameters) : ResourceProfile :=
  params.toProfile.toResourceProfile

@[simp] theorem registerFootprint_logicalQubits (params : ResourceParameters) :
    params.registerFootprint.logicalQubits =
      params.exponentWidth + params.modulusBits + params.controlQubits + params.workQubits :=
  rfl

@[simp] theorem registerFootprint_dataQubits (params : ResourceParameters) :
    params.registerFootprint.dataQubits =
      params.exponentWidth + params.modulusBits + params.controlQubits :=
  rfl

@[simp] theorem registerFootprint_workQubits (params : ResourceParameters) :
    params.registerFootprint.workQubits = params.workQubits :=
  rfl

@[simp] theorem registerFootprint_classicalArithmetic (params : ResourceParameters) :
    params.registerFootprint.classicalArithmetic = ClassicalArithmeticProfile.zero :=
  rfl

@[simp] theorem controlledMultiplicationStep_logicalQubits
    (params : ResourceParameters) :
    params.controlledMultiplicationStep.logicalQubits =
      max params.controlOverhead.logicalQubits params.multiplicationProfile.logicalQubits :=
  rfl

@[simp] theorem controlledMultiplicationStep_workQubits
    (params : ResourceParameters) :
    params.controlledMultiplicationStep.workQubits =
      max params.controlOverhead.workQubits params.multiplicationProfile.workQubits :=
  rfl

@[simp] theorem controlledMultiplicationStep_toffoliGates
    (params : ResourceParameters) :
    params.controlledMultiplicationStep.toffoliGates =
      params.controlOverhead.toffoliGates + params.multiplicationProfile.toffoliGates :=
  rfl

@[simp] theorem controlledMultiplicationStep_circuitDepth
    (params : ResourceParameters) :
    params.controlledMultiplicationStep.circuitDepth =
      params.controlOverhead.circuitDepth + params.multiplicationProfile.circuitDepth :=
  rfl

@[simp] theorem scheduledMultiplications_eq_repeatSequential
    (params : ResourceParameters) :
    params.scheduledMultiplications =
      ModularArithmeticResourceProfile.repeatSequential params.exponentWidth
        params.controlledMultiplicationStep :=
  rfl

private theorem scheduledMultiplications_zero_width (params : ResourceParameters)
    (h : params.exponentWidth = 0) :
    params.scheduledMultiplications = ModularArithmeticResourceProfile.zero := by
  cases params
  cases h
  rfl

@[simp] theorem toProfile_eq_register_precompute_schedule
    (params : ResourceParameters) :
    params.toProfile =
      ModularArithmeticResourceProfile.sequential params.registerFootprint
        (ModularArithmeticResourceProfile.sequential params.powerPrecomputeProfile
          params.scheduledMultiplications) :=
  rfl

@[simp] theorem toProfile_logicalQubits (params : ResourceParameters) :
    params.toProfile.logicalQubits =
      max params.registerFootprint.logicalQubits
        (max params.powerPrecomputeProfile.logicalQubits
          params.scheduledMultiplications.logicalQubits) :=
  rfl

@[simp] theorem toProfile_workQubits (params : ResourceParameters) :
    params.toProfile.workQubits =
      max params.registerFootprint.workQubits
        (max params.powerPrecomputeProfile.workQubits
          params.scheduledMultiplications.workQubits) :=
  rfl

theorem toProfile_toffoliGates (params : ResourceParameters) :
    params.toProfile.toffoliGates =
      params.powerPrecomputeProfile.toffoliGates +
        params.scheduledMultiplications.toffoliGates := by
  simp [toProfile, registerFootprint, ModularArithmeticResourceProfile.sequential]

theorem toProfile_circuitDepth (params : ResourceParameters) :
    params.toProfile.circuitDepth =
      params.powerPrecomputeProfile.circuitDepth +
        params.scheduledMultiplications.circuitDepth := by
  simp [toProfile, registerFootprint, ModularArithmeticResourceProfile.sequential]

@[simp] theorem toProfile_classicalArithmetic (params : ResourceParameters) :
    params.toProfile.classicalArithmetic =
      ClassicalArithmeticProfile.sequential params.registerFootprint.classicalArithmetic
        (ClassicalArithmeticProfile.sequential params.powerPrecomputeProfile.classicalArithmetic
          params.scheduledMultiplications.classicalArithmetic) :=
  rfl

@[simp] theorem toResourceProfile_eq (params : ResourceParameters) :
    params.toResourceProfile = params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem toResourceProfile_classicalOps (params : ResourceParameters) :
    params.toResourceProfile.classicalOps = params.toProfile.classicalArithmetic.total :=
  rfl

private theorem toResourceProfile_classicalOps_recurrence
    (params : ResourceParameters) :
    params.toResourceProfile.classicalOps =
      params.powerPrecomputeProfile.classicalArithmetic.total +
        params.scheduledMultiplications.classicalArithmetic.total := by
  simp [toResourceProfile, toProfile, registerFootprint,
    ModularArithmeticResourceProfile.sequential,
    ModularArithmeticResourceProfile.toResourceProfile]

/-! #### Circuit witness -/

/-- Typed circuit witness for the modular-exponentiation accumulator action.
The interpreted gate and projected resource profile are attached to the same
`Circuit` object. -/
noncomputable def applyUnitCircuit {m N : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (params : ResourceParameters) : Circuit (register m N) :=
  Circuit.ofGate "modular-exponentiation-accumulator" (applyUnitGate u)
    params.toResourceProfile params.toProfile.circuitDepth params.toProfile.oracleQueries

@[simp] theorem applyUnitCircuit_resources {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) :
    (applyUnitCircuit (m := m) u params).resources = params.toResourceProfile :=
  rfl

@[simp] theorem applyUnitCircuit_depth {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) :
    (applyUnitCircuit (m := m) u params).depth = params.toProfile.circuitDepth :=
  rfl

@[simp] theorem applyUnitCircuit_queryDepth {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) :
    (applyUnitCircuit (m := m) u params).queryDepth = params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for the typed modular-exponentiation circuit
witness. -/
theorem applyUnitCircuit_apply_ket {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) (x : Data m N) :
    Circuit.apply (applyUnitCircuit u params)
      (PureState.ket (R := register m N) x : StateVector (register m N)) =
      (PureState.ket (R := register m N) (x.applyUnit u) :
        StateVector (register m N)) := by
  simpa [applyUnitCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register m N) =>
      (psi : StateVector (register m N))) (applyUnitGate_apply_ket u x)

/-- Resource-correct witness for modular exponentiation: correctness and the
projected resource counters refer to the same typed circuit. -/
noncomputable def applyUnitCircuitResourceCorrectWitness {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) :
    ResourceCorrectWitness (R := register m N)
      (∀ x : Data m N,
        Circuit.apply (applyUnitCircuit (m := m) u params)
          (PureState.ket (R := register m N) x : StateVector (register m N)) =
          (PureState.ket (R := register m N) (x.applyUnit u) :
            StateVector (register m N)))
      ((applyUnitCircuit (m := m) u params).resources = params.toResourceProfile ∧
        (applyUnitCircuit (m := m) u params).depth = params.toProfile.circuitDepth ∧
        (applyUnitCircuit (m := m) u params).queryDepth =
          params.toProfile.oracleQueries) := by
  exact
    { circuit := applyUnitCircuit (m := m) u params
      correctness := fun x => applyUnitCircuit_apply_ket u params x
      resources := ⟨rfl, rfl, rfl⟩ }

/-! #### Clean-work and controlled-schedule circuit endpoints -/

/-- Typed clean-work circuit wrapper for the modular-exponentiation accumulator
action, leaving the external work register untouched. -/
noncomputable def applyUnitWithWorkCircuit {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data m N) Work) :=
  (Data.withWorkCleanMap u Work).circuit params.toProfile

@[simp] theorem applyUnitWithWorkCircuit_resources {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (applyUnitWithWorkCircuit (m := m) u Work params).resources =
      params.toResourceProfile :=
  rfl

@[simp] theorem applyUnitWithWorkCircuit_depth {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (applyUnitWithWorkCircuit (m := m) u Work params).depth =
      params.toProfile.circuitDepth :=
  rfl

@[simp] theorem applyUnitWithWorkCircuit_queryDepth {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (applyUnitWithWorkCircuit (m := m) u Work params).queryDepth =
      params.toProfile.oracleQueries :=
  rfl

/-- Basis-state action of the clean-work modular-exponentiation circuit. -/
theorem applyUnitWithWorkCircuit_apply_ket {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : Data m N) (w : Work) :
    Circuit.apply (applyUnitWithWorkCircuit (m := m) u Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work) (x, w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
        (x.applyUnit u, w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) := by
  simpa [applyUnitWithWorkCircuit] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := Data.withWorkCleanMap u Work)
      (profile := params.toProfile) (x := (x, w))

/-- Clean-basis action of the clean-work modular-exponentiation circuit:
`|x,y,0>|w> ↦ |x,y*u^x,0>|w>`. -/
private theorem applyUnitWithWorkCircuit_apply_clean_ket {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters)
    (exponent : Fin (2 ^ m)) (target : ZMod N) (w : Work) :
    Circuit.apply (applyUnitWithWorkCircuit (m := m) u Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
        (({ exponent := exponent, target := target, flag := false } : Data m N), w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
        (({ exponent := exponent
            target := target * ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
            flag := false } : Data m N), w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) := by
  simpa [Data.applyUnit] using
    applyUnitWithWorkCircuit_apply_ket (m := m) u Work params
      ({ exponent := exponent, target := target, flag := false } : Data m N) w

/-- Resource-correct witness for the clean-work modular-exponentiation
accumulator circuit. -/
noncomputable def applyUnitWithWorkCircuitResourceCorrectWitness
    {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
      (∀ x : Data m N × Work,
        Circuit.apply (applyUnitWithWorkCircuit (m := m) u Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data m N) Work) x :
            StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
            (x.1.applyUnit u, x.2) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)))
      ((applyUnitWithWorkCircuit (m := m) u Work params).resources =
          params.toResourceProfile ∧
        (applyUnitWithWorkCircuit (m := m) u Work params).depth =
          params.toProfile.circuitDepth ∧
        (applyUnitWithWorkCircuit (m := m) u Work params).queryDepth =
          params.toProfile.oracleQueries) := by
  exact
    { circuit := applyUnitWithWorkCircuit (m := m) u Work params
      correctness := fun x =>
        applyUnitWithWorkCircuit_apply_ket (m := m) u Work params x.1 x.2
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Typed circuit wrapper for a repeated controlled-power schedule. -/
noncomputable def controlledPowerScheduleCircuit {m N : ℕ} [NeZero N]
    (steps : List (ControlledPowerStep N))
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data m N) Work) :=
  (scheduleCleanMap (m := m) steps Work).circuit params.scheduledMultiplications

@[simp] theorem controlledPowerScheduleCircuit_resources {m N : ℕ} [NeZero N]
    (steps : List (ControlledPowerStep N))
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (controlledPowerScheduleCircuit (m := m) steps Work params).resources =
      params.scheduledMultiplications.toResourceProfile :=
  rfl

@[simp] theorem controlledPowerScheduleCircuit_depth {m N : ℕ} [NeZero N]
    (steps : List (ControlledPowerStep N))
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (controlledPowerScheduleCircuit (m := m) steps Work params).depth =
      params.scheduledMultiplications.circuitDepth :=
  rfl

@[simp] theorem controlledPowerScheduleCircuit_queryDepth {m N : ℕ} [NeZero N]
    (steps : List (ControlledPowerStep N))
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (controlledPowerScheduleCircuit (m := m) steps Work params).queryDepth =
      params.scheduledMultiplications.oracleQueries :=
  rfl

/-- Basis-state action of a typed controlled-power schedule circuit. -/
theorem controlledPowerScheduleCircuit_apply_ket {m N : ℕ} [NeZero N]
    (steps : List (ControlledPowerStep N))
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : Data m N) (w : Work) :
    Circuit.apply (controlledPowerScheduleCircuit (m := m) steps Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work) (x, w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
        (applySchedule steps x, w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) := by
  simpa [controlledPowerScheduleCircuit] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := scheduleCleanMap (m := m) steps Work)
      (profile := params.scheduledMultiplications) (x := (x, w))

/-- A schedule-composition certificate turns the typed schedule circuit into
the modular-exponentiation accumulator action on the certified input. -/
private theorem controlledPowerScheduleCircuit_applyUnit_of_certificate
    {m N : ℕ} [NeZero N] {u : (ZMod N)ˣ} {x : Data m N}
    (certificate : CompositionCertificate u x)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (w : Work) :
    Circuit.apply
      (controlledPowerScheduleCircuit (m := m) certificate.steps Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work) (x, w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
        (x.applyUnit u, w) :
        StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) := by
  rw [controlledPowerScheduleCircuit_apply_ket]
  simp [certificate.applySchedule_eq_applyUnit]

/-- Resource-correct witness for a typed controlled-power schedule circuit. -/
noncomputable def controlledPowerScheduleCircuitResourceCorrectWitness
    {m N : ℕ} [NeZero N]
    (steps : List (ControlledPowerStep N))
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
      (∀ x : Data m N × Work,
        Circuit.apply
          (controlledPowerScheduleCircuit (m := m) steps Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data m N) Work) x :
            StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data m N) Work)
            (applySchedule steps x.1, x.2) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data m N) Work)))
      ((controlledPowerScheduleCircuit (m := m) steps Work params).resources =
          params.scheduledMultiplications.toResourceProfile ∧
        (controlledPowerScheduleCircuit (m := m) steps Work params).depth =
          params.scheduledMultiplications.circuitDepth ∧
        (controlledPowerScheduleCircuit (m := m) steps Work params).queryDepth =
          params.scheduledMultiplications.oracleQueries) := by
  exact
    { circuit := controlledPowerScheduleCircuit (m := m) steps Work params
      correctness := fun x =>
        controlledPowerScheduleCircuit_apply_ket (m := m) steps Work params x.1 x.2
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Concrete component bounds for modular exponentiation in the selected
multiplicative-accumulator convention. -/
structure PublicBaselineBounds where
  /-- Exponent width component of this record. -/
  exponentWidth : ℕ
  /-- Explicit upper bound for the register footprint component. -/
  registerFootprintBound : ModularArithmeticResourceProfile
  /-- Explicit upper bound for the power precompute component. -/
  powerPrecomputeBound : ModularArithmeticResourceProfile
  /-- Explicit upper bound for the control overhead component. -/
  controlOverheadBound : ModularArithmeticResourceProfile
  /-- Explicit upper bound for the multiplication component. -/
  multiplicationBound : ModularArithmeticResourceProfile
deriving DecidableEq

namespace PublicBaselineBounds

/-- Bound for one controlled modular-multiplication slot. -/
def controlledMultiplicationStepBound
    (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.controlOverheadBound
    bounds.multiplicationBound

/-- Bound for the repeated controlled-multiplication schedule. -/
def scheduledMultiplicationsBound
    (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.repeatSequential bounds.exponentWidth
    bounds.controlledMultiplicationStepBound

/-- Source-facing modular-exponentiation bound obtained by composing register
footprint, precomputation, and scheduled controlled multiplications. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.registerFootprintBound
    (ModularArithmeticResourceProfile.sequential bounds.powerPrecomputeBound
      bounds.scheduledMultiplicationsBound)

end PublicBaselineBounds

/-- The exact modular-exponentiation recurrence supports the composed public
baseline bounds. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  upperBound :
    ModularArithmeticResourceProfile.SupportsUpperBound profile bounds.toProfile

/-- Fieldwise source-bound certificate for every component of the modular
exponentiation recurrence. -/
structure SourceBoundCertificate
    (params : ResourceParameters) (bounds : PublicBaselineBounds) : Prop where
  exponentWidth_eq : params.exponentWidth = bounds.exponentWidth
  registerFootprint_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.registerFootprint bounds.registerFootprintBound
  powerPrecompute_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.powerPrecomputeProfile bounds.powerPrecomputeBound
  controlOverhead_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.controlOverhead bounds.controlOverheadBound
  multiplication_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.multiplicationProfile bounds.multiplicationBound

/-- The componentwise certificate bounds one controlled-multiplication slot. -/
theorem SourceBoundCertificate.controlledMultiplicationStepBound
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.controlledMultiplicationStep bounds.controlledMultiplicationStepBound := by
  simpa [controlledMultiplicationStep, PublicBaselineBounds.controlledMultiplicationStepBound] using
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential
      cert.controlOverhead_le cert.multiplication_le

/-- The componentwise certificate bounds the repeated controlled-multiplication
schedule. -/
theorem SourceBoundCertificate.scheduledMultiplicationsBound
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.scheduledMultiplications bounds.scheduledMultiplicationsBound := by
  rw [scheduledMultiplications_eq_repeatSequential,
    PublicBaselineBounds.scheduledMultiplicationsBound, cert.exponentWidth_eq]
  exact
    ModularArithmeticResourceProfile.SupportsUpperBound.repeatSequential
      cert.controlledMultiplicationStepBound

/-- A componentwise source-bound certificate implies the public composed bound
for modular exponentiation. -/
theorem SourceBoundCertificate.supportsUpperBound
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound params.toProfile bounds.toProfile := by
  simpa [toProfile, PublicBaselineBounds.toProfile] using
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential cert.registerFootprint_le
      (ModularArithmeticResourceProfile.SupportsUpperBound.sequential
        cert.powerPrecompute_le cert.scheduledMultiplicationsBound)

/-- A componentwise source-bound certificate instantiates the source-facing
public baseline predicate. -/
theorem SourceBoundCertificate.supportsPublicBaseline
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    SupportsPublicBaseline params.toProfile bounds where
  upperBound := cert.supportsUpperBound

/-- Clean basis action of the typed modular-exponentiation circuit in
accumulator form: `|x,y,0> ↦ |x,y*u^x,0>`. -/
theorem applyUnitCircuit_apply_clean_ket {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters)
    (exponent : Fin (2 ^ m)) (target : ZMod N) :
    Circuit.apply (applyUnitCircuit (m := m) u params)
      (PureState.ket (R := register m N)
        ({ exponent := exponent, target := target, flag := false } : Data m N) :
          StateVector (register m N)) =
      (PureState.ket (R := register m N)
        ({ exponent := exponent
           target := target * ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
           flag := false } : Data m N) :
          StateVector (register m N)) := by
  simpa [Data.applyUnit] using
    applyUnitCircuit_apply_ket u params
      ({ exponent := exponent, target := target, flag := false } : Data m N)

/-- Modular-exponentiation endpoint with explicit component resource bounds.
The source-bound certificate supplies the chosen repeated controlled-
multiplication construction; the theorem keeps the typed accumulator circuit as
the shared object for correctness and resource projection. -/
private theorem main_with_public_bounds {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters)
    (bounds : PublicBaselineBounds)
    (componentBounds : SourceBoundCertificate params bounds) :
    (∀ exponent : Fin (2 ^ m), ∀ target : ZMod N,
      Circuit.apply (applyUnitCircuit (m := m) u params)
        (PureState.ket (R := register m N)
          ({ exponent := exponent, target := target, flag := false } : Data m N) :
            StateVector (register m N)) =
        (PureState.ket (R := register m N)
          ({ exponent := exponent
             target := target * ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
             flag := false } : Data m N) :
            StateVector (register m N))) ∧
      SupportsPublicBaseline params.toProfile bounds ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        params.toProfile bounds.toProfile ∧
      (applyUnitCircuit (m := m) u params).resources = params.toResourceProfile ∧
      (applyUnitCircuit (m := m) u params).depth = params.toProfile.circuitDepth ∧
      (applyUnitCircuit (m := m) u params).queryDepth =
        params.toProfile.oracleQueries := by
  constructor
  · intro exponent target
    exact applyUnitCircuit_apply_clean_ket u params exponent target
  constructor
  · exact componentBounds.supportsPublicBaseline
  constructor
  · exact componentBounds.supportsUpperBound
  · exact ⟨rfl, rfl, rfl⟩

/-- Resource-correct witness for the bounded modular-exponentiation endpoint. -/
private noncomputable def mainWithPublicBoundsResourceCorrectWitness
    {m N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters)
    (bounds : PublicBaselineBounds)
    (componentBounds : SourceBoundCertificate params bounds) :
    ResourceCorrectWitness (R := register m N)
      (∀ exponent : Fin (2 ^ m), ∀ target : ZMod N,
        Circuit.apply (applyUnitCircuit (m := m) u params)
          (PureState.ket (R := register m N)
            ({ exponent := exponent, target := target, flag := false } : Data m N) :
              StateVector (register m N)) =
          (PureState.ket (R := register m N)
            ({ exponent := exponent
               target := target * ((u ^ exponent.val : (ZMod N)ˣ) : ZMod N)
               flag := false } : Data m N) :
              StateVector (register m N)))
      (SupportsPublicBaseline params.toProfile bounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          params.toProfile bounds.toProfile ∧
        (applyUnitCircuit (m := m) u params).resources = params.toResourceProfile ∧
        (applyUnitCircuit (m := m) u params).depth = params.toProfile.circuitDepth ∧
        (applyUnitCircuit (m := m) u params).queryDepth =
          params.toProfile.oracleQueries) := by
  have hmain := main_with_public_bounds (m := m) u params bounds componentBounds
  exact
    { circuit := applyUnitCircuit (m := m) u params
      correctness := hmain.1
      resources := ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
        hmain.2.2.2.2.1, hmain.2.2.2.2.2⟩ }

end ResourceParameters

/-! ### Source-backed VBE package for modular exponentiation -/

namespace VBECounting

/-- Canonical VBE modular-multiplication parameters reused by the
modular-exponentiation package. -/
def vbeUnitMultiplicationResourceParameters (n : ℕ) :
    ModularMultiplication.ResourceParameters :=
  ModularMultiplication.VBECounting.vbeUnitMultiplicationResourceParameters n

/-- Canonical VBE modular-multiplication bounds reused by the
modular-exponentiation package. -/
def vbeUnitMultiplicationBounds (n : ℕ) :
    ModularMultiplication.ResourceParameters.PublicBaselineBounds :=
  ModularMultiplication.VBECounting.vbeUnitMultiplicationBounds n

/-- Canonical profile for one modular multiplication by a selected power in the
VBE modular-exponentiation route. -/
def vbeMultiplicationProfile (n : ℕ) : ModularArithmeticResourceProfile :=
  (vbeUnitMultiplicationResourceParameters n).toProfile

/-- Canonical source-backed bound for one modular multiplication by a selected
power in the VBE modular-exponentiation route. -/
def vbeMultiplicationBound (n : ℕ) : ModularArithmeticResourceProfile :=
  (vbeUnitMultiplicationBounds n).toProfile

/-- Explicit one-time precomputation profile for the binary-power table used by
the elementary square-and-multiply route. -/
def vbePowerPrecomputeProfile (exponentWidth : ℕ) : ModularArithmeticResourceProfile :=
  { ModularArithmeticResourceProfile.zero with
    classicalArithmetic :=
      { ClassicalArithmeticProfile.zero with
        groupControl :=
          { GroupControlOperationProfile.zero with precomputeOps := exponentWidth } } }

/-- Explicit per-bit control-selection overhead for the controlled-power
schedule. -/
def vbeControlOverheadProfile : ModularArithmeticResourceProfile :=
  { ModularArithmeticResourceProfile.zero with
    classicalArithmetic := ClassicalArithmeticProfile.ofControlRewriteOps 1 }

/-- Canonical VBE modular-exponentiation resource parameters for the
controlled-power schedule described by Vedral--Barenco--Ekert [VBE95,
9511018.tex:372-416]. -/
def vbeModularExponentiationResourceParameters
    (exponentWidth modulusBits : ℕ) : ResourceParameters where
  modulusBits := modulusBits
  exponentWidth := exponentWidth
  controlQubits := 1
  workQubits := (vbeMultiplicationProfile modulusBits).workQubits
  powerPrecomputeProfile := vbePowerPrecomputeProfile exponentWidth
  multiplicationProfile := vbeMultiplicationProfile modulusBits
  controlOverhead := vbeControlOverheadProfile

/-- Canonical VBE modular-exponentiation public bounds for the elementary
controlled-power schedule [VBE95, 9511018.tex:372-416]. -/
def vbeModularExponentiationBounds
    (exponentWidth modulusBits : ℕ) : ResourceParameters.PublicBaselineBounds where
  exponentWidth := exponentWidth
  registerFootprintBound :=
    (vbeModularExponentiationResourceParameters exponentWidth modulusBits).registerFootprint
  powerPrecomputeBound := vbePowerPrecomputeProfile exponentWidth
  controlOverheadBound := vbeControlOverheadProfile
  multiplicationBound := vbeMultiplicationBound modulusBits

/-- The canonical VBE modular-exponentiation package supplies its component
source-bound certificate without caller-selected modular-multiplication,
precomputation, or control-overhead profiles. -/
theorem vbeModularExponentiationSourceBoundCertificate
    (exponentWidth modulusBits : ℕ) (hpos : 0 < modulusBits) :
    ResourceParameters.SourceBoundCertificate
      (vbeModularExponentiationResourceParameters exponentWidth modulusBits)
      (vbeModularExponentiationBounds exponentWidth modulusBits) := by
  have hmul :=
    ModularMultiplication.ResourceParameters.SourceBoundCertificate.supportsUpperBound
      (ModularMultiplication.VBECounting.vbeUnitMultiplicationSourceBoundCertificate
        modulusBits hpos)
  refine
    { exponentWidth_eq := ?_
      registerFootprint_le := ?_
      powerPrecompute_le := ?_
      controlOverhead_le := ?_
      multiplication_le := ?_ }
  · rfl
  · simpa [vbeModularExponentiationBounds] using
      ModularArithmeticResourceProfile.SupportsUpperBound.refl
        (vbeModularExponentiationResourceParameters exponentWidth modulusBits).registerFootprint
  · simpa [vbeModularExponentiationResourceParameters, vbeModularExponentiationBounds] using
      ModularArithmeticResourceProfile.SupportsUpperBound.refl
        (vbePowerPrecomputeProfile exponentWidth)
  · simpa [vbeModularExponentiationResourceParameters, vbeModularExponentiationBounds] using
      ModularArithmeticResourceProfile.SupportsUpperBound.refl vbeControlOverheadProfile
  · simpa [vbeModularExponentiationResourceParameters, vbeModularExponentiationBounds,
      vbeMultiplicationProfile, vbeMultiplicationBound,
      vbeUnitMultiplicationResourceParameters, vbeUnitMultiplicationBounds] using hmul

end VBECounting

end ModularExponentiation
end QuantumAlg
