/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularAddition
public import QuantumAlg.Primitives.MAU.VBEBlockCounting

/-!
# Reversible modular multiply-accumulate

This module fixes the reusable multiply-accumulate convention used by modular
multiplication and exponentiation support.  For a constant `a : ZMod N`, the
map preserves the multiplicand and clean flag while updating the accumulator by
`y ↦ y + a*x`.

The MAC recurrence is the Lean-facing structural form of building controlled
modular multiplication from repeated controlled modular additions [VBE95,
9511018.tex:333-350]. Gidney--Ekerå use the same modular-arithmetic vocabulary
inside their RSA resource envelope [GE19, main.tex:511-519]; that citation is
resource-route context rather than an independent exact construction promoted
here.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularMultiplyAccumulate

/-- Data registers for a modular multiply-accumulate map. -/
structure Data (N : ℕ) where
  /-- Multiplicand register value for multiply-accumulate data. -/
  multiplicand : ZMod N
  /-- Accumulator register value for multiply-accumulate data. -/
  accumulator : ZMod N
  /-- Clean control or comparison flag component. -/
  flag : Bool
deriving DecidableEq

instance instFintypeData (N : ℕ) [NeZero N] : Fintype (Data N) := by
  classical
  let e : Data N ≃ (ZMod N × ZMod N × Bool) := {
    toFun := fun x => (x.multiplicand, (x.accumulator, x.flag))
    invFun := fun x => { multiplicand := x.1, accumulator := x.2.1, flag := x.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨multiplicand, rest⟩
      rcases rest with ⟨accumulator, flag⟩
      rfl
  }
  exact Fintype.ofEquiv (ZMod N × ZMod N × Bool) e.symm

namespace Data

/-- Extensionality for MAC data registers. -/
@[ext] theorem ext {N : ℕ} {x y : Data N}
    (hmultiplicand : x.multiplicand = y.multiplicand)
    (haccumulator : x.accumulator = y.accumulator)
    (hflag : x.flag = y.flag) : x = y := by
  cases x
  cases y
  simp_all

/-- The clean flag convention for multiply-accumulate. -/
def FlagClean {N : ℕ} (x : Data N) : Prop :=
  x.flag = false

/-- Add `a * multiplicand` into the accumulator. -/
def addScaled {N : ℕ} (a : ZMod N) (x : Data N) : Data N where
  multiplicand := x.multiplicand
  accumulator := x.accumulator + a * x.multiplicand
  flag := x.flag

/-- Inverse operation for `addScaled`. -/
def subScaled {N : ℕ} (a : ZMod N) (x : Data N) : Data N where
  multiplicand := x.multiplicand
  accumulator := x.accumulator - a * x.multiplicand
  flag := x.flag

@[simp] theorem addScaled_multiplicand {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.addScaled a).multiplicand = x.multiplicand :=
  rfl

@[simp] theorem addScaled_accumulator {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.addScaled a).accumulator = x.accumulator + a * x.multiplicand :=
  rfl

@[simp] theorem addScaled_flag {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.addScaled a).flag = x.flag :=
  rfl

@[simp] theorem subScaled_multiplicand {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.subScaled a).multiplicand = x.multiplicand :=
  rfl

@[simp] theorem subScaled_accumulator {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.subScaled a).accumulator = x.accumulator - a * x.multiplicand :=
  rfl

@[simp] theorem subScaled_flag {N : ℕ} (a : ZMod N) (x : Data N) :
    (x.subScaled a).flag = x.flag :=
  rfl

/-- Clean flags remain clean after multiply-accumulate. -/
private theorem addScaled_preserves_clean {N : ℕ} (a : ZMod N) (x : Data N)
    (h : x.FlagClean) : (x.addScaled a).FlagClean :=
  h

/-- Clean flags remain clean after inverse multiply-accumulate. -/
private theorem subScaled_preserves_clean {N : ℕ} (a : ZMod N) (x : Data N)
    (h : x.FlagClean) : (x.subScaled a).FlagClean :=
  h

/-- Reversible multiply-accumulate permutation for a fixed constant `a`. -/
def macEquiv {N : ℕ} (a : ZMod N) : Equiv.Perm (Data N) where
  toFun := addScaled a
  invFun := subScaled a
  left_inv := by
    intro x
    cases x
    simp [addScaled, subScaled]
  right_inv := by
    intro x
    cases x
    simp [addScaled, subScaled]

@[simp] theorem macEquiv_apply {N : ℕ} (a : ZMod N) (x : Data N) :
    macEquiv a x = x.addScaled a :=
  rfl

/-- Boolean-control convention: `false` is identity and `true` applies MAC. -/
def controlledApply {N : ℕ} (a : ZMod N) (control : Bool) (x : Data N) : Data N :=
  if control then x.addScaled a else x

@[simp] theorem controlledApply_false {N : ℕ} (a : ZMod N) (x : Data N) :
    controlledApply a false x = x := by
  simp [controlledApply]

@[simp] theorem controlledApply_true {N : ℕ} (a : ZMod N) (x : Data N) :
    controlledApply a true x = x.addScaled a := by
  simp [controlledApply]

/-- Multiply-accumulate with an external work register, leaving work untouched. -/
def withWorkEquiv {N : ℕ} (a : ZMod N) (Work : Type) :
    Equiv.Perm (Data N × Work) :=
  Equiv.prodCongr (macEquiv a) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {N : ℕ} (a : ZMod N) {Work : Type}
    (x : Data N) (w : Work) :
    withWorkEquiv a Work (x, w) = (x.addScaled a, w) :=
  rfl

/-- The MAC convention leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {N : ℕ} (a : ZMod N) {Work : Type} :
    WorkRegister.Preserves (Data := Data N) (Work := Work) (withWorkEquiv a Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for multiply-accumulate with an external
work register. -/
def withWorkCleanMap {N : ℕ} (a : ZMod N) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work where
  perm := withWorkEquiv a Work
  preservesWork := withWorkEquiv_preserves_work a

end Data

/-! ### MAC gate wrapper -/

/-- Register whose basis labels are clean multiply-accumulate data states. -/
def register (N : ℕ) [NeZero N] : Register where
  Index := Data N
  fintype := inferInstance
  decEq := inferInstance

/-- The fixed-constant multiply-accumulate gate, represented as a permutation
gate on the clean data-state basis. -/
noncomputable def macGate {N : ℕ} [NeZero N] (a : ZMod N) : Gate (register N) :=
  Gate.ofPerm (Data.macEquiv a).symm

/-- The MAC gate is unitary by construction as a permutation gate. -/
private theorem macGate_mem_unitaryGroup {N : ℕ} [NeZero N] (a : ZMod N) :
    ((macGate a : Gate (register N)) : HilbertOperator (register N))
      ∈ Matrix.unitaryGroup (register N).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Clean basis action of the MAC gate:
`|x,y,0> ↦ |x,y+a*x,0>`. -/
theorem macGate_apply_ket {N : ℕ} [NeZero N] (a : ZMod N) (x : Data N) :
    (macGate a).apply (PureState.ket (R := register N) x) =
      PureState.ket (R := register N) (x.addScaled a) := by
  rw [macGate, Gate.ofPerm_apply_ket]
  rfl

/-! ### Composition from controlled modular additions -/

/-- One controlled modular-addition step in a MAC decomposition. -/
structure ControlledAddStep (N : ℕ) where
  /-- Classical control bit selecting whether this scheduled step is active. -/
  control : Bool
  /-- Addend component of this record. -/
  addend : ZMod N
deriving DecidableEq

namespace ControlledAddStep

/-- Contribution of a controlled-addition step to the accumulator. -/
def contribution {N : ℕ} (step : ControlledAddStep N) : ZMod N :=
  if step.control then step.addend else 0

/-- Apply one controlled modular-addition step to MAC data. The active branch uses
the modular-addition primitive's `addIntoRight` operation. -/
def apply {N : ℕ} (step : ControlledAddStep N) (x : Data N) : Data N :=
  if step.control then
    let addData : ModularAddition.Data N :=
      { left := step.addend, right := x.accumulator, flag := x.flag }
    { multiplicand := x.multiplicand
      accumulator := addData.addIntoRight.right
      flag := addData.addIntoRight.flag }
  else
    x

@[simp] theorem apply_multiplicand {N : ℕ} (step : ControlledAddStep N) (x : Data N) :
    (step.apply x).multiplicand = x.multiplicand := by
  by_cases h : step.control <;> simp [apply, h]

@[simp] theorem apply_flag {N : ℕ} (step : ControlledAddStep N) (x : Data N) :
    (step.apply x).flag = x.flag := by
  by_cases h : step.control <;> simp [apply, h]

@[simp] theorem apply_accumulator {N : ℕ} (step : ControlledAddStep N) (x : Data N) :
    (step.apply x).accumulator = x.accumulator + step.contribution := by
  by_cases h : step.control <;> simp [apply, contribution, h]

/-- Inverse controlled-addition step. -/
def inverse {N : ℕ} (step : ControlledAddStep N) : ControlledAddStep N where
  control := step.control
  addend := -step.addend

@[simp] theorem inverse_control {N : ℕ} (step : ControlledAddStep N) :
    step.inverse.control = step.control :=
  rfl

@[simp] theorem inverse_addend {N : ℕ} (step : ControlledAddStep N) :
    step.inverse.addend = -step.addend :=
  rfl

@[simp] theorem inverse_contribution {N : ℕ} (step : ControlledAddStep N) :
    step.inverse.contribution = -step.contribution := by
  rcases step with ⟨control, addend⟩
  cases control <;> simp [contribution, inverse]

@[simp] theorem inverse_apply_apply {N : ℕ}
    (step : ControlledAddStep N) (x : Data N) :
    step.inverse.apply (step.apply x) = x := by
  ext
  · simp
  · rw [apply_accumulator, apply_accumulator, inverse_contribution]
    abel
  · simp

@[simp] theorem apply_inverse_apply {N : ℕ}
    (step : ControlledAddStep N) (x : Data N) :
    step.apply (step.inverse.apply x) = x := by
  ext
  · simp
  · rw [apply_accumulator, apply_accumulator, inverse_contribution]
    abel
  · simp

/-- Controlled-addition step as a reversible permutation on MAC data. -/
def applyEquiv {N : ℕ} (step : ControlledAddStep N) : Equiv.Perm (Data N) where
  toFun := step.apply
  invFun := step.inverse.apply
  left_inv := by
    intro x
    exact inverse_apply_apply step x
  right_inv := by
    intro x
    exact apply_inverse_apply step x

@[simp] theorem applyEquiv_apply {N : ℕ}
    (step : ControlledAddStep N) (x : Data N) :
    step.applyEquiv x = step.apply x :=
  rfl

/-- Controlled-addition step with an external work register, leaving work
untouched. -/
def withWorkEquiv {N : ℕ} (step : ControlledAddStep N) (Work : Type) :
    Equiv.Perm (Data N × Work) :=
  Equiv.prodCongr step.applyEquiv (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {N : ℕ}
    (step : ControlledAddStep N) {Work : Type} (x : Data N) (w : Work) :
    step.withWorkEquiv Work (x, w) = (step.apply x, w) :=
  rfl

/-- A controlled-addition step leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {N : ℕ}
    (step : ControlledAddStep N) {Work : Type} :
    WorkRegister.Preserves (Data := Data N) (Work := Work) (step.withWorkEquiv Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for one controlled-addition step. -/
def withWorkCleanMap {N : ℕ} (step : ControlledAddStep N) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work where
  perm := step.withWorkEquiv Work
  preservesWork := step.withWorkEquiv_preserves_work

@[simp] theorem withWorkCleanMap_perm_apply {N : ℕ}
    (step : ControlledAddStep N) {Work : Type} (x : Data N) (w : Work) :
    (step.withWorkCleanMap Work).perm (x, w) = (step.apply x, w) :=
  rfl

end ControlledAddStep

/-- Total contribution of a controlled-addition schedule. -/
def scheduleContribution {N : ℕ} : List (ControlledAddStep N) → ZMod N
  | [] => 0
  | step :: rest => step.contribution + scheduleContribution rest

/-- Apply a controlled-addition schedule to MAC data. -/
def applySchedule {N : ℕ} : List (ControlledAddStep N) → Data N → Data N
  | [], x => x
  | step :: rest, x => applySchedule rest (step.apply x)

/-- Clean reversible map for the controlled-addition schedule used in MAC
decompositions of modular multiplication [VBE95, 9511018.tex:333-350]. -/
def scheduleCleanMap {N : ℕ} (steps : List (ControlledAddStep N)) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work :=
  match steps with
  | [] => WorkRegister.CleanReversibleMap.identity (Data N) Work
  | step :: rest =>
      WorkRegister.CleanReversibleMap.sequential
        (ControlledAddStep.withWorkCleanMap step Work)
        (scheduleCleanMap rest Work)

@[simp] theorem scheduleContribution_nil {N : ℕ} :
    scheduleContribution ([] : List (ControlledAddStep N)) = 0 := rfl

@[simp] theorem scheduleContribution_cons {N : ℕ}
    (step : ControlledAddStep N) (rest : List (ControlledAddStep N)) :
    scheduleContribution (step :: rest) =
      step.contribution + scheduleContribution rest := rfl

@[simp] theorem applySchedule_nil {N : ℕ} (x : Data N) :
    applySchedule ([] : List (ControlledAddStep N)) x = x := rfl

@[simp] theorem applySchedule_cons {N : ℕ}
    (step : ControlledAddStep N) (rest : List (ControlledAddStep N)) (x : Data N) :
    applySchedule (step :: rest) x = applySchedule rest (step.apply x) := rfl

theorem applySchedule_multiplicand {N : ℕ}
    (steps : List (ControlledAddStep N)) (x : Data N) :
    (applySchedule steps x).multiplicand = x.multiplicand := by
  induction steps generalizing x with
  | nil => rfl
  | cons step rest ih =>
      simp [applySchedule_cons, ih]

theorem applySchedule_flag {N : ℕ}
    (steps : List (ControlledAddStep N)) (x : Data N) :
    (applySchedule steps x).flag = x.flag := by
  induction steps generalizing x with
  | nil => rfl
  | cons step rest ih =>
      simp [applySchedule_cons, ih]

theorem applySchedule_accumulator {N : ℕ}
    (steps : List (ControlledAddStep N)) (x : Data N) :
    (applySchedule steps x).accumulator =
      x.accumulator + scheduleContribution steps := by
  induction steps generalizing x with
  | nil =>
      simp
  | cons step rest ih =>
      rw [applySchedule_cons, ih, scheduleContribution_cons,
        ControlledAddStep.apply_accumulator]
      abel

@[simp] theorem scheduleCleanMap_perm_apply {N : ℕ}
    (steps : List (ControlledAddStep N)) {Work : Type}
    (x : Data N) (w : Work) :
    (scheduleCleanMap steps Work).perm (x, w) =
      (applySchedule steps x, w) := by
  induction steps generalizing x with
  | nil =>
      rfl
  | cons step rest ih =>
      simp [scheduleCleanMap, applySchedule_cons,
        WorkRegister.CleanReversibleMap.sequential_perm, ih]

/-- A controlled-addition schedule implements the MAC constant `a` for the given
input when its total contribution is `a * multiplicand`. -/
structure CompositionCertificate {N : ℕ} (a : ZMod N) (x : Data N) where
  /-- Ordered schedule of reversible primitive steps used by the composition certificate. -/
  steps : List (ControlledAddStep N)
  contribution_eq : scheduleContribution steps = a * x.multiplicand

namespace CompositionCertificate

/-- Correctness of a controlled-addition schedule whose contribution equals the
selected MAC product. -/
theorem applySchedule_eq_addScaled {N : ℕ} {a : ZMod N} {x : Data N}
    (certificate : CompositionCertificate a x) :
    applySchedule certificate.steps x = x.addScaled a := by
  ext <;>
    simp [applySchedule_multiplicand, applySchedule_flag, applySchedule_accumulator,
      certificate.contribution_eq, Data.addScaled]

/-- Clean reversible map selected by a MAC schedule-composition certificate. -/
def cleanMap {N : ℕ} {a : ZMod N} {x : Data N}
    (certificate : CompositionCertificate a x) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work :=
  scheduleCleanMap certificate.steps Work

/-- The certified controlled-addition schedule clean map realizes the same MAC
action as `Data.addScaled` on its certified input. -/
@[simp] theorem cleanMap_perm_addScaled {N : ℕ} {a : ZMod N} {x : Data N}
    (certificate : CompositionCertificate a x) {Work : Type} (w : Work) :
    (certificate.cleanMap Work).perm (x, w) = (x.addScaled a, w) := by
  simp [cleanMap, certificate.applySchedule_eq_addScaled]

end CompositionCertificate

/-! ### Resource recurrence from controlled modular additions -/

/-- Resource parameters for a MAC implementation built from controlled modular
additions. All fields are concrete profiles supplied by lower-level counting
passes; the recurrence itself contains no asymptotic notation. -/
structure ResourceParameters where
  /-- Bit width parameter for this resource recurrence. -/
  width : ℕ
  /-- Add profile component of this record. -/
  addProfile : ModularArithmeticResourceProfile
  /-- Control overhead component of this record. -/
  controlOverhead : ModularArithmeticResourceProfile
  /-- Constant load profile component of this record. -/
  constantLoadProfile : ModularArithmeticResourceProfile
deriving DecidableEq

namespace ResourceParameters

/-- One controlled-addition step: load/select the constant, apply control
overhead, then run the underlying modular adder. -/
def stepProfile (params : ResourceParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential params.constantLoadProfile
    (ModularArithmeticResourceProfile.sequential params.controlOverhead params.addProfile)

/-- MAC recurrence over the multiplicand bit width. The same live work footprint
is reused across sequential controlled-addition steps. -/
def toProfile (params : ResourceParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.repeatSequential params.width params.stepProfile

@[simp] theorem toProfile_eq_repeatSequential (params : ResourceParameters) :
    params.toProfile =
      ModularArithmeticResourceProfile.repeatSequential params.width params.stepProfile :=
  rfl

@[simp] theorem stepProfile_logicalQubits (params : ResourceParameters) :
    params.stepProfile.logicalQubits =
      max params.constantLoadProfile.logicalQubits
        (max params.controlOverhead.logicalQubits params.addProfile.logicalQubits) :=
  rfl

@[simp] theorem stepProfile_workQubits (params : ResourceParameters) :
    params.stepProfile.workQubits =
      max params.constantLoadProfile.workQubits
        (max params.controlOverhead.workQubits params.addProfile.workQubits) :=
  rfl

@[simp] theorem stepProfile_toffoliGates (params : ResourceParameters) :
    params.stepProfile.toffoliGates =
      params.constantLoadProfile.toffoliGates +
        (params.controlOverhead.toffoliGates + params.addProfile.toffoliGates) :=
  rfl

@[simp] theorem stepProfile_circuitDepth (params : ResourceParameters) :
    params.stepProfile.circuitDepth =
      params.constantLoadProfile.circuitDepth +
        (params.controlOverhead.circuitDepth + params.addProfile.circuitDepth) :=
  rfl

private theorem toProfile_zero_width (params : ResourceParameters)
    (h : params.width = 0) :
    params.toProfile = ModularArithmeticResourceProfile.zero := by
  cases params
  cases h
  rfl

/-- Concrete bounds for a MAC resource profile assembled from one controlled
modular-addition step repeated over the multiplicand width. -/
structure PublicBaselineBounds where
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ℕ
  /-- Qubit-count component for data qubits. -/
  dataQubits : ℕ
  /-- Qubit-count component for work qubits. -/
  workQubits : ℕ
  /-- Oracle-query count component for oracle queries. -/
  oracleQueries : ℕ
  /-- Gate-count component for Hadamard gates. -/
  hadamardGates : ℕ
  /-- Gate-count component for Toffoli gates. -/
  toffoliGates : ℕ
  /-- Gate-count component for T gates. -/
  tGates : ℕ
  /-- Gate-count component for CNOT gates. -/
  cnotGates : ℕ
  /-- Gate-count component for single-qubit gates. -/
  singleQubitGates : ℕ
  /-- Depth component for circuit depth. -/
  circuitDepth : ℕ
  /-- Depth component for Toffoli depth. -/
  toffoliDepth : ℕ
  /-- Classical-operation count for classical operations. -/
  classicalOps : ℕ
deriving DecidableEq

namespace PublicBaselineBounds

/-- Source-facing bound profile for the MAC recurrence. A scalar classical
operation bound is carried in the control/rewrite family until a source-specific
breakdown is available. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile where
  logicalQubits := bounds.logicalQubits
  dataQubits := bounds.dataQubits
  workQubits := bounds.workQubits
  oracleQueries := bounds.oracleQueries
  hadamardGates := bounds.hadamardGates
  toffoliGates := bounds.toffoliGates
  tGates := bounds.tGates
  cnotGates := bounds.cnotGates
  singleQubitGates := bounds.singleQubitGates
  circuitDepth := bounds.circuitDepth
  toffoliDepth := bounds.toffoliDepth
  classicalArithmetic := ClassicalArithmeticProfile.ofControlRewriteOps bounds.classicalOps

/-- Explicit source-count bounds for one controlled-addition step and the
positive bit width over which it is repeated. -/
structure FormulaParameters where
  /-- Bit width parameter for this resource recurrence. -/
  width : ℕ
  /-- Qubit-count component for step logical qubits. -/
  stepLogicalQubits : ℕ
  /-- Qubit-count component for step data qubits. -/
  stepDataQubits : ℕ
  /-- Qubit-count component for step work qubits. -/
  stepWorkQubits : ℕ
  /-- Oracle-query count component for step oracle queries. -/
  stepOracleQueries : ℕ
  /-- Gate-count component for step Hadamard gates. -/
  stepHadamardGates : ℕ
  /-- Gate-count component for step toffoli gates. -/
  stepToffoliGates : ℕ
  /-- Gate-count component for step T gates. -/
  stepTGates : ℕ
  /-- Gate-count component for step CNOT gates. -/
  stepCNOTGates : ℕ
  /-- Gate-count component for step single-qubit gates. -/
  stepSingleQubitGates : ℕ
  /-- Depth component for step circuit depth. -/
  stepCircuitDepth : ℕ
  /-- Depth component for step toffoli depth. -/
  stepToffoliDepth : ℕ
  /-- Classical-operation count for step classical operations. -/
  stepClassicalOps : ℕ
deriving DecidableEq

namespace FormulaParameters

/-- Bounds induced by repeating the same step for each multiplicand bit. The
live footprint is reused; counted gates, depth, and classical operations scale
by `width`. -/
def toPublicBaselineBounds (bounds : FormulaParameters) : PublicBaselineBounds where
  logicalQubits := bounds.stepLogicalQubits
  dataQubits := bounds.stepDataQubits
  workQubits := bounds.stepWorkQubits
  oracleQueries := bounds.width * bounds.stepOracleQueries
  hadamardGates := bounds.width * bounds.stepHadamardGates
  toffoliGates := bounds.width * bounds.stepToffoliGates
  tGates := bounds.width * bounds.stepTGates
  cnotGates := bounds.width * bounds.stepCNOTGates
  singleQubitGates := bounds.width * bounds.stepSingleQubitGates
  circuitDepth := bounds.width * bounds.stepCircuitDepth
  toffoliDepth := bounds.width * bounds.stepToffoliDepth
  classicalOps := bounds.width * bounds.stepClassicalOps

end FormulaParameters

end PublicBaselineBounds

/-- The exact MAC recurrence supports concrete source bounds when the repeated
step profile is bounded fieldwise and the multiplicand width is positive. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits
  dataQubits_le : profile.dataQubits ≤ bounds.dataQubits
  workQubits_le : profile.workQubits ≤ bounds.workQubits
  oracleQueries_le : profile.oracleQueries ≤ bounds.oracleQueries
  hadamardGates_le : profile.hadamardGates ≤ bounds.hadamardGates
  toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates
  tGates_le : profile.tGates ≤ bounds.tGates
  cnotGates_le : profile.cnotGates ≤ bounds.cnotGates
  singleQubitGates_le : profile.singleQubitGates ≤ bounds.singleQubitGates
  circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth
  toffoliDepth_le : profile.toffoliDepth ≤ bounds.toffoliDepth
  classicalOps_le : profile.classicalArithmetic.total ≤ bounds.classicalOps

/-- A MAC public-baseline certificate gives the generic modular-arithmetic
upper-bound relation used by higher-level composition layers. -/
theorem SupportsPublicBaseline.supportsUpperBound
    {profile : ModularArithmeticResourceProfile} {bounds : PublicBaselineBounds}
    (cert : SupportsPublicBaseline profile bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound profile bounds.toProfile where
  logicalQubits_le := cert.logicalQubits_le
  dataQubits_le := cert.dataQubits_le
  workQubits_le := cert.workQubits_le
  oracleQueries_le := cert.oracleQueries_le
  hadamardGates_le := cert.hadamardGates_le
  toffoliGates_le := cert.toffoliGates_le
  tGates_le := cert.tGates_le
  cnotGates_le := cert.cnotGates_le
  singleQubitGates_le := cert.singleQubitGates_le
  circuitDepth_le := cert.circuitDepth_le
  toffoliDepth_le := cert.toffoliDepth_le
  classicalOps_le := by
    simpa [PublicBaselineBounds.toProfile] using cert.classicalOps_le

/-- Build a MAC source-bound certificate from one-step bounds and a positive
multiplicand width. -/
theorem supportsPublicBaseline_of_stepBounds
    {params : ResourceParameters}
    {bounds : PublicBaselineBounds.FormulaParameters}
    (hwidth : params.width = bounds.width)
    (hwidth_pos : 0 < bounds.width)
    (hlogical : params.stepProfile.logicalQubits ≤ bounds.stepLogicalQubits)
    (hdata : params.stepProfile.dataQubits ≤ bounds.stepDataQubits)
    (hwork : params.stepProfile.workQubits ≤ bounds.stepWorkQubits)
    (horacle : params.stepProfile.oracleQueries ≤ bounds.stepOracleQueries)
    (hhadamard : params.stepProfile.hadamardGates ≤ bounds.stepHadamardGates)
    (htoffoli : params.stepProfile.toffoliGates ≤ bounds.stepToffoliGates)
    (ht : params.stepProfile.tGates ≤ bounds.stepTGates)
    (hcnot : params.stepProfile.cnotGates ≤ bounds.stepCNOTGates)
    (hsingle : params.stepProfile.singleQubitGates ≤ bounds.stepSingleQubitGates)
    (hdepth : params.stepProfile.circuitDepth ≤ bounds.stepCircuitDepth)
    (htoffoliDepth : params.stepProfile.toffoliDepth ≤ bounds.stepToffoliDepth)
    (hclassical : params.stepProfile.classicalArithmetic.total ≤ bounds.stepClassicalOps) :
    SupportsPublicBaseline params.toProfile bounds.toPublicBaselineBounds := by
  rcases bounds with
    ⟨width, stepLogicalQubits, stepDataQubits, stepWorkQubits, stepOracleQueries,
      stepHadamardGates, stepToffoliGates, stepTGates, stepCNOTGates,
      stepSingleQubitGates, stepCircuitDepth, stepToffoliDepth, stepClassicalOps⟩
  cases width with
  | zero => cases hwidth_pos
  | succ k =>
      refine
        { logicalQubits_le := ?_
          dataQubits_le := ?_
          workQubits_le := ?_
          oracleQueries_le := ?_
          hadamardGates_le := ?_
          toffoliGates_le := ?_
          tGates_le := ?_
          cnotGates_le := ?_
          singleQubitGates_le := ?_
          circuitDepth_le := ?_
          toffoliDepth_le := ?_
          classicalOps_le := ?_ }
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using hlogical
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using hdata
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using hwork
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) horacle
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) hhadamard
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) htoffoli
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) ht
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) hcnot
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) hsingle
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) hdepth
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) htoffoliDepth
      · rw [toProfile_eq_repeatSequential, hwidth]
        simpa [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds] using
          Nat.mul_le_mul_left (k + 1) hclassical

/-- Direct generic upper-bound certificate from explicit MAC source-count
bounds. -/
private theorem supportsUpperBound_of_stepBounds
    {params : ResourceParameters}
    {bounds : PublicBaselineBounds.FormulaParameters}
    (hwidth : params.width = bounds.width)
    (hwidth_pos : 0 < bounds.width)
    (hlogical : params.stepProfile.logicalQubits ≤ bounds.stepLogicalQubits)
    (hdata : params.stepProfile.dataQubits ≤ bounds.stepDataQubits)
    (hwork : params.stepProfile.workQubits ≤ bounds.stepWorkQubits)
    (horacle : params.stepProfile.oracleQueries ≤ bounds.stepOracleQueries)
    (hhadamard : params.stepProfile.hadamardGates ≤ bounds.stepHadamardGates)
    (htoffoli : params.stepProfile.toffoliGates ≤ bounds.stepToffoliGates)
    (ht : params.stepProfile.tGates ≤ bounds.stepTGates)
    (hcnot : params.stepProfile.cnotGates ≤ bounds.stepCNOTGates)
    (hsingle : params.stepProfile.singleQubitGates ≤ bounds.stepSingleQubitGates)
    (hdepth : params.stepProfile.circuitDepth ≤ bounds.stepCircuitDepth)
    (htoffoliDepth : params.stepProfile.toffoliDepth ≤ bounds.stepToffoliDepth)
    (hclassical : params.stepProfile.classicalArithmetic.total ≤ bounds.stepClassicalOps) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.toProfile bounds.toPublicBaselineBounds.toProfile :=
  (supportsPublicBaseline_of_stepBounds hwidth hwidth_pos hlogical hdata hwork
    horacle hhadamard htoffoli ht hcnot hsingle hdepth htoffoliDepth
    hclassical).supportsUpperBound

end ResourceParameters

/-! ### Source-backed VBE package for repeated controlled additions -/

namespace VBECounting

/-- Formula parameters for the VBE controlled-addition step reused by the MAC
package. -/
def controlledADDStepFormulaParameters (n : ℕ) :
    ModularAddition.ResourceParameters.PublicBaselineBounds.FormulaParameters :=
  ModularAddition.VBECounting.vbeControlledADDStepFormulaParameters n

/-- Public baseline bounds for the VBE controlled-addition step reused by MAC. -/
def controlledADDStepBounds (n : ℕ) :
    ModularAddition.ResourceParameters.PublicBaselineBounds :=
  (controlledADDStepFormulaParameters n).toPublicBaselineBounds

/-- Canonical VBE MAC resource parameters obtained by repeating the VBE
controlled modular-addition step. -/
def vbeMACResourceParameters (n : ℕ) : ResourceParameters where
  width := n
  addProfile :=
    (ModularAddition.VBECounting.vbeControlledADDStepResourceParameters n).toProfile n
  controlOverhead := ModularArithmeticResourceProfile.zero
  constantLoadProfile := ModularArithmeticResourceProfile.zero

/-- Canonical VBE MAC formula parameters induced by the VBE controlled-addition
step package. -/
def vbeMACFormulaParameters (n : ℕ) :
    ResourceParameters.PublicBaselineBounds.FormulaParameters where
  width := n
  stepLogicalQubits := (controlledADDStepBounds n).logicalQubits
  stepDataQubits := (controlledADDStepBounds n).dataQubits
  stepWorkQubits := (controlledADDStepBounds n).workQubits
  stepOracleQueries := 0
  stepHadamardGates := 0
  stepToffoliGates := (controlledADDStepBounds n).toffoliGates
  stepTGates := (controlledADDStepBounds n).tGates
  stepCNOTGates := (controlledADDStepBounds n).cnotGates
  stepSingleQubitGates := (controlledADDStepBounds n).singleQubitGates
  stepCircuitDepth := (controlledADDStepBounds n).circuitDepth
  stepToffoliDepth := (controlledADDStepBounds n).toffoliDepth
  stepClassicalOps := 0

@[simp] theorem vbeMACFormulaParameters_width (n : ℕ) :
    (vbeMACFormulaParameters n).width = n :=
  rfl

/-- The canonical VBE MAC package satisfies its public baseline bounds without
caller-supplied MAC step profiles. -/
theorem vbeMACSupportsPublicBaseline (n : ℕ) (hpos : 0 < n) :
    ResourceParameters.SupportsPublicBaseline
      (vbeMACResourceParameters n).toProfile
      (vbeMACFormulaParameters n).toPublicBaselineBounds := by
  have hadd :=
    ModularAddition.VBECounting.vbeControlledADDSupportsPublicBaseline n
  apply ResourceParameters.supportsPublicBaseline_of_stepBounds
  · rfl
  · simpa [vbeMACFormulaParameters] using hpos
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.logicalQubits_le
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.dataQubits_le
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.workQubits_le
  · simp [vbeMACResourceParameters, vbeMACFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero]
  · simp [vbeMACResourceParameters, vbeMACFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero]
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.toffoliGates_le
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.tGates_le
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.cnotGates_le
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.singleQubitGates_le
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.circuitDepth_le
  · simpa [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepBounds, controlledADDStepFormulaParameters,
      ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero] using
      hadd.toffoliDepth_le
  · norm_num [vbeMACResourceParameters, vbeMACFormulaParameters,
      controlledADDStepFormulaParameters, ResourceParameters.stepProfile,
      ModularAddition.ResourceParameters.toProfile,
      ModularArithmeticResourceProfile.sequential, ModularArithmeticResourceProfile.zero,
      ClassicalArithmeticProfile.total, ClassicalArithmeticProfile.sequential,
      ClassicalArithmeticProfile.zero, BitIntegerOperationProfile.total,
      BitIntegerOperationProfile.sequential, BitIntegerOperationProfile.zero,
      NumberTheoreticOperationProfile.total, NumberTheoreticOperationProfile.sequential,
      NumberTheoreticOperationProfile.zero, ModularFieldOperationProfile.total,
      ModularFieldOperationProfile.sequential, ModularFieldOperationProfile.zero,
      GroupControlOperationProfile.total, GroupControlOperationProfile.sequential,
      GroupControlOperationProfile.zero]

end VBECounting

/-! ### Circuit witness -/

namespace ResourceParameters

/-- Typed circuit witness for a fixed-constant modular multiply-accumulate
operation. The interpreted gate and the projected resource profile are carried
by the same `Circuit` object. -/
noncomputable def macCircuit {N : ℕ} [NeZero N] (a : ZMod N)
    (params : ResourceParameters) : Circuit (register N) :=
  Circuit.ofGate "modular-multiply-accumulate" (macGate a)
    params.toProfile.toResourceProfile params.toProfile.circuitDepth
    params.toProfile.oracleQueries

@[simp] theorem macCircuit_resources {N : ℕ} [NeZero N] (a : ZMod N)
    (params : ResourceParameters) :
    (macCircuit a params).resources = params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem macCircuit_depth {N : ℕ} [NeZero N] (a : ZMod N)
    (params : ResourceParameters) :
    (macCircuit a params).depth = params.toProfile.circuitDepth :=
  rfl

/-- Basis-state correctness for the typed MAC circuit witness. -/
theorem macCircuit_apply_ket {N : ℕ} [NeZero N] (a : ZMod N)
    (params : ResourceParameters) (x : Data N) :
    Circuit.apply (macCircuit a params)
      (PureState.ket (R := register N) x : StateVector (register N)) =
      (PureState.ket (R := register N) (x.addScaled a) :
        StateVector (register N)) := by
  simpa [macCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register N) => (psi : StateVector (register N)))
      (macGate_apply_ket a x)

/-- Clean basis action of the typed MAC circuit:
`|x,y,0> ↦ |x,y+a*x,0>` over `ZMod N`. -/
theorem macCircuit_apply_clean_ket {N : ℕ} [NeZero N] (a : ZMod N)
    (params : ResourceParameters) (x y : ZMod N) :
    Circuit.apply (macCircuit a params)
      (PureState.ket (R := register N)
        ({ multiplicand := x, accumulator := y, flag := false } : Data N) :
          StateVector (register N)) =
      (PureState.ket (R := register N)
        ({ multiplicand := x, accumulator := y + a * x, flag := false } : Data N) :
          StateVector (register N)) := by
  simpa [Data.addScaled] using
    macCircuit_apply_ket a params
      ({ multiplicand := x, accumulator := y, flag := false } : Data N)

/-- Correctness/resource proof package for a MAC circuit witness. -/
noncomputable def macCircuitResourceCorrectWitness {N : ℕ} [NeZero N]
    (a : ZMod N) (params : ResourceParameters) :
    ResourceCorrectWitness (R := register N)
      (∀ x : Data N,
        Circuit.apply (macCircuit a params)
          (PureState.ket (R := register N) x : StateVector (register N)) =
          (PureState.ket (R := register N) (x.addScaled a) :
            StateVector (register N)))
      ((macCircuit a params).resources = params.toProfile.toResourceProfile) where
  circuit := macCircuit a params
  correctness := by
    intro x
    exact macCircuit_apply_ket a params x
  resources := by
    rfl

/-! #### External work-register clean interface -/

/-- MAC as an external-work clean reversible circuit. The clean map, semantic
action, and projected resource profile are all attached to the same typed
`Circuit`. -/
noncomputable def macWithWorkCircuit {N : ℕ} [NeZero N] (a : ZMod N)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data N) Work) :=
  (Data.withWorkCleanMap a Work).circuit params.toProfile

@[simp] theorem macWithWorkCircuit_resources {N : ℕ} [NeZero N] (a : ZMod N)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (macWithWorkCircuit a Work params).resources =
      params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem macWithWorkCircuit_depth {N : ℕ} [NeZero N] (a : ZMod N)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (macWithWorkCircuit a Work params).depth = params.toProfile.circuitDepth :=
  rfl

@[simp] theorem macWithWorkCircuit_queryDepth {N : ℕ} [NeZero N] (a : ZMod N)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (macWithWorkCircuit a Work params).queryDepth = params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for MAC with an external work register. -/
theorem macWithWorkCircuit_apply_ket {N : ℕ} [NeZero N] (a : ZMod N)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : Data N) (w : Work) :
    Circuit.apply (macWithWorkCircuit a Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (x.addScaled a, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [macWithWorkCircuit, Data.withWorkCleanMap] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := Data.withWorkCleanMap a Work)
      (profile := params.toProfile) (x := (x, w))

/-- Clean basis action of the external-work MAC circuit:
`|x,y,0,w> ↦ |x,y+a*x,0,w>` over `ZMod N`. -/
private theorem macWithWorkCircuit_apply_clean_ket {N : ℕ} [NeZero N] (a : ZMod N)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x y : ZMod N) (w : Work) :
    Circuit.apply (macWithWorkCircuit a Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ multiplicand := x, accumulator := y, flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ multiplicand := x, accumulator := y + a * x, flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [Data.addScaled] using
    macWithWorkCircuit_apply_ket a Work params
      ({ multiplicand := x, accumulator := y, flag := false } : Data N) w

/-- Resource-correct witness for the external-work MAC circuit. -/
noncomputable def macWithWorkCircuitResourceCorrectWitness
    {N : ℕ} [NeZero N] (a : ZMod N)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
      (∀ x : Data N, ∀ w : Work,
        Circuit.apply (macWithWorkCircuit a Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
              (x.addScaled a, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)))
      ((macWithWorkCircuit a Work params).resources =
          params.toProfile.toResourceProfile ∧
        (macWithWorkCircuit a Work params).depth = params.toProfile.circuitDepth ∧
        (macWithWorkCircuit a Work params).queryDepth = params.toProfile.oracleQueries) := by
  exact
    { circuit := macWithWorkCircuit a Work params
      correctness := fun x w => macWithWorkCircuit_apply_ket a Work params x w
      resources := ⟨rfl, rfl, rfl⟩ }

/-- MAC support endpoint with explicit natural-number resource bounds. This is
the bounded bridge consumed by modular multiplication and exponentiation
composition layers. -/
private theorem main_with_public_bounds {N : ℕ} [NeZero N] (a : ZMod N)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (hwidth : params.width = bounds.width)
    (hwidth_pos : 0 < bounds.width)
    (hlogical : params.stepProfile.logicalQubits ≤ bounds.stepLogicalQubits)
    (hdata : params.stepProfile.dataQubits ≤ bounds.stepDataQubits)
    (hwork : params.stepProfile.workQubits ≤ bounds.stepWorkQubits)
    (horacle : params.stepProfile.oracleQueries ≤ bounds.stepOracleQueries)
    (hhadamard : params.stepProfile.hadamardGates ≤ bounds.stepHadamardGates)
    (htoffoli : params.stepProfile.toffoliGates ≤ bounds.stepToffoliGates)
    (ht : params.stepProfile.tGates ≤ bounds.stepTGates)
    (hcnot : params.stepProfile.cnotGates ≤ bounds.stepCNOTGates)
    (hsingle : params.stepProfile.singleQubitGates ≤ bounds.stepSingleQubitGates)
    (hdepth : params.stepProfile.circuitDepth ≤ bounds.stepCircuitDepth)
    (htoffoliDepth : params.stepProfile.toffoliDepth ≤ bounds.stepToffoliDepth)
    (hclassical : params.stepProfile.classicalArithmetic.total ≤ bounds.stepClassicalOps) :
    (∀ x y : ZMod N,
      Circuit.apply (macCircuit a params)
        (PureState.ket (R := register N)
          ({ multiplicand := x, accumulator := y, flag := false } : Data N) :
            StateVector (register N)) =
        (PureState.ket (R := register N)
          ({ multiplicand := x, accumulator := y + a * x, flag := false } : Data N) :
            StateVector (register N))) ∧
      SupportsPublicBaseline params.toProfile bounds.toPublicBaselineBounds ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        params.toProfile bounds.toPublicBaselineBounds.toProfile ∧
      (macCircuit a params).resources = params.toProfile.toResourceProfile ∧
      (macCircuit a params).depth = params.toProfile.circuitDepth := by
  have hbaseline :=
    supportsPublicBaseline_of_stepBounds hwidth hwidth_pos hlogical hdata hwork
      horacle hhadamard htoffoli ht hcnot hsingle hdepth htoffoliDepth
      hclassical
  constructor
  · intro x y
    exact macCircuit_apply_clean_ket a params x y
  constructor
  · exact hbaseline
  constructor
  · exact hbaseline.supportsUpperBound
  · exact ⟨rfl, rfl⟩

/-- Resource-correct witness for the bounded MAC support endpoint. -/
private noncomputable def mainWithPublicBoundsResourceCorrectWitness
    {N : ℕ} [NeZero N] (a : ZMod N)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (hwidth : params.width = bounds.width)
    (hwidth_pos : 0 < bounds.width)
    (hlogical : params.stepProfile.logicalQubits ≤ bounds.stepLogicalQubits)
    (hdata : params.stepProfile.dataQubits ≤ bounds.stepDataQubits)
    (hwork : params.stepProfile.workQubits ≤ bounds.stepWorkQubits)
    (horacle : params.stepProfile.oracleQueries ≤ bounds.stepOracleQueries)
    (hhadamard : params.stepProfile.hadamardGates ≤ bounds.stepHadamardGates)
    (htoffoli : params.stepProfile.toffoliGates ≤ bounds.stepToffoliGates)
    (ht : params.stepProfile.tGates ≤ bounds.stepTGates)
    (hcnot : params.stepProfile.cnotGates ≤ bounds.stepCNOTGates)
    (hsingle : params.stepProfile.singleQubitGates ≤ bounds.stepSingleQubitGates)
    (hdepth : params.stepProfile.circuitDepth ≤ bounds.stepCircuitDepth)
    (htoffoliDepth : params.stepProfile.toffoliDepth ≤ bounds.stepToffoliDepth)
    (hclassical : params.stepProfile.classicalArithmetic.total ≤ bounds.stepClassicalOps) :
    ResourceCorrectWitness (R := register N)
      (∀ x y : ZMod N,
        Circuit.apply (macCircuit a params)
          (PureState.ket (R := register N)
            ({ multiplicand := x, accumulator := y, flag := false } : Data N) :
              StateVector (register N)) =
          (PureState.ket (R := register N)
            ({ multiplicand := x, accumulator := y + a * x, flag := false } : Data N) :
              StateVector (register N)))
      (SupportsPublicBaseline params.toProfile bounds.toPublicBaselineBounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          params.toProfile bounds.toPublicBaselineBounds.toProfile ∧
        (macCircuit a params).resources = params.toProfile.toResourceProfile ∧
        (macCircuit a params).depth = params.toProfile.circuitDepth) := by
  have hmain :=
    main_with_public_bounds a params bounds hwidth hwidth_pos hlogical hdata hwork
      horacle hhadamard htoffoli ht hcnot hsingle hdepth htoffoliDepth
      hclassical
  exact
    { circuit := macCircuit a params
      correctness := hmain.1
      resources := ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2⟩ }

end ResourceParameters

end ModularMultiplyAccumulate
end QuantumAlg
