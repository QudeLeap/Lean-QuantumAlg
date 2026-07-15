/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.CleanInterface
public import QuantumAlg.Primitives.Arithmetic.PlainAdder
public import Mathlib.Tactic

/-!
# Reversible modular addition

This module records the clean reversible map for modular addition over `ZMod N`
and the arithmetic lemma behind the compare/subtract/add-back route: for
canonical representatives, subtracting `N` exactly when the plain sum overflows
computes reduction modulo `N`.

The clean modular-addition route follows the reversible compare/subtract/add-back
network used in elementary arithmetic constructions [VBE95,
9511018.tex:274-316, 634-643]. Beauregard's Fourier-space variant is tracked as
a source route but remains separate from the exact-count endpoint until its
approximation policy is discharged [Bea02, arxivfact.tex:97-118].
-/

@[expose] public section

namespace QuantumAlg
namespace ModularAddition

/-- Data registers for an in-place modular adder. The clean flag represents the
temporary comparison/borrow information after uncomputation. -/
structure Data (N : ℕ) where
  /-- Left data register component. -/
  left : ZMod N
  /-- Right data register component. -/
  right : ZMod N
  /-- Clean control or comparison flag component. -/
  flag : Bool
deriving DecidableEq

instance instFintypeData (N : ℕ) [NeZero N] : Fintype (Data N) := by
  classical
  let e : Data N ≃ (ZMod N × ZMod N × Bool) := {
    toFun := fun x => (x.left, (x.right, x.flag))
    invFun := fun x => { left := x.1, right := x.2.1, flag := x.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨left, rest⟩
      rcases rest with ⟨right, flag⟩
      rfl
  }
  exact Fintype.ofEquiv (ZMod N × ZMod N × Bool) e.symm

namespace Data

/-- The clean flag convention for modular addition. -/
def FlagClean {N : ℕ} (x : Data N) : Prop :=
  x.flag = false

/-- Add the left residue into the right residue modulo `N`, preserving the flag. -/
def addIntoRight {N : ℕ} (x : Data N) : Data N where
  left := x.left
  right := x.right + x.left
  flag := x.flag

/-- Inverse operation for the modular adder. -/
def subFromRight {N : ℕ} (x : Data N) : Data N where
  left := x.left
  right := x.right - x.left
  flag := x.flag

@[simp] theorem addIntoRight_left {N : ℕ} (x : Data N) :
    x.addIntoRight.left = x.left :=
  rfl

@[simp] theorem addIntoRight_right {N : ℕ} (x : Data N) :
    x.addIntoRight.right = x.right + x.left :=
  rfl

@[simp] theorem addIntoRight_flag {N : ℕ} (x : Data N) :
    x.addIntoRight.flag = x.flag :=
  rfl

@[simp] theorem subFromRight_left {N : ℕ} (x : Data N) :
    x.subFromRight.left = x.left :=
  rfl

@[simp] theorem subFromRight_right {N : ℕ} (x : Data N) :
    x.subFromRight.right = x.right - x.left :=
  rfl

@[simp] theorem subFromRight_flag {N : ℕ} (x : Data N) :
    x.subFromRight.flag = x.flag :=
  rfl

/-- Clean temporary flags remain clean after modular addition. -/
theorem addIntoRight_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.addIntoRight.FlagClean :=
  h

/-- Clean temporary flags remain clean after modular subtraction. -/
theorem subFromRight_preserves_clean {N : ℕ} (x : Data N)
    (h : x.FlagClean) : x.subFromRight.FlagClean :=
  h

/-- Modular addition as a reversible permutation on residue data registers. -/
def addEquiv (N : ℕ) : Equiv.Perm (Data N) where
  toFun := addIntoRight
  invFun := subFromRight
  left_inv := by
    intro x
    cases x
    simp [addIntoRight, subFromRight]
  right_inv := by
    intro x
    cases x
    simp [addIntoRight, subFromRight]

@[simp] theorem addEquiv_apply {N : ℕ} (x : Data N) :
    addEquiv N x = x.addIntoRight :=
  rfl

/-- Modular addition with an external work register, leaving the work untouched. -/
def withWorkEquiv (N : ℕ) (Work : Type) : Equiv.Perm (Data N × Work) :=
  Equiv.prodCongr (addEquiv N) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {N : ℕ} {Work : Type} (x : Data N) (w : Work) :
    withWorkEquiv N Work (x, w) = (x.addIntoRight, w) :=
  rfl

/-- The modular adder leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {N : ℕ} {Work : Type} :
    WorkRegister.Preserves (Data := Data N) (Work := Work) (withWorkEquiv N Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for modular addition with an external work
register. -/
def withWorkCleanMap (N : ℕ) (Work : Type) :
    WorkRegister.CleanReversibleMap (Data N) Work where
  perm := withWorkEquiv N Work
  preservesWork := withWorkEquiv_preserves_work

end Data

/-! ### ADD_N gate wrapper -/

/-- Register whose basis labels are clean modular-addition data states. -/
def register (N : ℕ) [NeZero N] : Register where
  Index := Data N
  fintype := inferInstance
  decEq := inferInstance

/-- The modular-addition gate `ADD_N`, represented as a permutation gate on the
clean data-state basis. -/
noncomputable def addGate (N : ℕ) [NeZero N] : Gate (register N) :=
  Gate.ofPerm (Data.addEquiv N).symm

/-- The modular-addition gate is unitary by construction as a permutation gate. -/
theorem addGate_mem_unitaryGroup (N : ℕ) [NeZero N] :
    ((addGate N : Gate (register N)) : HilbertOperator (register N))
      ∈ Matrix.unitaryGroup (register N).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Clean basis action of `ADD_N`: `|a,b,0> ↦ |a,a+b mod N,0>`. -/
theorem addGate_apply_ket (N : ℕ) [NeZero N] (x : Data N) :
    (addGate N).apply (PureState.ket (R := register N) x) =
      PureState.ket (R := register N) x.addIntoRight := by
  rw [addGate, Gate.ofPerm_apply_ket]
  rfl

/-! ### Exact-resource profile parameters -/

/-- Concrete resource parameters for an `ADD_N` implementation. These are
placeholders for exact counts or explicit upper-bound functions supplied by a
source-backed counting pass; no asymptotic notation is represented here. -/
structure ResourceParameters where
  /-- Qubit-count component for work qubits. -/
  workQubits : ℕ
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
deriving DecidableEq

namespace ResourceParameters

/-- Convert `ADD_N` resource parameters into the modular-arithmetic profile
for two `n`-bit data registers plus one clean flag. -/
def toProfile (n : ℕ) (params : ResourceParameters) : ModularArithmeticResourceProfile where
  logicalQubits := 2 * n + 1 + params.workQubits
  dataQubits := 2 * n + 1
  workQubits := params.workQubits
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := params.toffoliGates
  tGates := params.tGates
  cnotGates := params.cnotGates
  singleQubitGates := params.singleQubitGates
  circuitDepth := params.circuitDepth
  toffoliDepth := params.toffoliDepth
  classicalArithmetic := ClassicalArithmeticProfile.zero

@[simp] theorem toProfile_logicalQubits (n : ℕ) (params : ResourceParameters) :
    (params.toProfile n).logicalQubits = 2 * n + 1 + params.workQubits :=
  rfl

@[simp] theorem toProfile_dataQubits (n : ℕ) (params : ResourceParameters) :
    (params.toProfile n).dataQubits = 2 * n + 1 :=
  rfl

@[simp] theorem toProfile_workQubits (n : ℕ) (params : ResourceParameters) :
    (params.toProfile n).workQubits = params.workQubits :=
  rfl

@[simp] theorem toProfile_oracleQueries (n : ℕ) (params : ResourceParameters) :
    (params.toProfile n).oracleQueries = 0 :=
  rfl

@[simp] theorem toProfile_classicalArithmetic (n : ℕ) (params : ResourceParameters) :
    (params.toProfile n).classicalArithmetic = ClassicalArithmeticProfile.zero :=
  rfl

/-- Concrete bounds for an `ADD_N` implementation profile. -/
structure PublicBaselineBounds where
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ℕ
  /-- Qubit-count component for data qubits. -/
  dataQubits : ℕ
  /-- Qubit-count component for work qubits. -/
  workQubits : ℕ
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
deriving DecidableEq

namespace PublicBaselineBounds

/-- Source-facing bound profile for `ADD_N`. Classical arithmetic is zero at
this reversible circuit layer; post-processing counts are attached by callers. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile where
  logicalQubits := bounds.logicalQubits
  dataQubits := bounds.dataQubits
  workQubits := bounds.workQubits
  oracleQueries := 0
  hadamardGates := 0
  toffoliGates := bounds.toffoliGates
  tGates := bounds.tGates
  cnotGates := bounds.cnotGates
  singleQubitGates := bounds.singleQubitGates
  circuitDepth := bounds.circuitDepth
  toffoliDepth := bounds.toffoliDepth
  classicalArithmetic := ClassicalArithmeticProfile.zero

/-- Explicit natural-number bounds for a modular adder over `n`-bit residues. -/
structure FormulaParameters where
  /-- Bit width parameter for this resource recurrence. -/
  width : ℕ
  /-- Explicit upper bound for the work qubit component. -/
  workQubitBound : ℕ
  /-- Explicit upper bound for the Toffoli-gate component. -/
  toffoliGateBound : ℕ
  /-- Explicit upper bound for the T gate component. -/
  tGateBound : ℕ
  /-- Explicit upper bound for the CNOT-gate component. -/
  cnotGateBound : ℕ
  /-- Explicit upper bound for the single qubit gate component. -/
  singleQubitGateBound : ℕ
  /-- Explicit upper bound for the circuit depth component. -/
  circuitDepthBound : ℕ
  /-- Explicit upper bound for the Toffoli-depth component. -/
  toffoliDepthBound : ℕ
deriving DecidableEq

namespace FormulaParameters

/-- Bounds induced by the selected modular-adder width and gate-count bounds. -/
def toPublicBaselineBounds (bounds : FormulaParameters) : PublicBaselineBounds where
  logicalQubits := 2 * bounds.width + 1 + bounds.workQubitBound
  dataQubits := 2 * bounds.width + 1
  workQubits := bounds.workQubitBound
  toffoliGates := bounds.toffoliGateBound
  tGates := bounds.tGateBound
  cnotGates := bounds.cnotGateBound
  singleQubitGates := bounds.singleQubitGateBound
  circuitDepth := bounds.circuitDepthBound
  toffoliDepth := bounds.toffoliDepthBound

end FormulaParameters

end PublicBaselineBounds

/-- The exact `ADD_N` profile supports concrete source bounds when every field
is bounded by its corresponding explicit natural-number bound. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits
  dataQubits_le : profile.dataQubits ≤ bounds.dataQubits
  workQubits_le : profile.workQubits ≤ bounds.workQubits
  toffoliGates_le : profile.toffoliGates ≤ bounds.toffoliGates
  tGates_le : profile.tGates ≤ bounds.tGates
  cnotGates_le : profile.cnotGates ≤ bounds.cnotGates
  singleQubitGates_le : profile.singleQubitGates ≤ bounds.singleQubitGates
  circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth
  toffoliDepth_le : profile.toffoliDepth ≤ bounds.toffoliDepth

/-- An `ADD_N` public-baseline certificate for concrete parameters gives the
generic modular-arithmetic upper-bound relation used by composition layers. -/
theorem supportsUpperBound_of_supportsPublicBaseline
    {n : ℕ} {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SupportsPublicBaseline (params.toProfile n) bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      (params.toProfile n) bounds.toProfile where
  logicalQubits_le := cert.logicalQubits_le
  dataQubits_le := cert.dataQubits_le
  workQubits_le := cert.workQubits_le
  oracleQueries_le := le_rfl
  hadamardGates_le := le_rfl
  toffoliGates_le := cert.toffoliGates_le
  tGates_le := cert.tGates_le
  cnotGates_le := cert.cnotGates_le
  singleQubitGates_le := cert.singleQubitGates_le
  circuitDepth_le := cert.circuitDepth_le
  toffoliDepth_le := cert.toffoliDepth_le
  classicalOps_le := le_rfl

/-- Build an `ADD_N` source-bound certificate from explicit gate-count bounds. -/
theorem supportsPublicBaseline_of_formulaBounds
    {n : ℕ} {params : ResourceParameters}
    {bounds : PublicBaselineBounds.FormulaParameters}
    (hwidth : n = bounds.width)
    (hwork : params.workQubits ≤ bounds.workQubitBound)
    (htoffoli : params.toffoliGates ≤ bounds.toffoliGateBound)
    (ht : params.tGates ≤ bounds.tGateBound)
    (hcnot : params.cnotGates ≤ bounds.cnotGateBound)
    (hsingle : params.singleQubitGates ≤ bounds.singleQubitGateBound)
    (hdepth : params.circuitDepth ≤ bounds.circuitDepthBound)
    (htoffoliDepth : params.toffoliDepth ≤ bounds.toffoliDepthBound) :
    SupportsPublicBaseline (params.toProfile n) bounds.toPublicBaselineBounds where
  logicalQubits_le := by
    rw [hwidth]
    simp [PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds]
    omega
  dataQubits_le := by
    rw [hwidth]
    rfl
  workQubits_le := hwork
  toffoliGates_le := htoffoli
  tGates_le := ht
  cnotGates_le := hcnot
  singleQubitGates_le := hsingle
  circuitDepth_le := hdepth
  toffoliDepth_le := htoffoliDepth

/-- Direct generic upper-bound certificate from explicit `ADD_N` source-count
bounds. -/
private theorem supportsUpperBound_of_formulaBounds
    {n : ℕ} {params : ResourceParameters}
    {bounds : PublicBaselineBounds.FormulaParameters}
    (hwidth : n = bounds.width)
    (hwork : params.workQubits ≤ bounds.workQubitBound)
    (htoffoli : params.toffoliGates ≤ bounds.toffoliGateBound)
    (ht : params.tGates ≤ bounds.tGateBound)
    (hcnot : params.cnotGates ≤ bounds.cnotGateBound)
    (hsingle : params.singleQubitGates ≤ bounds.singleQubitGateBound)
    (hdepth : params.circuitDepth ≤ bounds.circuitDepthBound)
    (htoffoliDepth : params.toffoliDepth ≤ bounds.toffoliDepthBound) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      (params.toProfile n) bounds.toPublicBaselineBounds.toProfile :=
  supportsUpperBound_of_supportsPublicBaseline
    (supportsPublicBaseline_of_formulaBounds hwidth hwork htoffoli ht hcnot
      hsingle hdepth htoffoliDepth)

end ResourceParameters

/-! ### Circuit witness -/

/-- Typed circuit witness for `ADD_N`. The interpreted gate and the projected
resource profile are carried by the same `Circuit` object. -/
noncomputable def addCircuit (N n : ℕ) [NeZero N] (params : ResourceParameters) :
    Circuit (register N) :=
  Circuit.ofGate "ADD_N" (addGate N) (params.toProfile n).toResourceProfile
    params.circuitDepth 0

@[simp] theorem addCircuit_resources (N n : ℕ) [NeZero N]
    (params : ResourceParameters) :
    (addCircuit N n params).resources = (params.toProfile n).toResourceProfile :=
  rfl

@[simp] theorem addCircuit_depth (N n : ℕ) [NeZero N]
    (params : ResourceParameters) :
    (addCircuit N n params).depth = params.circuitDepth :=
  rfl

/-- Basis-state correctness for the typed `ADD_N` circuit witness. -/
theorem addCircuit_apply_ket (N n : ℕ) [NeZero N]
    (params : ResourceParameters) (x : Data N) :
    Circuit.apply (addCircuit N n params)
      (PureState.ket (R := register N) x : StateVector (register N)) =
      (PureState.ket (R := register N) x.addIntoRight : StateVector (register N)) := by
  simpa [addCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register N) => (psi : StateVector (register N)))
      (addGate_apply_ket N x)

/-- Clean basis action of the typed `ADD_N` circuit in public statement form:
`|a,b,0> ↦ |a,a+b,0>` over `ZMod N`. -/
theorem addCircuit_apply_clean_ket (N n : ℕ) [NeZero N]
    (params : ResourceParameters) (a b : ZMod N) :
    Circuit.apply (addCircuit N n params)
      (PureState.ket (R := register N)
        ({ left := a, right := b, flag := false } : Data N) :
          StateVector (register N)) =
      (PureState.ket (R := register N)
        ({ left := a, right := a + b, flag := false } : Data N) :
          StateVector (register N)) := by
  simpa [Data.addIntoRight, add_comm] using
    addCircuit_apply_ket N n params
      ({ left := a, right := b, flag := false } : Data N)

/-- Correctness/resource proof package for an `ADD_N` circuit witness. -/
noncomputable def addCircuitResourceCorrectWitness (N n : ℕ) [NeZero N]
    (params : ResourceParameters) :
    ResourceCorrectWitness (R := register N)
      (∀ x : Data N,
        Circuit.apply (addCircuit N n params)
          (PureState.ket (R := register N) x : StateVector (register N)) =
          (PureState.ket (R := register N) x.addIntoRight : StateVector (register N)))
      ((addCircuit N n params).resources = (params.toProfile n).toResourceProfile ∧
        (addCircuit N n params).depth = params.circuitDepth) := by
  exact
    { circuit := addCircuit N n params
      correctness := fun x => addCircuit_apply_ket N n params x
      resources := ⟨rfl, rfl⟩ }

/-! #### External work-register clean interface -/

/-- `ADD_N` as an external-work clean reversible circuit. This is the same
clean map used by the source-level interface, now wrapped as a typed `Circuit`
with the selected modular-arithmetic resource profile. -/
noncomputable def addWithWorkCircuit (N n : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data N) Work) :=
  (Data.withWorkCleanMap N Work).circuit (params.toProfile n)

@[simp] theorem addWithWorkCircuit_resources (N n : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (addWithWorkCircuit N n Work params).resources =
      (params.toProfile n).toResourceProfile :=
  rfl

@[simp] theorem addWithWorkCircuit_depth (N n : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (addWithWorkCircuit N n Work params).depth = params.circuitDepth :=
  rfl

@[simp] theorem addWithWorkCircuit_queryDepth (N n : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (addWithWorkCircuit N n Work params).queryDepth = 0 :=
  rfl

/-- Basis-state correctness for `ADD_N` with an external work register. -/
theorem addWithWorkCircuit_apply_ket (N n : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : Data N) (w : Work) :
    Circuit.apply (addWithWorkCircuit N n Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (x.addIntoRight, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [addWithWorkCircuit, Data.withWorkCleanMap] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := Data.withWorkCleanMap N Work)
      (profile := params.toProfile n) (x := (x, w))

/-- Clean public-form basis action with an external work register:
`|a,b,0,w> ↦ |a,a+b,0,w>`. -/
private theorem addWithWorkCircuit_apply_clean_ket (N n : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (a b : ZMod N) (w : Work) :
    Circuit.apply (addWithWorkCircuit N n Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ left := a, right := b, flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ left := a, right := a + b, flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [Data.addIntoRight, add_comm] using
    addWithWorkCircuit_apply_ket N n Work params
      ({ left := a, right := b, flag := false } : Data N) w

/-- Resource-correct witness for the external-work `ADD_N` circuit. -/
noncomputable def addWithWorkCircuitResourceCorrectWitness
    (N n : ℕ) [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
      (∀ x : Data N, ∀ w : Work,
        Circuit.apply (addWithWorkCircuit N n Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
              (x.addIntoRight, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)))
      ((addWithWorkCircuit N n Work params).resources =
          (params.toProfile n).toResourceProfile ∧
        (addWithWorkCircuit N n Work params).depth = params.circuitDepth ∧
        (addWithWorkCircuit N n Work params).queryDepth = 0) := by
  exact
    { circuit := addWithWorkCircuit N n Work params
      correctness := fun x w => addWithWorkCircuit_apply_ket N n Work params x w
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Public modular-addition endpoint with explicit natural-number resource
bounds. The theorem keeps the concrete `ADD_N` circuit as the shared object for
correctness and resource claims. -/
private theorem main_with_public_bounds (N n : ℕ) [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds.FormulaParameters)
    (hwidth : n = bounds.width)
    (hwork : params.workQubits ≤ bounds.workQubitBound)
    (htoffoli : params.toffoliGates ≤ bounds.toffoliGateBound)
    (ht : params.tGates ≤ bounds.tGateBound)
    (hcnot : params.cnotGates ≤ bounds.cnotGateBound)
    (hsingle : params.singleQubitGates ≤ bounds.singleQubitGateBound)
    (hdepth : params.circuitDepth ≤ bounds.circuitDepthBound)
    (htoffoliDepth : params.toffoliDepth ≤ bounds.toffoliDepthBound) :
    (∀ a b : ZMod N,
      Circuit.apply (addCircuit N n params)
        (PureState.ket (R := register N)
          ({ left := a, right := b, flag := false } : Data N) :
            StateVector (register N)) =
        (PureState.ket (R := register N)
          ({ left := a, right := a + b, flag := false } : Data N) :
            StateVector (register N))) ∧
      ResourceParameters.SupportsPublicBaseline
        (params.toProfile n) bounds.toPublicBaselineBounds ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        (params.toProfile n) bounds.toPublicBaselineBounds.toProfile ∧
      (addCircuit N n params).resources = (params.toProfile n).toResourceProfile ∧
      (addCircuit N n params).depth = params.circuitDepth := by
  have hbaseline :=
    ResourceParameters.supportsPublicBaseline_of_formulaBounds
      hwidth hwork htoffoli ht hcnot hsingle hdepth htoffoliDepth
  constructor
  · intro a b
    exact addCircuit_apply_clean_ket N n params a b
  constructor
  · exact hbaseline
  constructor
  · exact ResourceParameters.supportsUpperBound_of_supportsPublicBaseline hbaseline
  · exact ⟨rfl, rfl⟩

/-- Resource-correct public witness for the bounded `ADD_N` endpoint. -/
private noncomputable def mainWithPublicBoundsResourceCorrectWitness
    (N n : ℕ) [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds.FormulaParameters)
    (hwidth : n = bounds.width)
    (hwork : params.workQubits ≤ bounds.workQubitBound)
    (htoffoli : params.toffoliGates ≤ bounds.toffoliGateBound)
    (ht : params.tGates ≤ bounds.tGateBound)
    (hcnot : params.cnotGates ≤ bounds.cnotGateBound)
    (hsingle : params.singleQubitGates ≤ bounds.singleQubitGateBound)
    (hdepth : params.circuitDepth ≤ bounds.circuitDepthBound)
    (htoffoliDepth : params.toffoliDepth ≤ bounds.toffoliDepthBound) :
    ResourceCorrectWitness (R := register N)
      (∀ a b : ZMod N,
        Circuit.apply (addCircuit N n params)
          (PureState.ket (R := register N)
            ({ left := a, right := b, flag := false } : Data N) :
              StateVector (register N)) =
          (PureState.ket (R := register N)
            ({ left := a, right := a + b, flag := false } : Data N) :
              StateVector (register N)))
      (ResourceParameters.SupportsPublicBaseline
        (params.toProfile n) bounds.toPublicBaselineBounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          (params.toProfile n) bounds.toPublicBaselineBounds.toProfile ∧
        (addCircuit N n params).resources = (params.toProfile n).toResourceProfile ∧
        (addCircuit N n params).depth = params.circuitDepth) := by
  have hmain :=
    main_with_public_bounds N n params bounds hwidth hwork htoffoli ht hcnot
      hsingle hdepth htoffoliDepth
  exact
    { circuit := addCircuit N n params
      correctness := hmain.1
      resources := ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2⟩ }

/-! ### Compare/subtract/add-back route -/

/-- Natural-number representative produced by comparing `a+b` against `N` and
subtracting `N` exactly on overflow. -/
def compareSubtractAddBack (N a b : ℕ) : ℕ :=
  if N ≤ a + b then a + b - N else a + b

/-- For canonical representatives, compare/subtract/add-back is reduction modulo `N`. -/
theorem compareSubtractAddBack_eq_mod {N a b : ℕ}
    (_hN : 0 < N) (ha : a < N) (hb : b < N) :
    compareSubtractAddBack N a b = (a + b) % N := by
  unfold compareSubtractAddBack
  by_cases hoverflow : N ≤ a + b
  · have hlt : a + b - N < N := by omega
    rw [if_pos hoverflow, Nat.mod_eq_sub_mod hoverflow, Nat.mod_eq_of_lt hlt]
  · have hlt : a + b < N := by omega
    rw [if_neg hoverflow, Nat.mod_eq_of_lt hlt]

/-- The compare/subtract/add-back representative denotes modular addition in `ZMod N`. -/
private theorem natCast_compareSubtractAddBack {N a b : ℕ}
    (hN : 0 < N) (ha : a < N) (hb : b < N) :
    (compareSubtractAddBack N a b : ZMod N) = (a : ZMod N) + (b : ZMod N) := by
  rw [compareSubtractAddBack_eq_mod hN ha hb]
  simp [Nat.cast_add]

end ModularAddition
end QuantumAlg
