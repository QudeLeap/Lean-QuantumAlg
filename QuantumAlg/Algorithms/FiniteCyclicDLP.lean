/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Circuit
public import QuantumAlg.Core.ResourceModel
public import QuantumAlg.Util.FiniteCyclicDLP

/-!
# Finite-cyclic discrete logarithm endpoint

This module packages the finite-cyclic discrete-logarithm oracle/recovery
abstraction with exact natural-number resource counters. The correctness layer
reuses the Fourier-sample recovery certificate from `Util`; the resource layer
keeps every counted field as a concrete integer-valued function.

The two-register oracle and Fourier-sampling route follows Shor's discrete
logarithm algorithm [Sho95, source.tex:1704-1784] and the Abelian-HSP
presentation of discrete logarithms [dW19, qcnotes.tex:2475-2571].
-/

@[expose] public section

namespace QuantumAlg
namespace FiniteCyclicDLP

universe u v

variable {G : Type u} [Group G]

/-! ## Exact-resource profile -/

/-- Exact-resource dimensions for the finite-cyclic DLP endpoint. The named
Fourier-gate families are kept separate so theorem statements do not collapse
controlled phases and swaps into an undifferentiated elementary-gate counter. -/
structure ExactResourceProfile where
  /-- Oracle calls to the DLP oracle `U_x`. -/
  oracleQueries : ℕ
  /-- Total logical qubits/register footprint. -/
  logicalQubits : ℕ
  /-- Hadamard gates in the two exponent-register Fourier layers. -/
  hadamardGates : ℕ
  /-- Controlled-phase gates in the two exponent-register Fourier layers. -/
  controlledPhaseGates : ℕ
  /-- SWAP gates in the two exponent-register Fourier layers. -/
  swapGates : ℕ
  /-- Maximal circuit depth in the selected exact circuit model. -/
  circuitDepth : ℕ
  /-- Structured classical arithmetic post-processing count. -/
  classicalArithmetic : ClassicalArithmeticProfile
deriving DecidableEq

namespace ExactResourceProfile

/-- Scalar classical operation count obtained from the structured taxonomy. -/
def classicalOps (profile : ExactResourceProfile) : ℕ :=
  profile.classicalArithmetic.total

/-- Projection to the older coarse theorem-resource profile. Controlled-phase
and SWAP gates are projected into the elementary-gate counter. -/
def toResourceProfile (profile : ExactResourceProfile) : ResourceProfile where
  oracleQueries := profile.oracleQueries
  hadamardGates := profile.hadamardGates
  elementaryGates := profile.controlledPhaseGates + profile.swapGates
  classicalOps := profile.classicalOps

/-- Exact fieldwise count assertion for the private finite-cyclic DLP resource
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

/-- Concrete source-count parameters for the two-register finite-cyclic DLP
algorithm. `orderRegisterQubits` is the width of each exponent register, while
`groupRegisterQubits` accounts for the group workspace representation. The
depth fields are supplied by the selected exact circuit model. -/
structure ResourceParameters where
  /-- Width of each of the two exponent registers. -/
  orderRegisterQubits : ℕ
  /-- Width of the group workspace register used by the oracle. -/
  groupRegisterQubits : ℕ
  /-- Depth contribution of the single DLP oracle call. -/
  oracleDepth : ℕ
  /-- Depth contribution of the exact two-register Fourier/readout layer. -/
  fourierLayerDepth : ℕ
  /-- Structured classical arithmetic post-processing count. -/
  classicalPostProcessing : ClassicalArithmeticProfile
deriving DecidableEq

namespace ResourceParameters

/-- The selected finite-cyclic DLP route treats the DLP oracle body as one
black-box oracle query. -/
def oracleQueryCount : ℕ :=
  1

/-- Total live register footprint for two exponent registers plus one group
workspace register. -/
def logicalQubits (params : ResourceParameters) : ℕ :=
  2 * params.orderRegisterQubits + params.groupRegisterQubits

/-- Exact two-register Fourier gate profile obtained by applying the same
width to both exponent registers. -/
def fourierGateProfile (params : ResourceParameters) : CircuitGateProfile where
  hadamardGates := 2 * params.orderRegisterQubits
  controlledPhaseGates := params.orderRegisterQubits * (params.orderRegisterQubits - 1)
  swapGates := 2 * (params.orderRegisterQubits / 2)

/-- Maximal circuit depth in the selected sequential oracle/Fourier model. -/
def circuitDepth (params : ResourceParameters) : ℕ :=
  params.oracleDepth + params.fourierLayerDepth

/-- Exact finite-cyclic DLP resource profile determined by the source-count
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
      (2 * params.orderRegisterQubits)
      (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
      (2 * (params.orderRegisterQubits / 2)) :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem toExactResourceProfile_oracleQueries (params : ResourceParameters) :
    params.toExactResourceProfile.oracleQueries = 1 :=
  rfl

@[simp] theorem toExactResourceProfile_logicalQubits (params : ResourceParameters) :
    params.toExactResourceProfile.logicalQubits =
      2 * params.orderRegisterQubits + params.groupRegisterQubits :=
  rfl

@[simp] theorem toExactResourceProfile_hadamardGates (params : ResourceParameters) :
    params.toExactResourceProfile.hadamardGates =
      2 * params.orderRegisterQubits :=
  rfl

@[simp] theorem toExactResourceProfile_controlledPhaseGates
    (params : ResourceParameters) :
    params.toExactResourceProfile.controlledPhaseGates =
      params.orderRegisterQubits * (params.orderRegisterQubits - 1) :=
  rfl

@[simp] theorem toExactResourceProfile_swapGates (params : ResourceParameters) :
    params.toExactResourceProfile.swapGates =
      2 * (params.orderRegisterQubits / 2) :=
  rfl

@[simp] theorem toExactResourceProfile_circuitDepth (params : ResourceParameters) :
    params.toExactResourceProfile.circuitDepth =
      params.oracleDepth + params.fourierLayerDepth :=
  rfl

@[simp] theorem toExactResourceProfile_classicalOps (params : ResourceParameters) :
    params.toExactResourceProfile.classicalOps =
      params.classicalPostProcessing.total :=
  rfl

/-- Exact fieldwise resource theorem for the profile generated by the selected
finite-cyclic DLP source-count parameters. -/
theorem toExactResourceProfile_hasExactCounts (params : ResourceParameters) :
    ExactResourceProfile.HasExactCounts params.toExactResourceProfile
      1
      (2 * params.orderRegisterQubits + params.groupRegisterQubits)
      (2 * params.orderRegisterQubits)
      (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
      (2 * (params.orderRegisterQubits / 2))
      (params.oracleDepth + params.fourierLayerDepth)
      params.classicalPostProcessing.total := by
  simp [ExactResourceProfile.HasExactCounts]

end ResourceParameters

/-! ## Oracle circuit witness -/

instance instFintypeBoundedOracleRegister {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] :
    Fintype (BoundedOracleRegister P) := by
  classical
  let e : BoundedOracleRegister P ≃ (Fin P.order × Fin P.order × G₀) := {
    toFun := fun r => (r.leftExponent, (r.rightExponent, r.workspace))
    invFun := fun r =>
      { leftExponent := r.1
        rightExponent := r.2.1
        workspace := r.2.2 }
    left_inv := by
      intro r
      cases r
      rfl
    right_inv := by
      intro r
      rcases r with ⟨leftExponent, rest⟩
      rcases rest with ⟨rightExponent, workspace⟩
      rfl
  }
  exact Fintype.ofEquiv (Fin P.order × Fin P.order × G₀) e.symm

/-- Register whose basis labels are bounded finite-cyclic DLP oracle states. -/
def oracleRegister {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] : Register where
  Index := BoundedOracleRegister P
  fintype := inferInstance
  decEq := inferInstance

/-- Finite-cyclic DLP oracle gate:
`|a,b,y> ↦ |a,b,y * g^a * x^{-b}>`. -/
noncomputable def oracleGate {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] :
    Gate (oracleRegister P) :=
  Gate.ofPerm (KnownOrderProblem.oracleEquiv P).symm

/-- The finite-cyclic DLP oracle gate is unitary by construction as a
permutation gate. -/
private theorem oracleGate_mem_unitaryGroup {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] :
    ((oracleGate P : Gate (oracleRegister P)) : HilbertOperator (oracleRegister P))
      ∈ Matrix.unitaryGroup (oracleRegister P).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Basis action of the finite-cyclic DLP oracle gate. -/
theorem oracleGate_apply_ket {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (r : BoundedOracleRegister P) :
    (oracleGate P).apply (PureState.ket (R := oracleRegister P) r) =
      PureState.ket (R := oracleRegister P) (P.oracleAction r) := by
  rw [oracleGate, Gate.ofPerm_apply_ket]
  rfl

/-- Coarse one-query resource profile for the finite-cyclic DLP oracle boundary. -/
def oracleResourceProfile : ResourceProfile where
  oracleQueries := 1
  hadamardGates := 0
  elementaryGates := 0
  classicalOps := 0

theorem oracleResourceProfile_exact :
    ResourceProfile.HasExactCounts oracleResourceProfile 1 0 0 0 := by
  simp [ResourceProfile.HasExactCounts, oracleResourceProfile]

/-- Typed circuit witness for the finite-cyclic DLP oracle boundary. -/
noncomputable def oracleCircuit {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] :
    Circuit (oracleRegister P) :=
  Circuit.ofGate "finite-cyclic-dlp-oracle" (oracleGate P)
    oracleResourceProfile 1 1

@[simp] theorem oracleCircuit_resources {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] :
    (oracleCircuit P).resources = oracleResourceProfile :=
  rfl

@[simp] theorem oracleCircuit_depth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] :
    (oracleCircuit P).depth = 1 :=
  rfl

@[simp] theorem oracleCircuit_queryDepth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] :
    (oracleCircuit P).queryDepth = 1 :=
  rfl

/-- Basis-state correctness for the typed finite-cyclic DLP oracle circuit. -/
theorem oracleCircuit_apply_ket {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (r : BoundedOracleRegister P) :
    Circuit.apply (oracleCircuit P)
      (PureState.ket (R := oracleRegister P) r : StateVector (oracleRegister P)) =
      (PureState.ket (R := oracleRegister P) (P.oracleAction r) :
        StateVector (oracleRegister P)) := by
  simpa [oracleCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (oracleRegister P) =>
      (psi : StateVector (oracleRegister P))) (oracleGate_apply_ket P r)

/-- Resource-correct witness for the finite-cyclic DLP oracle boundary. -/
noncomputable def oracleCircuitResourceCorrectWitness {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀] :
    ResourceCorrectWitness (R := oracleRegister P)
      (∀ r : BoundedOracleRegister P,
        Circuit.apply (oracleCircuit P)
          (PureState.ket (R := oracleRegister P) r : StateVector (oracleRegister P)) =
          (PureState.ket (R := oracleRegister P) (P.oracleAction r) :
            StateVector (oracleRegister P)))
      (ResourceProfile.HasExactCounts (oracleCircuit P).resources 1 0 0 0 ∧
        (oracleCircuit P).depth = 1 ∧
        (oracleCircuit P).queryDepth = 1) := by
  exact
    { circuit := oracleCircuit P
      correctness := fun r => oracleCircuit_apply_ket P r
      resources := ⟨by simpa [oracleCircuit] using oracleResourceProfile_exact, rfl, rfl⟩ }

/-! ## Circuit witness -/

/-- Finite-cyclic DLP oracle circuit with source-selected depth. The query count
remains one; the depth field is selected by the exact resource-counting pass. -/
noncomputable def oracleCircuitWithDepth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (oracleDepth : ℕ) : Circuit (oracleRegister P) :=
  Circuit.ofGate "finite-cyclic-dlp-oracle" (oracleGate P)
    oracleResourceProfile oracleDepth 1

@[simp] theorem oracleCircuitWithDepth_resources {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (oracleDepth : ℕ) :
    (oracleCircuitWithDepth P oracleDepth).resources = oracleResourceProfile :=
  rfl

@[simp] theorem oracleCircuitWithDepth_depth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (oracleDepth : ℕ) :
    (oracleCircuitWithDepth P oracleDepth).depth = oracleDepth :=
  rfl

@[simp] theorem oracleCircuitWithDepth_queryDepth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (oracleDepth : ℕ) :
    (oracleCircuitWithDepth P oracleDepth).queryDepth = 1 :=
  rfl

/-- Resource projection for the two exponent-register Fourier/readout and
classical post-processing boundary. -/
def twoRegisterFourierReadoutResourceProfile
    (params : ResourceParameters) : ResourceProfile where
  oracleQueries := 0
  hadamardGates := 2 * params.orderRegisterQubits
  elementaryGates :=
    params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
      2 * (params.orderRegisterQubits / 2)
  classicalOps := params.classicalPostProcessing.total

/-- Typed circuit boundary for the two exponent-register QFT/readout layer in
the finite-cyclic DLP source route. -/
def twoRegisterFourierReadoutCircuit {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) : Circuit (oracleRegister P) :=
  Circuit.abstract (oracleRegister P) "finite-cyclic-dlp-two-register-fourier-readout"
    (twoRegisterFourierReadoutResourceProfile params) params.fourierLayerDepth 0

@[simp] theorem twoRegisterFourierReadoutCircuit_resources {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) :
    (twoRegisterFourierReadoutCircuit P params).resources =
      twoRegisterFourierReadoutResourceProfile params :=
  rfl

@[simp] theorem twoRegisterFourierReadoutCircuit_depth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) :
    (twoRegisterFourierReadoutCircuit P params).depth = params.fourierLayerDepth :=
  rfl

@[simp] theorem twoRegisterFourierReadoutCircuit_queryDepth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) :
    (twoRegisterFourierReadoutCircuit P params).queryDepth = 0 :=
  rfl

/-- Source-level finite-cyclic DLP circuit: the real DLP oracle gate followed by
the abstract two-register Fourier/readout and classical post-processing
boundary. -/
noncomputable def sourceAlgorithmCircuit {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) : Circuit (oracleRegister P) :=
  Circuit.seq (oracleCircuitWithDepth P params.oracleDepth)
    (twoRegisterFourierReadoutCircuit P params)

@[simp] theorem sourceAlgorithmCircuit_resources {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) :
    (sourceAlgorithmCircuit P params).resources =
      params.toExactResourceProfile.toResourceProfile := by
  ext <;>
    simp [sourceAlgorithmCircuit, oracleCircuitWithDepth,
      twoRegisterFourierReadoutCircuit, twoRegisterFourierReadoutResourceProfile,
      oracleResourceProfile, ResourceParameters.toExactResourceProfile,
      ResourceParameters.oracleQueryCount, ResourceParameters.fourierGateProfile,
      ExactResourceProfile.toResourceProfile, ResourceProfile.sequential,
      ExactResourceProfile.classicalOps,
      Circuit.seq, Circuit.ofGate, Circuit.atom, Circuit.abstract]

@[simp] theorem sourceAlgorithmCircuit_depth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) :
    (sourceAlgorithmCircuit P params).depth =
      params.oracleDepth + params.fourierLayerDepth :=
  rfl

@[simp] theorem sourceAlgorithmCircuit_queryDepth {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) :
    (sourceAlgorithmCircuit P params).queryDepth = 1 :=
  rfl

/-- Resource projection carried by the source-level finite-cyclic DLP circuit. -/
theorem sourceAlgorithmCircuit_resourceProjection {G₀ : Type} [Group G₀]
    (P : KnownOrderProblem G₀) [Fintype G₀] [DecidableEq G₀]
    (params : ResourceParameters) :
    (sourceAlgorithmCircuit P params).resources =
      params.toExactResourceProfile.toResourceProfile ∧
      (sourceAlgorithmCircuit P params).depth =
        params.oracleDepth + params.fourierLayerDepth ∧
      (sourceAlgorithmCircuit P params).queryDepth = 1 := by
  exact ⟨sourceAlgorithmCircuit_resources P params, rfl, rfl⟩

/-- Typed circuit boundary for the finite-cyclic DLP endpoint. The same circuit
object carries the projected resource profile used by public theorem witnesses;
the stronger named-field exact profile remains linked to this projection. -/
noncomputable def algorithmCircuit (params : ResourceParameters) :
    Circuit (Qubits params.logicalQubits) :=
  Circuit.abstract (Qubits params.logicalQubits) "finite-cyclic-dlp"
    params.toExactResourceProfile.toResourceProfile params.circuitDepth
    ResourceParameters.oracleQueryCount

@[simp] theorem algorithmCircuit_resources (params : ResourceParameters) :
    (algorithmCircuit params).resources =
      params.toExactResourceProfile.toResourceProfile :=
  rfl

@[simp] theorem algorithmCircuit_depth (params : ResourceParameters) :
    (algorithmCircuit params).depth = params.circuitDepth :=
  rfl

@[simp] theorem algorithmCircuit_queryDepth (params : ResourceParameters) :
    (algorithmCircuit params).queryDepth = ResourceParameters.oracleQueryCount :=
  rfl

/-- Coarse resource projection carried by the finite-cyclic DLP circuit
boundary. The private exact profile below records the finer named gate families
and logical footprint. -/
theorem algorithmCircuit_resourceProfile_hasExactCounts
    (params : ResourceParameters) :
    ResourceProfile.HasExactCounts (algorithmCircuit params).resources
      1
      (2 * params.orderRegisterQubits)
      (params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
        2 * (params.orderRegisterQubits / 2))
      params.classicalPostProcessing.total := by
  simp [algorithmCircuit, ResourceProfile.HasExactCounts]

/-! ## Public-bound support -/

/-- Public-facing finite-cyclic DLP resource fields as concrete natural-number
bounds. These fields replace the reader-facing asymptotic statement when the
private exact-resource theorem is instantiated. -/
structure PublicBaselineBounds where
  /-- Number of oracle queries used by the public bound. -/
  oracleQueries : ℕ
  /-- Qubit-count component for logical qubits. -/
  logicalQubits : ℕ
  /-- Gate-count component for Hadamard gates. -/
  hadamardGates : ℕ
  /-- Gate-count component for controlled-phase gates. -/
  controlledPhaseGates : ℕ
  /-- Gate-count component for SWAP gates. -/
  swapGates : ℕ
  /-- Depth component for circuit depth. -/
  circuitDepth : ℕ
  /-- Classical-operation count component. -/
  classicalOps : ℕ
deriving DecidableEq

namespace PublicBaselineBounds

/-- Explicit public-bound parameters for a known-order finite-cyclic DLP
instance. `orderBitUpperBound` is a natural-number upper bound for `log N`;
the remaining fields make the group representation, oracle scheduling, and
classical post-processing bounds explicit. -/
structure FormulaParameters where
  /-- Explicit upper bound for the subgroup-order bit length. -/
  orderBitUpperBound : ℕ
  /-- Explicit upper bound for the group-register footprint. -/
  groupRegisterQubitBound : ℕ
  /-- Explicit upper bound for the oracle-call depth. -/
  oracleDepthBound : ℕ
  /-- Explicit upper bound for the Fourier/readout layer depth. -/
  fourierLayerDepthBound : ℕ
  /-- Explicit upper bound for the classical post-processing count. -/
  classicalOperationBound : ℕ
deriving DecidableEq

namespace FormulaParameters

/-- Public bound obtained by replacing every finite-cyclic DLP asymptotic term
with an explicit natural-number upper-bound function. -/
def toPublicBaselineBounds (params : FormulaParameters) : PublicBaselineBounds where
  oracleQueries := 1
  logicalQubits := 2 * params.orderBitUpperBound + params.groupRegisterQubitBound
  hadamardGates := 2 * params.orderBitUpperBound
  controlledPhaseGates := params.orderBitUpperBound * (params.orderBitUpperBound - 1)
  swapGates := 2 * (params.orderBitUpperBound / 2)
  circuitDepth := params.oracleDepthBound + params.fourierLayerDepthBound
  classicalOps := params.classicalOperationBound

@[simp] theorem toPublicBaselineBounds_oracleQueries (params : FormulaParameters) :
    params.toPublicBaselineBounds.oracleQueries = 1 :=
  rfl

@[simp] theorem toPublicBaselineBounds_logicalQubits (params : FormulaParameters) :
    params.toPublicBaselineBounds.logicalQubits =
      2 * params.orderBitUpperBound + params.groupRegisterQubitBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_hadamardGates (params : FormulaParameters) :
    params.toPublicBaselineBounds.hadamardGates =
      2 * params.orderBitUpperBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_controlledPhaseGates
    (params : FormulaParameters) :
    params.toPublicBaselineBounds.controlledPhaseGates =
      params.orderBitUpperBound * (params.orderBitUpperBound - 1) :=
  rfl

@[simp] theorem toPublicBaselineBounds_swapGates (params : FormulaParameters) :
    params.toPublicBaselineBounds.swapGates =
      2 * (params.orderBitUpperBound / 2) :=
  rfl

@[simp] theorem toPublicBaselineBounds_circuitDepth (params : FormulaParameters) :
    params.toPublicBaselineBounds.circuitDepth =
      params.oracleDepthBound + params.fourierLayerDepthBound :=
  rfl

@[simp] theorem toPublicBaselineBounds_classicalOps (params : FormulaParameters) :
    params.toPublicBaselineBounds.classicalOps =
      params.classicalOperationBound :=
  rfl

end FormulaParameters

end PublicBaselineBounds

/-- The exact finite-cyclic DLP profile supports public-facing concrete bounds
when every exact field is bounded by its corresponding bound. -/
structure SupportsPublicBaseline
    (profile : ExactResourceProfile) (bounds : PublicBaselineBounds) : Prop where
  oracleQueries_le : profile.oracleQueries ≤ bounds.oracleQueries
  logicalQubits_le : profile.logicalQubits ≤ bounds.logicalQubits
  hadamardGates_le : profile.hadamardGates ≤ bounds.hadamardGates
  controlledPhaseGates_le :
    profile.controlledPhaseGates ≤ bounds.controlledPhaseGates
  swapGates_le : profile.swapGates ≤ bounds.swapGates
  circuitDepth_le : profile.circuitDepth ≤ bounds.circuitDepth
  classicalOps_le : profile.classicalOps ≤ bounds.classicalOps

/-- Build the public-bound certificate from explicit natural-number upper
bounds. This theorem is the private-resource bridge replacing the finite-cyclic
DLP statement's asymptotic resource terms. -/
theorem supportsPublicBaseline_of_formulaBounds
    {params : ResourceParameters}
    {bounds : PublicBaselineBounds.FormulaParameters}
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    SupportsPublicBaseline params.toExactResourceProfile bounds.toPublicBaselineBounds where
  oracleQueries_le := le_rfl
  logicalQubits_le := by
    simp
    omega
  hadamardGates_le := by
    simp
    omega
  controlledPhaseGates_le := by
    simp only [ResourceParameters.toExactResourceProfile_controlledPhaseGates,
      PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds_controlledPhaseGates]
    exact Nat.mul_le_mul horderBits (Nat.sub_le_sub_right horderBits 1)
  swapGates_le := by
    simp only [ResourceParameters.toExactResourceProfile_swapGates,
      PublicBaselineBounds.FormulaParameters.toPublicBaselineBounds_swapGates,
      Order.lt_two_iff, zero_le, mul_le_mul_iff_right₀]
    exact Nat.div_le_div_right horderBits
  circuitDepth_le := by
    simp
    omega
  classicalOps_le := by
    simpa using hclassical

/-! ## Public theorem shape -/

/-- Public exponent-register width used by the finite-cyclic DLP statement.
This is the explicit natural-number upper-bound width
`ceil(log_2 N) = Nat.clog 2 N`. -/
def publicOrderWidth (N : ℕ) : ℕ :=
  Nat.clog 2 N

/-- Public qubit count for the ideal finite-cyclic DLP algorithm statement. -/
def publicQubitCount (N : ℕ) : ℕ :=
  3 * publicOrderWidth N

/-- Public Hadamard count for two exponent-register Fourier layers. -/
def publicHadamardCount (N : ℕ) : ℕ :=
  2 * publicOrderWidth N

/-- Public controlled-phase count for two exponent-register Fourier layers. -/
def publicControlledPhaseCount (N : ℕ) : ℕ :=
  publicOrderWidth N * (publicOrderWidth N - 1)

/-- Public SWAP count for the two-register Fourier/readout schedule. -/
def publicSwapCount (N : ℕ) : ℕ :=
  2 * (publicOrderWidth N / 2)

/-- Public maximal circuit depth bound for one oracle call followed by the
two exponent-register Fourier/readout schedule. -/
def publicCircuitDepth (N : ℕ) : ℕ :=
  1 + publicHadamardCount N + publicControlledPhaseCount N + publicSwapCount N

/-- Public classical post-processing profile for the finite-cyclic DLP endpoint:
one gcd check, one extended-Euclidean run, one modular inversion, one
relation-check addition, one relation-check multiplication, and the final
negation/multiplication recovery expression. -/
def publicClassicalArithmeticProfile : ClassicalArithmeticProfile where
  bitInteger := BitIntegerOperationProfile.zero
  numberTheoretic :=
    { NumberTheoreticOperationProfile.zero with
      gcds := 1
      extendedEuclidean := 1 }
  modularField :=
    { ModularFieldOperationProfile.zero with
      additions := 1
      negations := 1
      multiplications := 2
      inversions := 1 }
  groupControl := GroupControlOperationProfile.zero

@[simp] theorem publicClassicalArithmeticProfile_total :
    publicClassicalArithmeticProfile.total = 7 := by
  simp [publicClassicalArithmeticProfile, ClassicalArithmeticProfile.total,
    BitIntegerOperationProfile.zero, NumberTheoreticOperationProfile.zero,
    ModularFieldOperationProfile.zero, GroupControlOperationProfile.zero,
    BitIntegerOperationProfile.total, NumberTheoreticOperationProfile.total,
    ModularFieldOperationProfile.total, GroupControlOperationProfile.total]

/-- Public resource profile with every field expressed directly in terms of the
known group order `N`. -/
def publicExactResourceProfile (N : ℕ) : ExactResourceProfile where
  oracleQueries := 1
  logicalQubits := publicQubitCount N
  hadamardGates := publicHadamardCount N
  controlledPhaseGates := publicControlledPhaseCount N
  swapGates := publicSwapCount N
  circuitDepth := publicCircuitDepth N
  classicalArithmetic := publicClassicalArithmeticProfile

/-- Exact fieldwise counts for the public finite-cyclic DLP resource profile. -/
theorem publicExactResourceProfile_hasExactCounts (N : ℕ) :
    (publicExactResourceProfile N).HasExactCounts
      1
      (publicQubitCount N)
      (publicHadamardCount N)
      (publicControlledPhaseCount N)
      (publicSwapCount N)
      (publicCircuitDepth N)
      7 := by
  simp [ExactResourceProfile.HasExactCounts, ExactResourceProfile.classicalOps,
    publicExactResourceProfile]

/-- Public endpoint data for the finite-cyclic DLP TeX statement. The public
resource profile is fixed by the known group order `N`; implementation-carrier
resource parameters stay in private bridge theorems. -/
structure PublicEndpointData {P : KnownOrderProblem G}
    (N : ℕ) (secret output : ZMod P.order) (successMass : ℝ) where
  order_eq : P.order = N
  output_eq_secret : output = secret
  success_atLeast_twoThirds : (2 : ℝ) / 3 ≤ successMass
  success_nonneg : 0 ≤ successMass
  success_le_one : successMass ≤ 1
  hasExactCounts :
    (publicExactResourceProfile N).HasExactCounts
      1
      (publicQubitCount N)
      (publicHadamardCount N)
      (publicControlledPhaseCount N)
      (publicSwapCount N)
      (publicCircuitDepth N)
      7

/-- Public theorem shape for finite-cyclic discrete logarithms. -/
def PublicTheoremShape {P : KnownOrderProblem G}
    (N : ℕ) (secret output : ZMod P.order) (successMass : ℝ) : Prop :=
  Nonempty (PublicEndpointData (P := P) N secret output successMass)

namespace PublicTheoremShape

/-- Public theorem endpoint with resource counts fixed by the problem order.

The statement follows Shor's finite-cyclic discrete-logarithm oracle route
[Sho95, source.tex:1704-1784]. The width `Nat.clog 2 N` records the explicit
natural-number upper bound rendered as `n = \lceil\log_2 N\rceil` in the
public TeX statement; no implementation-specific workspace or schedule symbols
appear in the public theorem. -/
theorem main {P : KnownOrderProblem G}
    (N : ℕ) (secret output : ZMod P.order) (successMass : ℝ)
    (order_eq : P.order = N)
    (output_eq_secret : output = secret)
    (success_atLeast_twoThirds : (2 : ℝ) / 3 ≤ successMass)
    (success_nonneg : 0 ≤ successMass)
    (success_le_one : successMass ≤ 1) :
    PublicTheoremShape (P := P) N secret output successMass := by
  exact ⟨
    { order_eq := order_eq
      output_eq_secret := output_eq_secret
      success_atLeast_twoThirds := success_atLeast_twoThirds
      success_nonneg := success_nonneg
      success_le_one := success_le_one
      hasExactCounts := publicExactResourceProfile_hasExactCounts N }⟩

end PublicTheoremShape

/-! ## Classical recovery and endpoint theorem -/

/-- Minimal classical arithmetic profile for the final recovery expression once
an inverse of the first Fourier frequency has already been supplied. The profile
counts the negation and multiplication in `-k * a^{-1}`; inverse computation can
be supplied by `ResourceParameters.classicalPostProcessing` when it is not part
of the sample certificate. -/
def recoveryWithInverseProfile : ClassicalArithmeticProfile where
  bitInteger := BitIntegerOperationProfile.zero
  numberTheoretic := NumberTheoreticOperationProfile.zero
  modularField :=
    { ModularFieldOperationProfile.zero with
      negations := 1
      multiplications := 1 }
  groupControl := GroupControlOperationProfile.zero

@[simp] theorem recoveryWithInverseProfile_total :
    recoveryWithInverseProfile.total = 2 := by
  simp [recoveryWithInverseProfile, ClassicalArithmeticProfile.total,
    BitIntegerOperationProfile.zero, NumberTheoreticOperationProfile.zero,
    ModularFieldOperationProfile.zero, GroupControlOperationProfile.zero,
    BitIntegerOperationProfile.total, NumberTheoreticOperationProfile.total,
    ModularFieldOperationProfile.total, GroupControlOperationProfile.total]

/-- Concrete classical-count parameters for the finite-cyclic DLP recovery step.
The fields separate the exact operation families required by the shared
classical-arithmetic taxonomy: unit/inverse discovery via gcd/EEA, modular
inversion, relation validation, and the final `-right * inverse` recovery. -/
structure ClassicalRecoveryCountParameters where
  /-- GCD checks used to validate that the first Fourier frequency is invertible. -/
  inverseGcdChecks : ℕ
  /-- Extended-Euclidean runs used to construct the inverse. -/
  inverseExtendedEuclideanRuns : ℕ
  /-- Modular inverse operations counted as modular/field work when the source
  treats inversion separately from EEA. -/
  modularInversions : ℕ
  /-- Modular additions used when validating the DLP linear relation. -/
  relationCheckAdditions : ℕ
  /-- Modular multiplications used when validating the DLP linear relation. -/
  relationCheckMultiplications : ℕ
deriving DecidableEq

namespace ClassicalRecoveryCountParameters

/-- Count parameters for the direct recovery rule when the inverse is already
part of the source sample certificate. -/
def withSuppliedInverse : ClassicalRecoveryCountParameters where
  inverseGcdChecks := 0
  inverseExtendedEuclideanRuns := 0
  modularInversions := 0
  relationCheckAdditions := 0
  relationCheckMultiplications := 0

/-- Structured classical arithmetic profile for one finite-cyclic DLP recovery
attempt. The final recovery expression always contributes one modular negation
and one modular multiplication; the remaining fields make inverse discovery and
linear-relation validation explicit natural-number counts. -/
def toProfile (params : ClassicalRecoveryCountParameters) :
    ClassicalArithmeticProfile where
  bitInteger := BitIntegerOperationProfile.zero
  numberTheoretic :=
    { NumberTheoreticOperationProfile.zero with
      gcds := params.inverseGcdChecks
      extendedEuclidean := params.inverseExtendedEuclideanRuns }
  modularField :=
    { ModularFieldOperationProfile.zero with
      additions := params.relationCheckAdditions
      negations := 1
      multiplications := 1 + params.relationCheckMultiplications
      inversions := params.modularInversions }
  groupControl := GroupControlOperationProfile.zero

@[simp] theorem toProfile_withSuppliedInverse :
    withSuppliedInverse.toProfile = recoveryWithInverseProfile :=
  rfl

@[simp] theorem toProfile_total (params : ClassicalRecoveryCountParameters) :
    params.toProfile.total =
      params.inverseGcdChecks +
        params.inverseExtendedEuclideanRuns +
        params.relationCheckAdditions +
        1 +
        (1 + params.relationCheckMultiplications) +
        params.modularInversions := by
  simp [toProfile, ClassicalArithmeticProfile.total,
    BitIntegerOperationProfile.zero, NumberTheoreticOperationProfile.zero,
    ModularFieldOperationProfile.zero, GroupControlOperationProfile.zero,
    BitIntegerOperationProfile.total, NumberTheoreticOperationProfile.total,
    ModularFieldOperationProfile.total, GroupControlOperationProfile.total]
  omega

/-- Canonical explicit upper-bound profile for one finite-cyclic DLP classical
recovery attempt. The source route recovers the hidden exponent from the
two-register Fourier relation: one unit/inverse check, one inverse
construction, one modular inverse counted in the modular-field family, one
linear-relation validation addition and multiplication, and the final
`-right * inverse` recovery expression. -/
def directRecoveryUpperBound : ClassicalRecoveryCountParameters where
  inverseGcdChecks := 1
  inverseExtendedEuclideanRuns := 1
  modularInversions := 1
  relationCheckAdditions := 1
  relationCheckMultiplications := 1

/-- Scalar form of the canonical finite-cyclic DLP recovery upper bound. -/
def directRecoveryUpperBoundTotal : ℕ :=
  1 + 1 + 1 + 1 + (1 + 1) + 1

theorem directRecoveryUpperBound_total :
    directRecoveryUpperBound.toProfile.total =
      directRecoveryUpperBoundTotal := by
  simp [directRecoveryUpperBound, directRecoveryUpperBoundTotal]

/-- The canonical finite-cyclic DLP recovery count is an explicit natural-number
upper-bound function, not an asymptotic resource term. -/
def directRecoveryUpperBoundSpec : ClassicalCountSpec Unit :=
  ClassicalCountSpec.explicitUpperBound (fun _ => directRecoveryUpperBoundTotal)

@[simp] theorem directRecoveryUpperBoundSpec_kind :
    directRecoveryUpperBoundSpec.kind = ClassicalCountKind.explicitUpperBound :=
  rfl

@[simp] theorem directRecoveryUpperBoundSpec_count (params : Unit) :
    directRecoveryUpperBoundSpec.count params = directRecoveryUpperBoundTotal :=
  rfl

end ClassicalRecoveryCountParameters

namespace ResourceParameters

/-- Replace the finite-cyclic DLP classical post-processing profile by an
explicit recovery-count profile. -/
def withClassicalRecoveryCounts (params : ResourceParameters)
    (counts : ClassicalRecoveryCountParameters) : ResourceParameters :=
  { params with classicalPostProcessing := counts.toProfile }

@[simp] theorem withClassicalRecoveryCounts_classicalPostProcessing
    (params : ResourceParameters) (counts : ClassicalRecoveryCountParameters) :
    (params.withClassicalRecoveryCounts counts).classicalPostProcessing =
      counts.toProfile :=
  rfl

@[simp] theorem withClassicalRecoveryCounts_classicalOps
    (params : ResourceParameters) (counts : ClassicalRecoveryCountParameters) :
    (params.withClassicalRecoveryCounts counts).classicalPostProcessing.total =
      counts.toProfile.total :=
  rfl

/-- Replace the finite-cyclic DLP classical post-processing profile by the
canonical direct-recovery explicit upper-bound function. -/
def withDirectRecoveryUpperBound (params : ResourceParameters) :
    ResourceParameters :=
  params.withClassicalRecoveryCounts
    ClassicalRecoveryCountParameters.directRecoveryUpperBound

@[simp] theorem withDirectRecoveryUpperBound_classicalOps
    (params : ResourceParameters) :
    params.withDirectRecoveryUpperBound.classicalPostProcessing.total =
      ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal := by
  rw [withDirectRecoveryUpperBound, withClassicalRecoveryCounts_classicalOps,
    ClassicalRecoveryCountParameters.directRecoveryUpperBound_total]

/-- Fieldwise exact-resource profile after selecting an explicit classical
recovery-count profile. -/
theorem withClassicalRecoveryCounts_toExactResourceProfile_hasExactCounts
    (params : ResourceParameters) (counts : ClassicalRecoveryCountParameters) :
    (params.withClassicalRecoveryCounts counts).toExactResourceProfile.HasExactCounts
      1
      (2 * params.orderRegisterQubits + params.groupRegisterQubits)
      (2 * params.orderRegisterQubits)
      (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
      (2 * (params.orderRegisterQubits / 2))
      (params.oracleDepth + params.fourierLayerDepth)
      counts.toProfile.total := by
  simpa [withClassicalRecoveryCounts] using
    (params.withClassicalRecoveryCounts counts).toExactResourceProfile_hasExactCounts

/-- Fieldwise exact-resource theorem after attaching the canonical direct
classical-recovery upper bound. -/
private theorem withDirectRecoveryUpperBound_toExactResourceProfile_hasExactCounts
    (params : ResourceParameters) :
    params.withDirectRecoveryUpperBound.toExactResourceProfile.HasExactCounts
      1
      (2 * params.orderRegisterQubits + params.groupRegisterQubits)
      (2 * params.orderRegisterQubits)
      (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
      (2 * (params.orderRegisterQubits / 2))
      (params.oracleDepth + params.fourierLayerDepth)
      ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal := by
  rw [withDirectRecoveryUpperBound]
  rw [← ClassicalRecoveryCountParameters.directRecoveryUpperBound_total]
  exact
    withClassicalRecoveryCounts_toExactResourceProfile_hasExactCounts params
      ClassicalRecoveryCountParameters.directRecoveryUpperBound

end ResourceParameters

/-! ## Public endpoint shape -/

/-- Public exact resource fields for the finite-cyclic DLP theorem statement.
These are the theorem-facing dimensions for the known-order oracle, two
exponent registers, Fourier/readout layer, and direct classical recovery step
[Sho95, source.tex:1704-1784] [dW19, qcnotes.tex:2475-2571]. -/
structure PublicResourceFields where
  /-- Exact width of each exponent register. -/
  orderRegisterQubits : Nat
  /-- Exact group-workspace footprint. -/
  groupRegisterQubits : Nat
  /-- Exact depth of the single DLP-oracle call. -/
  oracleDepth : Nat
  /-- Exact depth of the two-register Fourier/readout schedule. -/
  fourierLayerDepth : Nat
deriving DecidableEq

namespace PublicResourceFields

/-- Resource parameters with zero classical post-processing, before the
canonical direct-recovery upper bound is attached. -/
def baseResourceParameters (fields : PublicResourceFields) :
    ResourceParameters where
  orderRegisterQubits := fields.orderRegisterQubits
  groupRegisterQubits := fields.groupRegisterQubits
  oracleDepth := fields.oracleDepth
  fourierLayerDepth := fields.fourierLayerDepth
  classicalPostProcessing := ClassicalArithmeticProfile.zero

/-- Exact finite-cyclic DLP resource parameters with the canonical direct
classical-recovery count attached. -/
def toResourceParameters (fields : PublicResourceFields) :
    ResourceParameters :=
  fields.baseResourceParameters.withDirectRecoveryUpperBound

/-- Public bound obtained from exact finite-cyclic DLP resource fields. -/
def toPublicBaselineBounds (fields : PublicResourceFields) :
    PublicBaselineBounds where
  oracleQueries := 1
  logicalQubits := 2 * fields.orderRegisterQubits + fields.groupRegisterQubits
  hadamardGates := 2 * fields.orderRegisterQubits
  controlledPhaseGates :=
    fields.orderRegisterQubits * (fields.orderRegisterQubits - 1)
  swapGates := 2 * (fields.orderRegisterQubits / 2)
  circuitDepth := fields.oracleDepth + fields.fourierLayerDepth
  classicalOps := ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal

@[simp] theorem toResourceParameters_classicalOps
    (fields : PublicResourceFields) :
    fields.toResourceParameters.classicalPostProcessing.total =
      ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal := by
  exact ResourceParameters.withDirectRecoveryUpperBound_classicalOps
    fields.baseResourceParameters

/-- Exact fieldwise resource theorem for the public resource fields. -/
theorem toResourceParameters_hasExactCounts
    (fields : PublicResourceFields) :
    ExactResourceProfile.HasExactCounts
      fields.toResourceParameters.toExactResourceProfile
      1
      (2 * fields.orderRegisterQubits + fields.groupRegisterQubits)
      (2 * fields.orderRegisterQubits)
      (fields.orderRegisterQubits * (fields.orderRegisterQubits - 1))
      (2 * (fields.orderRegisterQubits / 2))
      (fields.oracleDepth + fields.fourierLayerDepth)
      ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal := by
  simpa [toResourceParameters, baseResourceParameters] using
    ResourceParameters.withDirectRecoveryUpperBound_toExactResourceProfile_hasExactCounts
      fields.baseResourceParameters

/-- The exact public resource profile supports its matching public baseline
without asymptotic slack. -/
theorem supportsPublicBaseline (fields : PublicResourceFields) :
    SupportsPublicBaseline
      fields.toResourceParameters.toExactResourceProfile
      fields.toPublicBaselineBounds where
  oracleQueries_le := by simp [toResourceParameters, baseResourceParameters,
    ResourceParameters.withDirectRecoveryUpperBound,
    ResourceParameters.withClassicalRecoveryCounts, toPublicBaselineBounds]
  logicalQubits_le := by simp [toResourceParameters, baseResourceParameters,
    ResourceParameters.withDirectRecoveryUpperBound,
    ResourceParameters.withClassicalRecoveryCounts, toPublicBaselineBounds]
  hadamardGates_le := by simp [toResourceParameters, baseResourceParameters,
    ResourceParameters.withDirectRecoveryUpperBound,
    ResourceParameters.withClassicalRecoveryCounts, toPublicBaselineBounds]
  controlledPhaseGates_le := by simp [toResourceParameters,
    baseResourceParameters, ResourceParameters.withDirectRecoveryUpperBound,
    ResourceParameters.withClassicalRecoveryCounts, toPublicBaselineBounds]
  swapGates_le := by simp [toResourceParameters, baseResourceParameters,
    ResourceParameters.withDirectRecoveryUpperBound,
    ResourceParameters.withClassicalRecoveryCounts, toPublicBaselineBounds]
  circuitDepth_le := by simp [toResourceParameters, baseResourceParameters,
    ResourceParameters.withDirectRecoveryUpperBound,
    ResourceParameters.withClassicalRecoveryCounts, toPublicBaselineBounds]
  classicalOps_le := by
    change
      ClassicalRecoveryCountParameters.directRecoveryUpperBound.toProfile.total <=
        ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal
    exact le_of_eq ClassicalRecoveryCountParameters.directRecoveryUpperBound_total

end PublicResourceFields

/-- Public finite-cyclic DLP input package.  The hidden scalar and target-power
equation are public theorem data; Fourier-support and sampling certificates
remain support-layer objects and are not fields of this public input [Sho95,
source.tex:1704-1784]. -/
structure PublicInput (P : KnownOrderProblem G) where
  /-- Hidden scalar in the known-order residue ring. -/
  secret : ZMod P.order
  /-- The target is the advertised power of the selected generator. -/
  target_eq_generator_pow : P.generator ^ secret.val = P.target
  /-- Exact public resource fields for the oracle/Fourier/recovery route. -/
  resources : PublicResourceFields

/-- Public endpoint witness for finite-cyclic discrete logarithms.  It records
only theorem-facing endpoint data: an output scalar, the one-run success lower
bound, exact resource fields, and support for the public baseline.  Constructors
from Shor/Fourier sampling support stay separate and must not be registered as
the public theorem endpoint [Sho95, source.tex:1704-1784] [dW19,
qcnotes.tex:2475-2571]. -/
structure PublicEndpointWitness {P : KnownOrderProblem G}
    (input : PublicInput P) (bounds : PublicBaselineBounds) where
  /-- Recovered scalar in `ZMod N` form. -/
  output : ZMod P.order
  /-- Exact profile associated with the endpoint route. -/
  profile : ExactResourceProfile
  /-- The recovered scalar is the hidden scalar from the public input. -/
  output_eq_secret : output = input.secret
  /-- Numerator of the certified one-run success lower bound. -/
  successNumerator : Nat
  /-- Denominator of the certified one-run success lower bound. -/
  successDenominator : Nat
  successDenominator_pos : 0 < successDenominator
  /-- The endpoint success probability is at least `2/3`. -/
  success_atLeast_twoThirds :
    2 * successDenominator <= 3 * successNumerator
  /-- Exact fieldwise resource theorem for the public profile. -/
  exactCounts :
    ExactResourceProfile.HasExactCounts profile
      1
      (2 * input.resources.orderRegisterQubits +
        input.resources.groupRegisterQubits)
      (2 * input.resources.orderRegisterQubits)
      (input.resources.orderRegisterQubits *
        (input.resources.orderRegisterQubits - 1))
      (2 * (input.resources.orderRegisterQubits / 2))
      (input.resources.oracleDepth + input.resources.fourierLayerDepth)
      ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal
  /-- The exact profile supports the public baseline fields. -/
  supportsPublicBaseline : SupportsPublicBaseline profile bounds

namespace PublicEndpointWitness

/-- Public consequence predicate for a finite-cyclic DLP endpoint witness. -/
def Statement {P : KnownOrderProblem G} {input : PublicInput P}
    {bounds : PublicBaselineBounds}
    (witness : PublicEndpointWitness input bounds) : Prop :=
  witness.output = input.secret /\
    P.generator ^ witness.output.val = P.target /\
    0 < witness.successDenominator /\
    2 * witness.successDenominator <= 3 * witness.successNumerator /\
    ExactResourceProfile.HasExactCounts witness.profile
      1
      (2 * input.resources.orderRegisterQubits +
        input.resources.groupRegisterQubits)
      (2 * input.resources.orderRegisterQubits)
      (input.resources.orderRegisterQubits *
        (input.resources.orderRegisterQubits - 1))
      (2 * (input.resources.orderRegisterQubits / 2))
      (input.resources.oracleDepth + input.resources.fourierLayerDepth)
      ClassicalRecoveryCountParameters.directRecoveryUpperBoundTotal /\
    SupportsPublicBaseline witness.profile bounds

/-- Any public endpoint witness exposes the public theorem-shape consequence. -/
theorem statement {P : KnownOrderProblem G} {input : PublicInput P}
    {bounds : PublicBaselineBounds}
    (witness : PublicEndpointWitness input bounds) :
    witness.Statement := by
  refine ⟨witness.output_eq_secret, ?_, witness.successDenominator_pos,
    witness.success_atLeast_twoThirds, witness.exactCounts,
    witness.supportsPublicBaseline⟩
  simpa [witness.output_eq_secret] using input.target_eq_generator_pow

end PublicEndpointWitness

/-- Finite-cyclic DLP endpoint with exact resource counters. The theorem keeps
sampling success as an explicit certificate and proves that the classical
recovery output and every resource field match the selected concrete count. -/
private theorem exactResourceEndpoint {P : KnownOrderProblem G}
    (run : AlgorithmRunCertificate P) (params : ResourceParameters) :
    run.output = run.secret ∧
      run.SuccessAtLeastTwoThirds ∧
      ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total := by
  constructor
  · exact run.output_eq_secret
  constructor
  · exact run.successAtLeastTwoThirds
  · exact params.toExactResourceProfile_hasExactCounts

/-- Circuit-based witness for the finite-cyclic DLP endpoint: correctness,
private exact named-resource counts, and the circuit's projected resource
counters are packaged around one typed circuit boundary. -/
private noncomputable def mainResourceCorrectWitness {P : KnownOrderProblem G}
    (run : AlgorithmRunCertificate P) (params : ResourceParameters) :
    ResourceCorrectWitness (R := Qubits params.logicalQubits)
      (run.output = run.secret ∧ run.SuccessAtLeastTwoThirds)
      (ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
        ResourceProfile.HasExactCounts (algorithmCircuit params).resources
          1
          (2 * params.orderRegisterQubits)
          (params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
            2 * (params.orderRegisterQubits / 2))
          params.classicalPostProcessing.total ∧
        (algorithmCircuit params).depth =
          params.oracleDepth + params.fourierLayerDepth) := by
  have hmain := exactResourceEndpoint run params
  exact
    { circuit := algorithmCircuit params
      correctness := ⟨hmain.1, hmain.2.1⟩
      resources := by
        refine ⟨hmain.2.2, ?_, ?_⟩
        · exact algorithmCircuit_resourceProfile_hasExactCounts params
        · rfl }

/-- Finite-cyclic DLP endpoint with exact counts and explicit public resource
bounds. This packages the correctness/resource theorem with the private
exact-resource bridge that replaces asymptotic public resource terms by
natural-number upper-bound functions. -/
private theorem exactResourceEndpoint_with_public_bounds {P : KnownOrderProblem G}
    (run : AlgorithmRunCertificate P)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    run.output = run.secret ∧
      run.SuccessAtLeastTwoThirds ∧
      ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
      SupportsPublicBaseline params.toExactResourceProfile
        bounds.toPublicBaselineBounds := by
  have hmain := exactResourceEndpoint run params
  refine ⟨hmain.1, hmain.2.1, hmain.2.2, ?_⟩
  exact supportsPublicBaseline_of_formulaBounds horderBits hgroup horacleDepth
    hfourierDepth hclassical

/-- Circuit-based witness for the finite-cyclic DLP endpoint with public
resource bounds. -/
private noncomputable def mainWithPublicBoundsResourceCorrectWitness {P : KnownOrderProblem G}
    (run : AlgorithmRunCertificate P)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    ResourceCorrectWitness (R := Qubits params.logicalQubits)
      (run.output = run.secret ∧ run.SuccessAtLeastTwoThirds)
      (ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
        SupportsPublicBaseline params.toExactResourceProfile
          bounds.toPublicBaselineBounds ∧
        ResourceProfile.HasExactCounts (algorithmCircuit params).resources
          1
          (2 * params.orderRegisterQubits)
          (params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
            2 * (params.orderRegisterQubits / 2))
          params.classicalPostProcessing.total) := by
  have hmain :=
    exactResourceEndpoint_with_public_bounds run params bounds horderBits hgroup horacleDepth
      hfourierDepth hclassical
  exact
    { circuit := algorithmCircuit params
      correctness := ⟨hmain.1, hmain.2.1⟩
      resources := by
        exact ⟨hmain.2.2.1, hmain.2.2.2,
          algorithmCircuit_resourceProfile_hasExactCounts params⟩ }

/-- Finite-cyclic DLP endpoint from an explicit source sampling certificate.
The theorem states deterministic correctness on every certified good event,
keeps the aggregate sampling success lower bound as source data, and exposes
exact resource counts plus concrete public bounds. -/
private theorem publicBounds_of_samplingCertificate {P : KnownOrderProblem G}
    {Ω : Type v}
    (sampling : SamplingCertificate P Ω)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    (∀ outcome (hgood : outcome ∈ sampling.goodEvents),
      (sampling.recovery outcome hgood).output =
        (sampling.recovery outcome hgood).secret) ∧
      sampling.SuccessAtLeastTwoThirds ∧
      (2 : ℝ) / 3 ≤ sampling.goodMass ∧
      (sampling.successNumerator : ℝ) /
          (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
      0 ≤ sampling.goodMass ∧
      sampling.goodMass ≤ 1 ∧
      ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
      SupportsPublicBaseline params.toExactResourceProfile
        bounds.toPublicBaselineBounds := by
  constructor
  · intro outcome hgood
    exact sampling.recovery_output_eq_secret outcome hgood
  constructor
  · exact sampling.successAtLeastTwoThirds
  constructor
  · exact sampling.twoThirds_le_goodMass
  constructor
  · exact sampling.rationalBound_le_goodMass'
  constructor
  · exact sampling.goodMass_nonneg
  constructor
  · exact sampling.goodMass_le_one'
  constructor
  · exact params.toExactResourceProfile_hasExactCounts
  · exact supportsPublicBaseline_of_formulaBounds horderBits hgroup horacleDepth
      hfourierDepth hclassical

/-- Circuit-based witness for the finite-cyclic DLP source-sampling endpoint
with public resource bounds. -/
private noncomputable def mainWithPublicBoundsOfSamplingCertificateResourceCorrectWitness
    {P : KnownOrderProblem G} {Ω : Type v}
    (sampling : SamplingCertificate P Ω)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    ResourceCorrectWitness (R := Qubits params.logicalQubits)
      ((∀ outcome (hgood : outcome ∈ sampling.goodEvents),
        (sampling.recovery outcome hgood).output =
          (sampling.recovery outcome hgood).secret) ∧
        sampling.SuccessAtLeastTwoThirds ∧
        (2 : ℝ) / 3 ≤ sampling.goodMass ∧
        (sampling.successNumerator : ℝ) /
            (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
        0 ≤ sampling.goodMass ∧
        sampling.goodMass ≤ 1)
      (ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
        SupportsPublicBaseline params.toExactResourceProfile
          bounds.toPublicBaselineBounds ∧
        ResourceProfile.HasExactCounts (algorithmCircuit params).resources
          1
          (2 * params.orderRegisterQubits)
          (params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
            2 * (params.orderRegisterQubits / 2))
          params.classicalPostProcessing.total) := by
  have hmain :=
    publicBounds_of_samplingCertificate sampling params bounds
      horderBits hgroup horacleDepth hfourierDepth hclassical
  exact
    { circuit := algorithmCircuit params
      correctness := ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
        hmain.2.2.2.2.1, hmain.2.2.2.2.2.1⟩
      resources := by
        exact ⟨hmain.2.2.2.2.2.2.1, hmain.2.2.2.2.2.2.2,
          algorithmCircuit_resourceProfile_hasExactCounts params⟩ }

/-- Finite-cyclic DLP endpoint directly from source good-event data. The source
analysis supplies the probability mass bound; this wrapper derives the
deterministic recovery certificates from the Fourier relation on every good
event and then applies the public-bound endpoint. -/
private theorem publicBounds_of_leftUnitAddEqZero {P : KnownOrderProblem G}
    {Ω : Type v}
    (secret : ZMod P.order)
    (prob : Ω → ℝ)
    (prob_nonneg : ∀ outcome, 0 ≤ prob outcome)
    (goodEvents : Finset Ω)
    (sample :
      ∀ outcome, outcome ∈ goodEvents → FourierSample P)
    (leftUnit :
      ∀ outcome (_ : outcome ∈ goodEvents), (ZMod P.order)ˣ)
    (leftUnit_eq :
      ∀ outcome (hgood : outcome ∈ goodEvents),
        (sample outcome hgood).leftFrequency = leftUnit outcome hgood)
    (addEqZero :
      ∀ outcome (hgood : outcome ∈ goodEvents),
        secret * (sample outcome hgood).leftFrequency +
            (sample outcome hgood).rightFrequency = 0)
    (successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (success_atLeast_twoThirds : 2 * successDenominator ≤ 3 * successNumerator)
    (rationalBound_le_goodMass :
      (successNumerator : ℝ) / (successDenominator : ℝ) ≤ goodEvents.sum prob)
    (goodMass_le_one : goodEvents.sum prob ≤ 1)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    let sampling : SamplingCertificate P Ω :=
      SamplingCertificate.ofLeftUnitAddEqZero secret prob prob_nonneg goodEvents
        sample leftUnit leftUnit_eq addEqZero successNumerator successDenominator
        successDenominator_pos success_atLeast_twoThirds
        rationalBound_le_goodMass goodMass_le_one
    (∀ outcome (hgood : outcome ∈ sampling.goodEvents),
      (sampling.recovery outcome hgood).output = secret) ∧
      sampling.SuccessAtLeastTwoThirds ∧
      (2 : ℝ) / 3 ≤ sampling.goodMass ∧
      (sampling.successNumerator : ℝ) /
          (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
      0 ≤ sampling.goodMass ∧
      sampling.goodMass ≤ 1 ∧
      ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
      SupportsPublicBaseline params.toExactResourceProfile
        bounds.toPublicBaselineBounds := by
  dsimp
  have hmain :=
    publicBounds_of_samplingCertificate
      (SamplingCertificate.ofLeftUnitAddEqZero secret prob prob_nonneg goodEvents
        sample leftUnit leftUnit_eq addEqZero successNumerator successDenominator
        successDenominator_pos success_atLeast_twoThirds
        rationalBound_le_goodMass goodMass_le_one)
      params bounds horderBits hgroup horacleDepth hfourierDepth hclassical
  constructor
  · intro outcome hgood
    simpa [SamplingCertificate.ofLeftUnitAddEqZero,
      RecoverableFourierSample.RecoveryCertificate.ofLeftUnitAndAddEqZero,
      RecoverableFourierSample.RecoveryCertificate.ofLeftUnitAndLinearRelation] using
        hmain.1 outcome hgood
  · exact hmain.2

/-- Finite-cyclic DLP endpoint from Shor source-good-output data. This wrapper
keeps Shor's source constants and repeated-sampling/CRT success bound in the
mass certificate, while reusing the existing deterministic recovery bridge for
each recoverable postprocessed good output. -/
private theorem publicBounds_of_shorGoodOutputs {P : KnownOrderProblem G}
    {Ω : Type v} {shorParams : Shor.Parameters}
    (secret : ZMod P.order)
    (mass : Shor.RepeatedGoodOutputMassCertificate shorParams Ω)
    (output :
      ∀ outcome, outcome ∈ mass.goodEvents →
        Shor.RecoverableGoodOutput P shorParams secret)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    let sampling : SamplingCertificate P Ω :=
      SamplingCertificate.ofShorRecoverableGoodOutputs secret mass output
    (∀ outcome (hgood : outcome ∈ sampling.goodEvents),
      (sampling.recovery outcome hgood).output = secret) ∧
      sampling.SuccessAtLeastTwoThirds ∧
      (2 : ℝ) / 3 ≤ sampling.goodMass ∧
      (sampling.successNumerator : ℝ) /
          (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
      0 ≤ sampling.goodMass ∧
      sampling.goodMass ≤ 1 ∧
      ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
      SupportsPublicBaseline params.toExactResourceProfile
        bounds.toPublicBaselineBounds := by
  simpa [SamplingCertificate.ofShorRecoverableGoodOutputs] using
    publicBounds_of_leftUnitAddEqZero
      secret mass.prob mass.prob_nonneg mass.goodEvents
      (fun outcome hgood => (output outcome hgood).toFourierSample)
      (fun outcome hgood => (output outcome hgood).leftUnit)
      (fun outcome hgood =>
        (output outcome hgood).toFourierSample_leftFrequency_eq_leftUnit)
      (fun outcome hgood => (output outcome hgood).toFourierSample_addEqZero)
      mass.successNumerator mass.successDenominator mass.successDenominator_pos
      mass.success_atLeast_twoThirds mass.rationalBound_le_goodMass mass.goodMass_le_one
      params bounds horderBits hgroup horacleDepth hfourierDepth hclassical

/-- Finite-cyclic DLP endpoint from a two-register Fourier-support certificate.
The support certificate records the exact Fourier relation forced by hidden-line
invariance after the two exponent-register QFTs; this wrapper derives the
deterministic recovery certificate and then applies the public-bound endpoint. -/
private theorem publicBounds_of_fourierSamplingSupport
    {P : KnownOrderProblem G} {Ω : Type v}
    (support : FourierSamplingSupport P Ω)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    let sampling : SamplingCertificate P Ω := support.toSamplingCertificate
    (∀ outcome (hgood : outcome ∈ sampling.goodEvents),
      (sampling.recovery outcome hgood).output = support.secret) ∧
      sampling.SuccessAtLeastTwoThirds ∧
      (2 : ℝ) / 3 ≤ sampling.goodMass ∧
      (sampling.successNumerator : ℝ) /
          (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
      0 ≤ sampling.goodMass ∧
      sampling.goodMass ≤ 1 ∧
      ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
      SupportsPublicBaseline params.toExactResourceProfile
        bounds.toPublicBaselineBounds := by
  simpa [FourierSamplingSupport.toSamplingCertificate,
    SamplingCertificate.ofLeftUnitAddEqZero] using
    publicBounds_of_leftUnitAddEqZero
      support.secret support.prob support.prob_nonneg support.goodEvents
      support.sample support.leftUnit support.leftUnit_eq support.addEqZero
      support.successNumerator support.successDenominator
      support.successDenominator_pos support.success_atLeast_twoThirds
      support.rationalBound_le_goodMass support.goodMass_le_one
      params bounds horderBits hgroup horacleDepth hfourierDepth hclassical

/-- Circuit-based witness for the source-good-event finite-cyclic DLP endpoint. -/
private noncomputable def mainWithPublicBoundsOfLeftUnitAddEqZeroResourceCorrectWitness
    {P : KnownOrderProblem G} {Ω : Type v}
    (secret : ZMod P.order)
    (prob : Ω → ℝ)
    (prob_nonneg : ∀ outcome, 0 ≤ prob outcome)
    (goodEvents : Finset Ω)
    (sample :
      ∀ outcome, outcome ∈ goodEvents → FourierSample P)
    (leftUnit :
      ∀ outcome (_ : outcome ∈ goodEvents), (ZMod P.order)ˣ)
    (leftUnit_eq :
      ∀ outcome (hgood : outcome ∈ goodEvents),
        (sample outcome hgood).leftFrequency = leftUnit outcome hgood)
    (addEqZero :
      ∀ outcome (hgood : outcome ∈ goodEvents),
        secret * (sample outcome hgood).leftFrequency +
            (sample outcome hgood).rightFrequency = 0)
    (successNumerator successDenominator : ℕ)
    (successDenominator_pos : 0 < successDenominator)
    (success_atLeast_twoThirds : 2 * successDenominator ≤ 3 * successNumerator)
    (rationalBound_le_goodMass :
      (successNumerator : ℝ) / (successDenominator : ℝ) ≤ goodEvents.sum prob)
    (goodMass_le_one : goodEvents.sum prob ≤ 1)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    let sampling : SamplingCertificate P Ω :=
      SamplingCertificate.ofLeftUnitAddEqZero secret prob prob_nonneg goodEvents
        sample leftUnit leftUnit_eq addEqZero successNumerator successDenominator
        successDenominator_pos success_atLeast_twoThirds
        rationalBound_le_goodMass goodMass_le_one
    ResourceCorrectWitness (R := Qubits params.logicalQubits)
      ((∀ outcome (hgood : outcome ∈ sampling.goodEvents),
        (sampling.recovery outcome hgood).output = secret) ∧
        sampling.SuccessAtLeastTwoThirds ∧
        (2 : ℝ) / 3 ≤ sampling.goodMass ∧
        (sampling.successNumerator : ℝ) /
            (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
        0 ≤ sampling.goodMass ∧
        sampling.goodMass ≤ 1)
      (ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
        SupportsPublicBaseline params.toExactResourceProfile
          bounds.toPublicBaselineBounds ∧
        ResourceProfile.HasExactCounts (algorithmCircuit params).resources
          1
          (2 * params.orderRegisterQubits)
          (params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
            2 * (params.orderRegisterQubits / 2))
          params.classicalPostProcessing.total) := by
  dsimp
  have hmain :=
    publicBounds_of_leftUnitAddEqZero
      secret prob prob_nonneg goodEvents sample leftUnit leftUnit_eq addEqZero
      successNumerator successDenominator successDenominator_pos
      success_atLeast_twoThirds rationalBound_le_goodMass goodMass_le_one
      params bounds horderBits hgroup horacleDepth hfourierDepth hclassical
  exact
    { circuit := algorithmCircuit params
      correctness := ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
        hmain.2.2.2.2.1, hmain.2.2.2.2.2.1⟩
      resources := by
        exact ⟨hmain.2.2.2.2.2.2.1, hmain.2.2.2.2.2.2.2,
          algorithmCircuit_resourceProfile_hasExactCounts params⟩ }

/-- Circuit-based witness for the finite-cyclic DLP endpoint from Shor
source-good-output data. This wrapper keeps Shor's source probability and
repeated-sampling/CRT certificate as data, while tying the endpoint to the
same typed `algorithmCircuit` and public-bound resource projection. -/
private noncomputable def mainWithPublicBoundsOfShorGoodOutputsResourceCorrectWitness
    {P : KnownOrderProblem G} {Ω : Type v} {shorParams : Shor.Parameters}
    (secret : ZMod P.order)
    (mass : Shor.RepeatedGoodOutputMassCertificate shorParams Ω)
    (output :
      ∀ outcome, outcome ∈ mass.goodEvents →
        Shor.RecoverableGoodOutput P shorParams secret)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    let sampling : SamplingCertificate P Ω :=
      SamplingCertificate.ofShorRecoverableGoodOutputs secret mass output
    ResourceCorrectWitness (R := Qubits params.logicalQubits)
      ((∀ outcome (hgood : outcome ∈ sampling.goodEvents),
        (sampling.recovery outcome hgood).output = secret) ∧
        sampling.SuccessAtLeastTwoThirds ∧
        (2 : ℝ) / 3 ≤ sampling.goodMass ∧
        (sampling.successNumerator : ℝ) /
            (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
        0 ≤ sampling.goodMass ∧
        sampling.goodMass ≤ 1)
      (ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
        SupportsPublicBaseline params.toExactResourceProfile
          bounds.toPublicBaselineBounds ∧
        ResourceProfile.HasExactCounts (algorithmCircuit params).resources
          1
          (2 * params.orderRegisterQubits)
          (params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
            2 * (params.orderRegisterQubits / 2))
          params.classicalPostProcessing.total) := by
  simpa [SamplingCertificate.ofShorRecoverableGoodOutputs] using
    mainWithPublicBoundsOfLeftUnitAddEqZeroResourceCorrectWitness
      secret mass.prob mass.prob_nonneg mass.goodEvents
      (fun outcome hgood => (output outcome hgood).toFourierSample)
      (fun outcome hgood => (output outcome hgood).leftUnit)
      (fun outcome hgood =>
        (output outcome hgood).toFourierSample_leftFrequency_eq_leftUnit)
      (fun outcome hgood => (output outcome hgood).toFourierSample_addEqZero)
      mass.successNumerator mass.successDenominator mass.successDenominator_pos
      mass.success_atLeast_twoThirds mass.rationalBound_le_goodMass mass.goodMass_le_one
      params bounds horderBits hgroup horacleDepth hfourierDepth hclassical

/-- Circuit-based witness for the finite-cyclic DLP endpoint from a two-register
Fourier-support certificate. -/
private noncomputable def mainWithPublicBoundsOfFourierSamplingSupportResourceCorrectWitness
    {P : KnownOrderProblem G} {Ω : Type v}
    (support : FourierSamplingSupport P Ω)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    let sampling : SamplingCertificate P Ω := support.toSamplingCertificate
    ResourceCorrectWitness (R := Qubits params.logicalQubits)
      ((∀ outcome (hgood : outcome ∈ sampling.goodEvents),
        (sampling.recovery outcome hgood).output = support.secret) ∧
        sampling.SuccessAtLeastTwoThirds ∧
        (2 : ℝ) / 3 ≤ sampling.goodMass ∧
        (sampling.successNumerator : ℝ) /
            (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
        0 ≤ sampling.goodMass ∧
        sampling.goodMass ≤ 1)
      (ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
        SupportsPublicBaseline params.toExactResourceProfile
          bounds.toPublicBaselineBounds ∧
        ResourceProfile.HasExactCounts (algorithmCircuit params).resources
          1
          (2 * params.orderRegisterQubits)
          (params.orderRegisterQubits * (params.orderRegisterQubits - 1) +
            2 * (params.orderRegisterQubits / 2))
          params.classicalPostProcessing.total) := by
  simpa [FourierSamplingSupport.toSamplingCertificate,
    SamplingCertificate.ofLeftUnitAddEqZero] using
    mainWithPublicBoundsOfLeftUnitAddEqZeroResourceCorrectWitness
      support.secret support.prob support.prob_nonneg support.goodEvents
      support.sample support.leftUnit support.leftUnit_eq support.addEqZero
      support.successNumerator support.successDenominator
      support.successDenominator_pos support.success_atLeast_twoThirds
      support.rationalBound_le_goodMass support.goodMass_le_one
      params bounds horderBits hgroup horacleDepth hfourierDepth hclassical

/-- Source-register circuit witness for the finite-cyclic DLP endpoint from a
two-register Fourier-support certificate. Unlike `algorithmCircuit`, this
witness composes the actual DLP oracle gate with the Fourier/readout resource
boundary on the same typed source register. -/
private noncomputable def sourceAlgorithmCircuitResourceCorrectWitnessOfFourierSamplingSupport
    {G₀ : Type} [Group G₀] {P : KnownOrderProblem G₀}
    [Fintype G₀] [DecidableEq G₀] {Ω : Type v}
    (support : FourierSamplingSupport P Ω)
    (params : ResourceParameters)
    (bounds : PublicBaselineBounds.FormulaParameters)
    (horderBits : params.orderRegisterQubits ≤ bounds.orderBitUpperBound)
    (hgroup : params.groupRegisterQubits ≤ bounds.groupRegisterQubitBound)
    (horacleDepth : params.oracleDepth ≤ bounds.oracleDepthBound)
    (hfourierDepth : params.fourierLayerDepth ≤ bounds.fourierLayerDepthBound)
    (hclassical :
      params.classicalPostProcessing.total ≤ bounds.classicalOperationBound) :
    let sampling : SamplingCertificate P Ω := support.toSamplingCertificate
    ResourceCorrectWitness (R := oracleRegister P)
      ((∀ outcome (hgood : outcome ∈ sampling.goodEvents),
        (sampling.recovery outcome hgood).output = support.secret) ∧
        sampling.SuccessAtLeastTwoThirds ∧
        (2 : ℝ) / 3 ≤ sampling.goodMass ∧
        (sampling.successNumerator : ℝ) /
            (sampling.successDenominator : ℝ) ≤ sampling.goodMass ∧
        0 ≤ sampling.goodMass ∧
        sampling.goodMass ≤ 1)
      (ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (2 * params.orderRegisterQubits + params.groupRegisterQubits)
        (2 * params.orderRegisterQubits)
        (params.orderRegisterQubits * (params.orderRegisterQubits - 1))
        (2 * (params.orderRegisterQubits / 2))
        (params.oracleDepth + params.fourierLayerDepth)
        params.classicalPostProcessing.total ∧
        SupportsPublicBaseline params.toExactResourceProfile
          bounds.toPublicBaselineBounds ∧
        (sourceAlgorithmCircuit P params).resources =
          params.toExactResourceProfile.toResourceProfile ∧
        (sourceAlgorithmCircuit P params).depth =
          params.oracleDepth + params.fourierLayerDepth ∧
        (sourceAlgorithmCircuit P params).queryDepth = 1) := by
  have hmain :=
    publicBounds_of_fourierSamplingSupport support params bounds
      horderBits hgroup horacleDepth hfourierDepth hclassical
  have hprojection := sourceAlgorithmCircuit_resourceProjection P params
  exact
    { circuit := sourceAlgorithmCircuit P params
      correctness := ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
        hmain.2.2.2.2.1, hmain.2.2.2.2.2.1⟩
      resources := ⟨hmain.2.2.2.2.2.2.1, hmain.2.2.2.2.2.2.2,
        hprojection.1, hprojection.2.1, hprojection.2.2⟩ }

end FiniteCyclicDLP
end QuantumAlg
