/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularInversion.Schedule

/-!
# Modular-inversion resource and circuit witness

This module attaches resource parameters, source-bound certificates, and
typed circuit witnesses to the selected unit-domain modular-inversion route.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularInversion

/-! ### INV_N gate wrapper -/

/-- Register whose basis labels are unit-domain inversion data states. -/
def register (N : ℕ) [NeZero N] : Register where
  Index := Data N
  fintype := inferInstance
  decEq := inferInstance

/-- The modular-inversion gate `INV_N` on unit-domain data. -/
noncomputable def invGate (N : ℕ) [NeZero N] : Gate (register N) :=
  Gate.ofPerm (Data.invEquiv N).symm

/-- The modular-inversion gate is unitary by construction as a permutation gate. -/
theorem invGate_mem_unitaryGroup (N : ℕ) [NeZero N] :
    ((invGate N : Gate (register N)) : HilbertOperator (register N))
      ∈ Matrix.unitaryGroup (register N).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Clean basis action of `INV_N`: `|u,z,0> ↦ |u,z+u⁻¹,0>`. -/
theorem invGate_apply_ket (N : ℕ) [NeZero N] (x : Data N) :
    (invGate N).apply (PureState.ket (R := register N) x) =
      PureState.ket (R := register N) x.addInverseIntoTarget := by
  rw [invGate, Gate.ofPerm_apply_ket]
  rfl

/-! ### Resource profile parameters -/

/-- Resource parameters attached to the clean modular-inversion endpoint witness.
The fields represent assumed compute-inverse, target-add, and uncompute blocks. -/
structure ResourceParameters where
  /-- Resource profile for the reversible inverse computation. -/
  inverseProfile : ModularArithmeticResourceProfile
  /-- Resource profile for adding the inverse into the target. -/
  targetAddProfile : ModularArithmeticResourceProfile
  /-- Resource profile for uncomputing the inverse work registers. -/
  uncomputeProfile : ModularArithmeticResourceProfile
deriving DecidableEq

namespace ResourceParameters

/-- Compose the modular-inversion resource profile from compute, add, and
uncompute components. -/
def toProfile (params : ResourceParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential params.inverseProfile
    (ModularArithmeticResourceProfile.sequential params.targetAddProfile params.uncomputeProfile)

@[simp] theorem toProfile_circuitDepth (params : ResourceParameters) :
    params.toProfile.circuitDepth =
      params.inverseProfile.circuitDepth +
        (params.targetAddProfile.circuitDepth + params.uncomputeProfile.circuitDepth) :=
  rfl

/-- Component bound parameters for a future refined modular-inversion realization. -/
structure PublicBaselineBounds where
  /-- Public bound for the inverse-computation component. -/
  inverseBound : ModularArithmeticResourceProfile
  /-- Public bound for adding the inverse into the target. -/
  targetAddBound : ModularArithmeticResourceProfile
  /-- Public bound for the uncompute component. -/
  uncomputeBound : ModularArithmeticResourceProfile
deriving DecidableEq

namespace PublicBaselineBounds

/-- The source-facing bound profile obtained by composing the bounded
components of modular inversion. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.inverseBound
    (ModularArithmeticResourceProfile.sequential bounds.targetAddBound bounds.uncomputeBound)

end PublicBaselineBounds

/-- The exact modular-inversion profile supports the composed public baseline. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  upperBound :
    ModularArithmeticResourceProfile.SupportsUpperBound profile bounds.toProfile

/-- Fieldwise source-bound certificate for the clean modular-inversion blocks. -/
structure SourceBoundCertificate
    (params : ResourceParameters) (bounds : PublicBaselineBounds) : Prop where
  inverse_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.inverseProfile bounds.inverseBound
  targetAdd_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.targetAddProfile bounds.targetAddBound
  uncompute_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.uncomputeProfile bounds.uncomputeBound

/-- A componentwise source-bound certificate implies the composed public bound. -/
theorem SourceBoundCertificate.supportsUpperBound
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound params.toProfile bounds.toProfile := by
  simpa [toProfile, PublicBaselineBounds.toProfile] using
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential cert.inverse_le
      (ModularArithmeticResourceProfile.SupportsUpperBound.sequential
        cert.targetAdd_le cert.uncompute_le)

/-- A componentwise source-bound certificate instantiates the public-baseline
predicate. -/
theorem SourceBoundCertificate.supportsPublicBaseline
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    SupportsPublicBaseline params.toProfile bounds where
  upperBound := cert.supportsUpperBound

end ResourceParameters

/-- Resource certificate tied to the selected fixed-round inversion schedule.
It records that the source-backed component bounds are attached to the same
coarse compute/add/uncompute route used by the stage invariant. -/
structure ScheduleResourceCertificate
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds) where
  /-- Selected inversion schedule whose stages are being certified. -/
  schedule : Schedule
  /-- Proof that the schedule uses the selected RNSL17 stage list. -/
  stages_eq : schedule.stages = rnsl17MontgomeryStages
  /-- Componentwise source-bound proof for the selected parameters. -/
  componentBounds : ResourceParameters.SourceBoundCertificate params bounds

namespace ScheduleResourceCertificate

/-- A schedule-tied resource certificate gives the same composed upper bound as
the underlying component certificate. -/
theorem supportsUpperBound
    {params : ResourceParameters} {bounds : ResourceParameters.PublicBaselineBounds}
    (cert : ScheduleResourceCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound params.toProfile bounds.toProfile :=
  cert.componentBounds.supportsUpperBound

/-- A schedule-tied resource certificate instantiates the public-baseline
predicate for the selected inversion route. -/
theorem supportsPublicBaseline
    {params : ResourceParameters} {bounds : ResourceParameters.PublicBaselineBounds}
    (cert : ScheduleResourceCertificate params bounds) :
    ResourceParameters.SupportsPublicBaseline params.toProfile bounds :=
  cert.componentBounds.supportsPublicBaseline

end ScheduleResourceCertificate

/-! ### Circuit witness -/

/-- Typed endpoint witness for unit-domain modular inversion, modeled as one
permutation gate with an attached resource profile.  This compatibility wrapper
is not the decomposed same-Circuit artifact; use
`DecomposedStageWitness.decomposedCleanResourceCorrectWitness` when correctness
and resources must be audited on the compute / target-add / uncompute program
[RNSL17, ECDLP.tex:390-465,753-755]. -/
noncomputable def invCircuit {N : ℕ} [NeZero N]
    (params : ResourceParameters) : Circuit (register N) :=
  Circuit.ofGate "modular-inversion-unit-domain" (invGate N)
    params.toProfile.toResourceProfile params.toProfile.circuitDepth
    params.toProfile.oracleQueries

@[simp] theorem invCircuit_resources {N : ℕ} [NeZero N]
    (params : ResourceParameters) :
    (invCircuit (N := N) params).resources = params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem invCircuit_depth {N : ℕ} [NeZero N]
    (params : ResourceParameters) :
    (invCircuit (N := N) params).depth = params.toProfile.circuitDepth :=
  rfl

@[simp] theorem invCircuit_queryDepth {N : ℕ} [NeZero N]
    (params : ResourceParameters) :
    (invCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for the typed `INV_N` circuit witness. -/
theorem invCircuit_apply_ket {N : ℕ} [NeZero N]
    (params : ResourceParameters) (x : Data N) :
    Circuit.apply (invCircuit (N := N) params)
      (PureState.ket (R := register N) x : StateVector (register N)) =
      (PureState.ket (R := register N) x.addInverseIntoTarget :
        StateVector (register N)) := by
  simpa [invCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register N) => (psi : StateVector (register N)))
      (invGate_apply_ket N x)

/-- Clean public-form basis action:
`|u,z,0> ↦ |u,z+u⁻¹,0>` over `ZMod N`. -/
theorem invCircuit_apply_clean_ket {N : ℕ} [NeZero N]
    (params : ResourceParameters) (u : (ZMod N)ˣ) (z : ZMod N) :
    Circuit.apply (invCircuit (N := N) params)
      (PureState.ket (R := register N)
        ({ input := u, target := z, flag := false } : Data N) :
          StateVector (register N)) =
      (PureState.ket (R := register N)
        ({ input := u, target := z + inverseResidue u, flag := false } : Data N) :
          StateVector (register N)) := by
  simpa [Data.addInverseIntoTarget] using
    invCircuit_apply_ket (N := N) params
      ({ input := u, target := z, flag := false } : Data N)

/-- Resource-correct witness for the unit-domain inversion circuit. -/
noncomputable def invCircuitResourceCorrectWitness
    {N : ℕ} [NeZero N] (params : ResourceParameters) :
    ResourceCorrectWitness (R := register N)
      (∀ x : Data N,
        Circuit.apply (invCircuit (N := N) params)
          (PureState.ket (R := register N) x : StateVector (register N)) =
          (PureState.ket (R := register N) x.addInverseIntoTarget :
            StateVector (register N)))
      ((invCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
        (invCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
        (invCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries) := by
  exact
    { circuit := invCircuit (N := N) params
      correctness := fun x => invCircuit_apply_ket (N := N) params x
      resources := ⟨rfl, rfl, rfl⟩ }

/-! #### External work-register clean interface -/

/-- Unit-domain modular inversion as an external-work clean reversible circuit. -/
noncomputable def invWithWorkCircuit {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data N) Work) :=
  (Data.withWorkCleanMap N Work).circuit params.toProfile

@[simp] theorem invWithWorkCircuit_resources {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (invWithWorkCircuit (N := N) Work params).resources =
      params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem invWithWorkCircuit_depth {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (invWithWorkCircuit (N := N) Work params).depth =
      params.toProfile.circuitDepth :=
  rfl

@[simp] theorem invWithWorkCircuit_queryDepth {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (invWithWorkCircuit (N := N) Work params).queryDepth =
      params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for `INV_N` with an external work register. -/
theorem invWithWorkCircuit_apply_ket {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : Data N) (w : Work) :
    Circuit.apply (invWithWorkCircuit (N := N) Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (x.addInverseIntoTarget, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [invWithWorkCircuit, Data.withWorkCleanMap] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := Data.withWorkCleanMap N Work)
      (profile := params.toProfile) (x := (x, w))

/-- Clean public-form basis action with an external work register:
`|u,z,0,w> ↦ |u,z+u⁻¹,0,w>`. -/
theorem invWithWorkCircuit_apply_clean_ket {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (u : (ZMod N)ˣ) (z : ZMod N) (w : Work) :
    Circuit.apply (invWithWorkCircuit (N := N) Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ input := u, target := z, flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ input := u, target := z + inverseResidue u, flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [Data.addInverseIntoTarget] using
    invWithWorkCircuit_apply_ket (N := N) Work params
      ({ input := u, target := z, flag := false } : Data N) w

/-- Resource-correct witness for the external-work `INV_N` circuit. -/
noncomputable def invWithWorkCircuitResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
      (∀ x : Data N, ∀ w : Work,
        Circuit.apply (invWithWorkCircuit (N := N) Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
              (x.addInverseIntoTarget, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)))
      ((invWithWorkCircuit (N := N) Work params).resources =
          params.toProfile.toResourceProfile ∧
        (invWithWorkCircuit (N := N) Work params).depth =
          params.toProfile.circuitDepth ∧
        (invWithWorkCircuit (N := N) Work params).queryDepth =
          params.toProfile.oracleQueries) := by
  exact
    { circuit := invWithWorkCircuit (N := N) Work params
      correctness := fun x w => invWithWorkCircuit_apply_ket (N := N) Work params x w
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Public modular-inversion endpoint with explicit component resource-bound
assumptions. The theorem keeps the concrete `INV_N` endpoint witness as the
shared object for correctness and resources, but does not expose a gate-level
decomposition. -/
theorem main_with_public_bounds {N : ℕ} [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    (∀ u : (ZMod N)ˣ, ∀ z : ZMod N,
      Circuit.apply (invCircuit (N := N) params)
        (PureState.ket (R := register N)
          ({ input := u, target := z, flag := false } : Data N) :
            StateVector (register N)) =
        (PureState.ket (R := register N)
          ({ input := u, target := z + inverseResidue u, flag := false } : Data N) :
            StateVector (register N))) ∧
      ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        params.toProfile bounds.toProfile ∧
      (invCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
      (invCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
      (invCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries := by
  constructor
  · intro u z
    exact invCircuit_apply_clean_ket (N := N) params u z
  constructor
  · exact componentBounds.supportsPublicBaseline
  constructor
  · exact componentBounds.supportsUpperBound
  · exact ⟨rfl, rfl, rfl⟩

/-- Resource-correct public witness for the bounded unit-domain inversion endpoint. -/
noncomputable def mainWithPublicBoundsResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    ResourceCorrectWitness (R := register N)
      (∀ u : (ZMod N)ˣ, ∀ z : ZMod N,
        Circuit.apply (invCircuit (N := N) params)
          (PureState.ket (R := register N)
            ({ input := u, target := z, flag := false } : Data N) :
              StateVector (register N)) =
          (PureState.ket (R := register N)
            ({ input := u, target := z + inverseResidue u, flag := false } : Data N) :
              StateVector (register N)))
      (ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          params.toProfile bounds.toProfile ∧
        (invCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
        (invCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
        (invCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries) := by
  have hmain := main_with_public_bounds (N := N) params bounds componentBounds
  exact
    { circuit := invCircuit (N := N) params
      correctness := hmain.1
      resources := ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
        hmain.2.2.2.2.1, hmain.2.2.2.2.2⟩ }

/-- Resource-correct witness tied to the selected fixed-round inversion
schedule certificate.  This keeps the correctness theorem, resource fields, and
selected schedule in one proof package while the endpoint remains a typed
permutation boundary rather than a gate-level binary-GCD expansion. -/
noncomputable def scheduleResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (cert : ScheduleResourceCertificate params bounds) :
    ResourceCorrectWitness (R := register N)
      (∀ u : (ZMod N)ˣ, ∀ z : ZMod N,
        Circuit.apply (invCircuit (N := N) params)
          (PureState.ket (R := register N)
            ({ input := u, target := z, flag := false } : Data N) :
              StateVector (register N)) =
          (PureState.ket (R := register N)
            ({ input := u, target := z + inverseResidue u, flag := false } : Data N) :
              StateVector (register N)))
      (ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          params.toProfile bounds.toProfile ∧
        (invCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
        (invCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
        (invCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries) :=
  mainWithPublicBoundsResourceCorrectWitness params bounds cert.componentBounds

end ModularInversion

end QuantumAlg
