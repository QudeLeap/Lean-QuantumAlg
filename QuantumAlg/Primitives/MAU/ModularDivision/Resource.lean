/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularDivision.Pipeline
public import QuantumAlg.Primitives.MAU.ModularMultiplication

/-!
# Modular-division resource and circuit witness

This module attaches resource parameters, source-bound certificates, and
typed circuit witnesses to the selected unit-denominator modular-division
pipeline.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularDivision

/-! ### DIV_N gate wrapper -/

/-- Register whose basis labels are unit-denominator division data states. -/
def register (N : ℕ) [NeZero N] : Register where
  Index := Data N
  fintype := inferInstance
  decEq := inferInstance

/-- The modular-division gate `DIV_N` on unit-denominator data. -/
noncomputable def divGate (N : ℕ) [NeZero N] : Gate (register N) :=
  Gate.ofPerm (Data.divEquiv N).symm

/-- The modular-division gate is unitary by construction as a permutation gate. -/
theorem divGate_mem_unitaryGroup (N : ℕ) [NeZero N] :
    ((divGate N : Gate (register N)) : HilbertOperator (register N))
      ∈ Matrix.unitaryGroup (register N).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Clean basis action of `DIV_N`: `|u,v,z,0> ↦ |u,v,z+v*u⁻¹,0>`. -/
theorem divGate_apply_ket (N : ℕ) [NeZero N] (x : Data N) :
    (divGate N).apply (PureState.ket (R := register N) x) =
      PureState.ket (R := register N) x.addQuotientIntoTarget := by
  rw [divGate, Gate.ofPerm_apply_ket]
  rfl

/-! ### Resource profile parameters -/

/-- Resource parameters attached to the clean modular-division endpoint witness.
The fields represent assumed inversion, quotient multiplication, target-add, and
uncompute blocks. -/
structure ResourceParameters where
  /-- Resource profile for modular inversion of the denominator. -/
  inversionProfile : ModularArithmeticResourceProfile
  /-- Resource profile for multiplying the numerator by the inverse. -/
  multiplicationProfile : ModularArithmeticResourceProfile
  /-- Resource profile for adding the quotient into the target. -/
  targetAddProfile : ModularArithmeticResourceProfile
  /-- Resource profile for uncomputing scratch registers. -/
  uncomputeProfile : ModularArithmeticResourceProfile
deriving DecidableEq

namespace ResourceParameters

/-- Compose the modular-division resource profile from inversion,
multiplication, add, and uncompute components. -/
def toProfile (params : ResourceParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential params.inversionProfile
    (ModularArithmeticResourceProfile.sequential params.multiplicationProfile
      (ModularArithmeticResourceProfile.sequential params.targetAddProfile
        params.uncomputeProfile))

@[simp] theorem toProfile_circuitDepth (params : ResourceParameters) :
    params.toProfile.circuitDepth =
      params.inversionProfile.circuitDepth +
        (params.multiplicationProfile.circuitDepth +
          (params.targetAddProfile.circuitDepth + params.uncomputeProfile.circuitDepth)) :=
  rfl

/-- Component bound parameters for a future refined modular-division realization. -/
structure PublicBaselineBounds where
  /-- Public bound for the inversion component. -/
  inversionBound : ModularArithmeticResourceProfile
  /-- Public bound for the multiplication component. -/
  multiplicationBound : ModularArithmeticResourceProfile
  /-- Public bound for the target-add component. -/
  targetAddBound : ModularArithmeticResourceProfile
  /-- Public bound for the uncompute component. -/
  uncomputeBound : ModularArithmeticResourceProfile
deriving DecidableEq

namespace PublicBaselineBounds

/-- The source-facing bound profile obtained by composing the bounded
components of modular division. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.inversionBound
    (ModularArithmeticResourceProfile.sequential bounds.multiplicationBound
      (ModularArithmeticResourceProfile.sequential bounds.targetAddBound
        bounds.uncomputeBound))

end PublicBaselineBounds

/-- The exact modular-division profile supports the composed public baseline. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  upperBound :
    ModularArithmeticResourceProfile.SupportsUpperBound profile bounds.toProfile

/-- Fieldwise source-bound certificate for the clean modular-division blocks. -/
structure SourceBoundCertificate
    (params : ResourceParameters) (bounds : PublicBaselineBounds) : Prop where
  inversion_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.inversionProfile bounds.inversionBound
  multiplication_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.multiplicationProfile bounds.multiplicationBound
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
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential cert.inversion_le
      (ModularArithmeticResourceProfile.SupportsUpperBound.sequential
        cert.multiplication_le
        (ModularArithmeticResourceProfile.SupportsUpperBound.sequential
          cert.targetAdd_le cert.uncompute_le))

/-- A componentwise source-bound certificate instantiates the public-baseline
predicate. -/
theorem SourceBoundCertificate.supportsPublicBaseline
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    SupportsPublicBaseline params.toProfile bounds where
  upperBound := cert.supportsUpperBound

end ResourceParameters

/-- Resource certificate tied to the selected inverse/multiply/add/uncompute
division pipeline. -/
structure PipelineResourceCertificate
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds) where
  /-- Selected division pipeline schedule being certified. -/
  schedule : PipelineSchedule
  /-- Proof that the schedule uses the selected inverse-multiply-add-uncompute stages. -/
  stages_eq : schedule.stages = inverseMultiplyAddUncomputeStages
  /-- Componentwise source-bound proof for the selected parameters. -/
  componentBounds : ResourceParameters.SourceBoundCertificate params bounds

namespace PipelineResourceCertificate

/-- A pipeline-tied resource certificate gives the same composed upper bound as
the underlying component certificate. -/
theorem supportsUpperBound
    {params : ResourceParameters} {bounds : ResourceParameters.PublicBaselineBounds}
    (cert : PipelineResourceCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound params.toProfile bounds.toProfile :=
  cert.componentBounds.supportsUpperBound

/-- A pipeline-tied resource certificate instantiates the public-baseline
predicate for the selected division route. -/
theorem supportsPublicBaseline
    {params : ResourceParameters} {bounds : ResourceParameters.PublicBaselineBounds}
    (cert : PipelineResourceCertificate params bounds) :
    ResourceParameters.SupportsPublicBaseline params.toProfile bounds :=
  cert.componentBounds.supportsPublicBaseline

end PipelineResourceCertificate

/-! ### Circuit witness -/

/-- Typed endpoint witness for unit-denominator modular division, modeled as one
permutation gate with an attached resource profile. -/
noncomputable def divCircuit {N : ℕ} [NeZero N]
    (params : ResourceParameters) : Circuit (register N) :=
  Circuit.ofGate "modular-division-unit-denominator" (divGate N)
    params.toProfile.toResourceProfile params.toProfile.circuitDepth
    params.toProfile.oracleQueries

@[simp] theorem divCircuit_resources {N : ℕ} [NeZero N]
    (params : ResourceParameters) :
    (divCircuit (N := N) params).resources = params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem divCircuit_depth {N : ℕ} [NeZero N]
    (params : ResourceParameters) :
    (divCircuit (N := N) params).depth = params.toProfile.circuitDepth :=
  rfl

@[simp] theorem divCircuit_queryDepth {N : ℕ} [NeZero N]
    (params : ResourceParameters) :
    (divCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for the typed `DIV_N` circuit witness. -/
theorem divCircuit_apply_ket {N : ℕ} [NeZero N]
    (params : ResourceParameters) (x : Data N) :
    Circuit.apply (divCircuit (N := N) params)
      (PureState.ket (R := register N) x : StateVector (register N)) =
      (PureState.ket (R := register N) x.addQuotientIntoTarget :
        StateVector (register N)) := by
  simpa [divCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register N) => (psi : StateVector (register N)))
      (divGate_apply_ket N x)

/-- Clean public-form basis action:
`|u,v,z,0> ↦ |u,v,z+v*u⁻¹,0>` over `ZMod N`. -/
theorem divCircuit_apply_clean_ket {N : ℕ} [NeZero N]
    (params : ResourceParameters) (u : (ZMod N)ˣ) (v z : ZMod N) :
    Circuit.apply (divCircuit (N := N) params)
      (PureState.ket (R := register N)
        ({ denominator := u, numerator := v, target := z, flag := false } : Data N) :
          StateVector (register N)) =
      (PureState.ket (R := register N)
        ({ denominator := u
           numerator := v
           target := z + quotientResidue u v
           flag := false } : Data N) :
          StateVector (register N)) := by
  simpa [Data.addQuotientIntoTarget] using
    divCircuit_apply_ket (N := N) params
      ({ denominator := u, numerator := v, target := z, flag := false } : Data N)

/-- Resource-correct witness for the unit-denominator division circuit. -/
noncomputable def divCircuitResourceCorrectWitness
    {N : ℕ} [NeZero N] (params : ResourceParameters) :
    ResourceCorrectWitness (R := register N)
      (∀ x : Data N,
        Circuit.apply (divCircuit (N := N) params)
          (PureState.ket (R := register N) x : StateVector (register N)) =
          (PureState.ket (R := register N) x.addQuotientIntoTarget :
            StateVector (register N)))
      ((divCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
        (divCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
        (divCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries) := by
  exact
    { circuit := divCircuit (N := N) params
      correctness := fun x => divCircuit_apply_ket (N := N) params x
      resources := ⟨rfl, rfl, rfl⟩ }

/-! #### External work-register clean interface -/

/-- Unit-denominator modular division as an external-work clean reversible circuit. -/
noncomputable def divWithWorkCircuit {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data N) Work) :=
  (Data.withWorkCleanMap N Work).circuit params.toProfile

@[simp] theorem divWithWorkCircuit_resources {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (divWithWorkCircuit (N := N) Work params).resources =
      params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem divWithWorkCircuit_depth {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (divWithWorkCircuit (N := N) Work params).depth =
      params.toProfile.circuitDepth :=
  rfl

@[simp] theorem divWithWorkCircuit_queryDepth {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (divWithWorkCircuit (N := N) Work params).queryDepth =
      params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for `DIV_N` with an external work register. -/
theorem divWithWorkCircuit_apply_ket {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : Data N) (w : Work) :
    Circuit.apply (divWithWorkCircuit (N := N) Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (x.addQuotientIntoTarget, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [divWithWorkCircuit, Data.withWorkCleanMap] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := Data.withWorkCleanMap N Work)
      (profile := params.toProfile) (x := (x, w))

/-- Clean public-form basis action with an external work register:
`|u,v,z,0,w> ↦ |u,v,z+v*u⁻¹,0,w>`. -/
theorem divWithWorkCircuit_apply_clean_ket {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (u : (ZMod N)ˣ) (v z : ZMod N) (w : Work) :
    Circuit.apply (divWithWorkCircuit (N := N) Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ denominator := u, numerator := v, target := z, flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
          (({ denominator := u
              numerator := v
              target := z + quotientResidue u v
              flag := false } : Data N), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) := by
  simpa [Data.addQuotientIntoTarget] using
    divWithWorkCircuit_apply_ket (N := N) Work params
      ({ denominator := u, numerator := v, target := z, flag := false } : Data N) w

/-- Resource-correct witness for the external-work `DIV_N` circuit. -/
noncomputable def divWithWorkCircuitResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
      (∀ x : Data N, ∀ w : Work,
        Circuit.apply (divWithWorkCircuit (N := N) Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work) (x, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data N) Work)
              (x.addQuotientIntoTarget, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data N) Work)))
      ((divWithWorkCircuit (N := N) Work params).resources =
          params.toProfile.toResourceProfile ∧
        (divWithWorkCircuit (N := N) Work params).depth =
          params.toProfile.circuitDepth ∧
        (divWithWorkCircuit (N := N) Work params).queryDepth =
          params.toProfile.oracleQueries) := by
  exact
    { circuit := divWithWorkCircuit (N := N) Work params
      correctness := fun x w => divWithWorkCircuit_apply_ket (N := N) Work params x w
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Public modular-division endpoint with explicit component resource-bound
assumptions. The theorem keeps the concrete `DIV_N` endpoint witness as the
shared object for correctness and resources, but does not expose a gate-level
decomposition. -/
theorem main_with_public_bounds {N : ℕ} [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    (∀ u : (ZMod N)ˣ, ∀ v z : ZMod N,
      Circuit.apply (divCircuit (N := N) params)
        (PureState.ket (R := register N)
          ({ denominator := u, numerator := v, target := z, flag := false } : Data N) :
            StateVector (register N)) =
        (PureState.ket (R := register N)
          ({ denominator := u
             numerator := v
             target := z + quotientResidue u v
             flag := false } : Data N) :
            StateVector (register N))) ∧
      ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        params.toProfile bounds.toProfile ∧
      (divCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
      (divCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
      (divCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries := by
  constructor
  · intro u v z
    exact divCircuit_apply_clean_ket (N := N) params u v z
  constructor
  · exact componentBounds.supportsPublicBaseline
  constructor
  · exact componentBounds.supportsUpperBound
  · exact ⟨rfl, rfl, rfl⟩

/-- Resource-correct public witness for the bounded unit-denominator division endpoint. -/
noncomputable def mainWithPublicBoundsResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    ResourceCorrectWitness (R := register N)
      (∀ u : (ZMod N)ˣ, ∀ v z : ZMod N,
        Circuit.apply (divCircuit (N := N) params)
          (PureState.ket (R := register N)
            ({ denominator := u, numerator := v, target := z, flag := false } : Data N) :
              StateVector (register N)) =
          (PureState.ket (R := register N)
            ({ denominator := u
               numerator := v
               target := z + quotientResidue u v
               flag := false } : Data N) :
              StateVector (register N)))
      (ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          params.toProfile bounds.toProfile ∧
        (divCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
        (divCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
        (divCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries) := by
  have hmain := main_with_public_bounds (N := N) params bounds componentBounds
  exact
    { circuit := divCircuit (N := N) params
      correctness := hmain.1
      resources := ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
        hmain.2.2.2.2.1, hmain.2.2.2.2.2⟩ }

/-- Resource-correct witness tied to the selected division pipeline certificate.
The endpoint remains a typed permutation boundary, while this wrapper records
that its resource assumptions follow the explicit inverse/multiply/add/uncompute
pipeline. -/
noncomputable def pipelineResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (cert : PipelineResourceCertificate params bounds) :
    ResourceCorrectWitness (R := register N)
      (∀ u : (ZMod N)ˣ, ∀ v z : ZMod N,
        Circuit.apply (divCircuit (N := N) params)
          (PureState.ket (R := register N)
            ({ denominator := u, numerator := v, target := z, flag := false } : Data N) :
              StateVector (register N)) =
          (PureState.ket (R := register N)
            ({ denominator := u
               numerator := v
               target := z + quotientResidue u v
               flag := false } : Data N) :
              StateVector (register N)))
      (ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          params.toProfile bounds.toProfile ∧
        (divCircuit (N := N) params).resources = params.toProfile.toResourceProfile ∧
        (divCircuit (N := N) params).depth = params.toProfile.circuitDepth ∧
        (divCircuit (N := N) params).queryDepth = params.toProfile.oracleQueries) :=
  mainWithPublicBoundsResourceCorrectWitness params bounds cert.componentBounds

end ModularDivision

end QuantumAlg
