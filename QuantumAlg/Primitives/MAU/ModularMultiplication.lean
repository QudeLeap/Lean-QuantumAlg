/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.EncodedBasisMap
public import QuantumAlg.Primitives.MAU.ModularMultiplyAccumulate
public import QuantumAlg.Util.ModularMultiplicationDomain
public import QuantumAlg.Util.ZModUnits

/-!
# Reversible modular multiplication by a unit

Multiplication by a unit of `ZMod N` is a permutation of all residues.  This is
the semantic permutation used by the modular-multiplication circuit target; the
binary-register action is exposed on valid canonical labels through the existing
residue encoding interface.

The clean multiplication-by-unit endpoint is represented as a MAC/swap/
inverse-MAC wrapper over the VBE-style elementary arithmetic route [VBE95,
9511018.tex:333-350]. Beauregard's compact Fourier-space construction and the
Gidney--Ekerå RSA envelope are cited as comparison/resource-envelope context,
not as exact structural support promoted here [Bea02, arxivfact.tex:129-146]
[GE19, main.tex:507-522].
-/

@[expose] public section

namespace QuantumAlg
namespace ModularMultiplication

/-! ### Gate wrapper and resource profile -/

/-- Register whose basis labels are residues modulo `N`. -/
def residueRegister (N : ℕ) [NeZero N] : Register where
  Index := ZMod N
  fintype := inferInstance
  decEq := inferInstance

/-- The semantic modular-multiplication gate `U_{u,N}` on residue labels. -/
noncomputable def unitGate {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    Gate (residueRegister N) :=
  Gate.ofPerm (multiplyByUnitEquiv u).symm

/-- The modular-multiplication gate is unitary by construction as a permutation gate. -/
private theorem unitGate_mem_unitaryGroup {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    ((unitGate u : Gate (residueRegister N)) : HilbertOperator (residueRegister N))
      ∈ Matrix.unitaryGroup (residueRegister N).Index ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Basis action of multiplication by a unit: `U_u |x> = |u*x>`. -/
theorem unitGate_apply_ket {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (x : ZMod N) :
    (unitGate u).apply (PureState.ket (R := residueRegister N) x) =
      PureState.ket (R := residueRegister N) (multiplyByUnit u x) := by
  rw [unitGate, Gate.ofPerm_apply_ket]
  rfl

/-- Resource parameters for `U_{a,N}` as MAC, swap, and inverse-uncompute blocks.
Each field is a concrete exact profile or explicit upper-bound profile supplied
by lower-level counting passes. -/
structure ResourceParameters where
  /-- Mac profile component of this record. -/
  macProfile : ModularArithmeticResourceProfile
  /-- Swap profile component of this record. -/
  swapProfile : ModularArithmeticResourceProfile
  /-- Inverse mac profile component of this record. -/
  inverseMacProfile : ModularArithmeticResourceProfile
deriving DecidableEq

namespace ResourceParameters

/-- Compose the multiplication-by-unit resource profile from MAC, swap, and
inverse MAC. -/
def toProfile (params : ResourceParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential params.macProfile
    (ModularArithmeticResourceProfile.sequential params.swapProfile params.inverseMacProfile)

@[simp] theorem toProfile_logicalQubits (params : ResourceParameters) :
    params.toProfile.logicalQubits =
      max params.macProfile.logicalQubits
        (max params.swapProfile.logicalQubits params.inverseMacProfile.logicalQubits) :=
  rfl

@[simp] theorem toProfile_workQubits (params : ResourceParameters) :
    params.toProfile.workQubits =
      max params.macProfile.workQubits
        (max params.swapProfile.workQubits params.inverseMacProfile.workQubits) :=
  rfl

theorem toProfile_toffoliGates (params : ResourceParameters) :
    params.toProfile.toffoliGates =
      params.macProfile.toffoliGates +
        (params.swapProfile.toffoliGates + params.inverseMacProfile.toffoliGates) :=
  rfl

theorem toProfile_circuitDepth (params : ResourceParameters) :
    params.toProfile.circuitDepth =
      params.macProfile.circuitDepth +
        (params.swapProfile.circuitDepth + params.inverseMacProfile.circuitDepth) :=
  rfl

/-- Concrete component bounds for the MAC / swap / inverse-MAC construction of
`U_{a,N}`. -/
structure PublicBaselineBounds where
  /-- Explicit upper bound for the mac component. -/
  macBound : ModularArithmeticResourceProfile
  /-- Explicit upper bound for the swap component. -/
  swapBound : ModularArithmeticResourceProfile
  /-- Explicit upper bound for the inverse mac component. -/
  inverseMacBound : ModularArithmeticResourceProfile
deriving DecidableEq

namespace PublicBaselineBounds

/-- The source-facing bound profile obtained by composing the three bounded
components of multiplication by a unit. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.macBound
    (ModularArithmeticResourceProfile.sequential bounds.swapBound bounds.inverseMacBound)

end PublicBaselineBounds

/-- The exact modular-multiplication profile supports the composed public
baseline bounds. -/
structure SupportsPublicBaseline
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  upperBound :
    ModularArithmeticResourceProfile.SupportsUpperBound profile bounds.toProfile

/-- Fieldwise source-bound certificate for the component profiles used by
`U_{a,N}`. -/
structure SourceBoundCertificate
    (params : ResourceParameters) (bounds : PublicBaselineBounds) : Prop where
  mac_le :
    ModularArithmeticResourceProfile.SupportsUpperBound params.macProfile bounds.macBound
  swap_le :
    ModularArithmeticResourceProfile.SupportsUpperBound params.swapProfile bounds.swapBound
  inverseMac_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.inverseMacProfile bounds.inverseMacBound

/-- A componentwise source-bound certificate implies the public composed bound
for multiplication by a unit. -/
theorem SourceBoundCertificate.supportsUpperBound
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound params.toProfile bounds.toProfile := by
  simpa [toProfile, PublicBaselineBounds.toProfile] using
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential cert.mac_le
      (ModularArithmeticResourceProfile.SupportsUpperBound.sequential
        cert.swap_le cert.inverseMac_le)

/-- A componentwise source-bound certificate instantiates the source-facing
public baseline predicate. -/
theorem SourceBoundCertificate.supportsPublicBaseline
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    SupportsPublicBaseline params.toProfile bounds where
  upperBound := cert.supportsUpperBound

end ResourceParameters

/-! ### Source-backed VBE package for multiplication by a unit -/

namespace VBECounting

/-- Canonical MAC resource parameters used by the VBE multiplication package. -/
def vbeMACResourceParameters (n : ℕ) :
    ModularMultiplyAccumulate.ResourceParameters :=
  ModularMultiplyAccumulate.VBECounting.vbeMACResourceParameters n

/-- Canonical MAC formula parameters used by the VBE multiplication package. -/
def vbeMACFormulaParameters (n : ℕ) :
    ModularMultiplyAccumulate.ResourceParameters.PublicBaselineBounds.FormulaParameters :=
  ModularMultiplyAccumulate.VBECounting.vbeMACFormulaParameters n

/-- Canonical MAC public baseline bounds used by the VBE multiplication package. -/
def vbeMACPublicBounds (n : ℕ) :
    ModularMultiplyAccumulate.ResourceParameters.PublicBaselineBounds :=
  (vbeMACFormulaParameters n).toPublicBaselineBounds

/-- Canonical MAC public bounds used by the VBE multiplication package. -/
def vbeMACBound (n : ℕ) : ModularArithmeticResourceProfile :=
  (vbeMACPublicBounds n).toProfile

/-- Zero-cost swap profile for the abstract register swap in the VBE
MAC/swap/uncompute wrapper. -/
def vbeSwapProfile : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.zero

/-- Canonical VBE modular-multiplication resource parameters. -/
def vbeUnitMultiplicationResourceParameters (n : ℕ) : ResourceParameters where
  macProfile := (vbeMACResourceParameters n).toProfile
  swapProfile := vbeSwapProfile
  inverseMacProfile := (vbeMACResourceParameters n).toProfile

/-- Canonical VBE modular-multiplication public bounds. -/
def vbeUnitMultiplicationBounds (n : ℕ) : ResourceParameters.PublicBaselineBounds where
  macBound := vbeMACBound n
  swapBound := vbeSwapProfile
  inverseMacBound := vbeMACBound n

/-- The canonical VBE modular-multiplication package supplies its component
source-bound certificate without caller-supplied MAC or swap profiles. -/
theorem vbeUnitMultiplicationSourceBoundCertificate (n : ℕ) (hpos : 0 < n) :
    ResourceParameters.SourceBoundCertificate
      (vbeUnitMultiplicationResourceParameters n)
      (vbeUnitMultiplicationBounds n) := by
  have hmac :=
    ModularMultiplyAccumulate.ResourceParameters.SupportsPublicBaseline.supportsUpperBound
      (ModularMultiplyAccumulate.VBECounting.vbeMACSupportsPublicBaseline n hpos)
  refine
    { mac_le := ?_
      swap_le := ?_
      inverseMac_le := ?_ }
  · simpa [vbeUnitMultiplicationResourceParameters, vbeUnitMultiplicationBounds,
      vbeMACResourceParameters, vbeMACFormulaParameters, vbeMACPublicBounds,
      vbeMACBound] using hmac
  · simpa [vbeUnitMultiplicationResourceParameters, vbeUnitMultiplicationBounds,
      vbeSwapProfile] using
      ModularArithmeticResourceProfile.SupportsUpperBound.refl
        ModularArithmeticResourceProfile.zero
  · simpa [vbeUnitMultiplicationResourceParameters, vbeUnitMultiplicationBounds,
      vbeMACResourceParameters, vbeMACFormulaParameters, vbeMACPublicBounds,
      vbeMACBound] using hmac

end VBECounting

/-! ### Circuit witness -/

/-- Typed circuit witness for multiplication by a unit modulo `N`. The
correctness gate and projected resource profile are attached to the same
`Circuit` object. -/
noncomputable def unitCircuit {N : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (params : ResourceParameters) : Circuit (residueRegister N) :=
  Circuit.ofGate "modular-multiplication-by-unit" (unitGate u)
    params.toProfile.toResourceProfile params.toProfile.circuitDepth
    params.toProfile.oracleQueries

@[simp] theorem unitCircuit_resources {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) :
    (unitCircuit u params).resources = params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem unitCircuit_depth {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) :
    (unitCircuit u params).depth = params.toProfile.circuitDepth :=
  rfl

/-- Basis-state correctness for the typed modular-multiplication circuit
witness. -/
theorem unitCircuit_apply_ket {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) (x : ZMod N) :
    Circuit.apply (unitCircuit u params)
      (PureState.ket (R := residueRegister N) x : StateVector (residueRegister N)) =
      (PureState.ket (R := residueRegister N) (multiplyByUnit u x) :
        StateVector (residueRegister N)) := by
  simpa [unitCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (residueRegister N) =>
      (psi : StateVector (residueRegister N))) (unitGate_apply_ket u x)

/-- Basis action of multiplication by a coprime natural representative. -/
private theorem unitCircuit_apply_coprime_ket {N a : ℕ} [NeZero N]
    (h : Nat.Coprime a N) (params : ResourceParameters) (x : ZMod N) :
    Circuit.apply (unitCircuit (unitOfCoprime (N := N) (a := a) h) params)
      (PureState.ket (R := residueRegister N) x : StateVector (residueRegister N)) =
      (PureState.ket (R := residueRegister N) ((a : ZMod N) * x) :
        StateVector (residueRegister N)) := by
  simpa [multiplyByUnit] using
    unitCircuit_apply_ket (unitOfCoprime (N := N) (a := a) h) params x

/-- Resource-correct witness for modular multiplication by a unit: correctness
and projected resource counters refer to the same typed circuit. -/
noncomputable def unitCircuitResourceCorrectWitness {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters) :
    ResourceCorrectWitness (R := residueRegister N)
      (∀ x : ZMod N,
        Circuit.apply (unitCircuit u params)
          (PureState.ket (R := residueRegister N) x : StateVector (residueRegister N)) =
          (PureState.ket (R := residueRegister N) (multiplyByUnit u x) :
            StateVector (residueRegister N)))
      ((unitCircuit u params).resources = params.toProfile.toResourceProfile ∧
        (unitCircuit u params).depth = params.toProfile.circuitDepth ∧
        (unitCircuit u params).queryDepth = params.toProfile.oracleQueries) := by
  exact
    { circuit := unitCircuit u params
      correctness := fun x => unitCircuit_apply_ket u params x
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Multiplication-by-unit endpoint with explicit component resource bounds.
The component certificate is supplied by the MAC/swap/inverse-MAC construction
chosen by the caller; this endpoint keeps the semantic unit circuit as the
shared object for correctness and resource projection. -/
private theorem main_with_public_bounds {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    (∀ x : ZMod N,
      Circuit.apply (unitCircuit u params)
        (PureState.ket (R := residueRegister N) x : StateVector (residueRegister N)) =
        (PureState.ket (R := residueRegister N) (multiplyByUnit u x) :
          StateVector (residueRegister N))) ∧
      ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        params.toProfile bounds.toProfile ∧
      (unitCircuit u params).resources = params.toProfile.toResourceProfile ∧
      (unitCircuit u params).depth = params.toProfile.circuitDepth ∧
      (unitCircuit u params).queryDepth = params.toProfile.oracleQueries := by
  constructor
  · intro x
    exact unitCircuit_apply_ket u params x
  constructor
  · exact componentBounds.supportsPublicBaseline
  constructor
  · exact componentBounds.supportsUpperBound
  · exact ⟨rfl, rfl, rfl⟩

/-- Multiplication-by-coprime endpoint with explicit component resource bounds. -/
private theorem main_with_public_bounds_of_coprime {N a : ℕ} [NeZero N]
    (h : Nat.Coprime a N) (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    (∀ x : ZMod N,
      Circuit.apply (unitCircuit (unitOfCoprime (N := N) (a := a) h) params)
        (PureState.ket (R := residueRegister N) x : StateVector (residueRegister N)) =
        (PureState.ket (R := residueRegister N) ((a : ZMod N) * x) :
          StateVector (residueRegister N))) ∧
      ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        params.toProfile bounds.toProfile ∧
      (unitCircuit (unitOfCoprime (N := N) (a := a) h) params).resources =
        params.toProfile.toResourceProfile ∧
      (unitCircuit (unitOfCoprime (N := N) (a := a) h) params).depth =
        params.toProfile.circuitDepth ∧
      (unitCircuit (unitOfCoprime (N := N) (a := a) h) params).queryDepth =
        params.toProfile.oracleQueries := by
  have hmain :=
    main_with_public_bounds (unitOfCoprime (N := N) (a := a) h)
      params bounds componentBounds
  constructor
  · intro x
    simpa [multiplyByUnit] using hmain.1 x
  · exact hmain.2

/-- Resource-correct witness for multiplication by a unit with component
resource bounds. -/
private noncomputable def mainWithPublicBoundsResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    ResourceCorrectWitness (R := residueRegister N)
      (∀ x : ZMod N,
        Circuit.apply (unitCircuit u params)
          (PureState.ket (R := residueRegister N) x : StateVector (residueRegister N)) =
          (PureState.ket (R := residueRegister N) (multiplyByUnit u x) :
            StateVector (residueRegister N)))
      (ResourceParameters.SupportsPublicBaseline params.toProfile bounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          params.toProfile bounds.toProfile ∧
        (unitCircuit u params).resources = params.toProfile.toResourceProfile ∧
        (unitCircuit u params).depth = params.toProfile.circuitDepth ∧
        (unitCircuit u params).queryDepth = params.toProfile.oracleQueries) := by
  have hmain := main_with_public_bounds u params bounds componentBounds
  exact
    { circuit := unitCircuit u params
      correctness := hmain.1
      resources := ⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
        hmain.2.2.2.2.1, hmain.2.2.2.2.2⟩ }

/-! ### Bridge to the modular-multiplication domain convention -/

/-- The residue action agrees with the existing unit-carrier multiplication
domain on the underlying residue. -/
private theorem domain_multiplyUnit_residue {N n : ℕ} (D : ModularMultiplicationDomain N n)
    (a x : ModularMultiplicationDomain.UnitCarrier D) :
    multiplyByUnit a (D.unitResidue x) = D.unitResidue (D.multiplyUnit a x) :=
  rfl

/-- On canonical encoded labels for units, the valid-label action agrees with
the existing modular-multiplication-domain canonical-label convention. -/
private theorem encoded_validAction_domain_canonicalLabel {N n : ℕ}
    (D : ModularMultiplicationDomain N n)
    (a x : ModularMultiplicationDomain.UnitCarrier D) :
    Encoded.validAction D.toBinaryResidueEncoding a (D.canonicalLabel x) =
      D.canonicalLabel (D.multiplyUnit a x) := by
  apply Fin.ext
  simp [Encoded.validAction, ModularMultiplicationDomain.canonicalLabel,
    ModularMultiplicationDomain.multiplyUnit, multiplyByUnit]

namespace Encoded

/-- Total binary-label action for multiplication by a unit: canonical residue
labels follow multiplication by `u`, while padding labels are fixed. -/
def totalAction {N n : ℕ} (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if _hx : E.IsValid x then validAction E u x else x

@[simp] theorem totalAction_of_valid {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    totalAction E u x = validAction E u x := by
  simp [totalAction, hx]

@[simp] theorem totalAction_of_padding {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : ¬ E.IsValid x) :
    totalAction E u x = x := by
  simp [totalAction, hx]

private theorem validAction_isValid {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) (x : Fin (2 ^ n)) :
    E.IsValid (validAction E u x) :=
  E.encode_isValid _

private theorem decode_validAction {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) (x : Fin (2 ^ n)) :
    E.decode (validAction E u x) = multiplyByUnit u (E.decode x) :=
  E.decode_encode _

/-- The total multiplication action preserves canonical validity. -/
theorem totalAction_preservesValid {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    E.IsValid (totalAction E u x) := by
  simp [totalAction_of_valid E u x hx, validAction_isValid]

/-- The total multiplication action fixes padding labels. -/
theorem totalAction_preservesPadding {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : ¬ E.IsValid x) :
    ¬ E.IsValid (totalAction E u x) := by
  simpa [totalAction_of_padding E u x hx] using hx

/-- On canonical labels, the total action decodes to multiplication by `u`. -/
theorem decode_totalAction_of_valid {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    E.decode (totalAction E u x) = multiplyByUnit u (E.decode x) := by
  simpa [totalAction_of_valid E u x hx] using decode_validAction E u x

/-- Applying the valid-label multiplication action and then its inverse returns
the original canonical label. -/
theorem validAction_inv_left {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    validAction E u⁻¹ (validAction E u x) = x := by
  calc
    validAction E u⁻¹ (validAction E u x)
        = E.encode (multiplyByUnit u⁻¹ (E.decode (validAction E u x))) := rfl
    _ = E.encode (multiplyByUnit u⁻¹ (multiplyByUnit u (E.decode x))) := by
        rw [decode_validAction]
    _ = E.encode (E.decode x) := by
        simp [multiplyByUnit]
    _ = x := E.encode_decode_of_valid x hx

/-- Applying inverse valid-label multiplication and then the forward action
returns the original canonical label. -/
theorem validAction_inv_right {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    validAction E u (validAction E u⁻¹ x) = x := by
  calc
    validAction E u (validAction E u⁻¹ x)
        = E.encode (multiplyByUnit u (E.decode (validAction E u⁻¹ x))) := rfl
    _ = E.encode (multiplyByUnit u (multiplyByUnit u⁻¹ (E.decode x))) := by
        rw [decode_validAction]
    _ = E.encode (E.decode x) := by
        simp [multiplyByUnit]
    _ = x := E.encode_decode_of_valid x hx

/-- Total permutation of the binary residue-label space induced by
multiplication by a unit, fixing padding labels. -/
def totalPerm {N n : ℕ} (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := totalAction E u
  invFun := totalAction E u⁻¹
  left_inv := by
    intro x
    by_cases hx : E.IsValid x
    · have hvalid : E.IsValid (validAction E u x) :=
        validAction_isValid E u x
      rw [totalAction_of_valid E u x hx]
      rw [totalAction_of_valid E u⁻¹ (validAction E u x) hvalid]
      exact validAction_inv_left E u x hx
    · simp [totalAction_of_padding E u x hx, totalAction_of_padding E u⁻¹ x hx]
  right_inv := by
    intro x
    by_cases hx : E.IsValid x
    · have hvalid : E.IsValid (validAction E u⁻¹ x) :=
        validAction_isValid E u⁻¹ x
      rw [totalAction_of_valid E u⁻¹ x hx]
      rw [totalAction_of_valid E u (validAction E u⁻¹ x) hvalid]
      exact validAction_inv_right E u x hx
    · simp [totalAction_of_padding E u⁻¹ x hx, totalAction_of_padding E u x hx]

@[simp] theorem totalPerm_apply {N n : ℕ}
    (E : BinaryResidueEncoding N n) (u : (ZMod N)ˣ)
    (x : Fin (2 ^ n)) :
    totalPerm E u x = totalAction E u x :=
  rfl

/-- Encoded residue basis-map contract for multiplication by a unit. -/
def totalContract {N n : ℕ} (E : BinaryResidueEncoding N n)
    (u : (ZMod N)ˣ) : EncodedResidueBasisMap E where
  perm := totalPerm E u
  residueMap := multiplyByUnit u
  preservesValid := totalAction_preservesValid E u
  preservesPadding := totalAction_preservesPadding E u
  action_on_valid := decode_totalAction_of_valid E u

end Encoded

/-! ### MAC / swap / uncompute construction -/

/-- Swap the multiplicand and accumulator registers in the MAC layout. -/
def swapMacRegisters {N : ℕ}
    (x : ModularMultiplyAccumulate.Data N) : ModularMultiplyAccumulate.Data N where
  multiplicand := x.accumulator
  accumulator := x.multiplicand
  flag := x.flag

@[simp] theorem swapMacRegisters_multiplicand {N : ℕ}
    (x : ModularMultiplyAccumulate.Data N) :
    (swapMacRegisters x).multiplicand = x.accumulator :=
  rfl

@[simp] theorem swapMacRegisters_accumulator {N : ℕ}
    (x : ModularMultiplyAccumulate.Data N) :
    (swapMacRegisters x).accumulator = x.multiplicand :=
  rfl

@[simp] theorem swapMacRegisters_flag {N : ℕ}
    (x : ModularMultiplyAccumulate.Data N) :
    (swapMacRegisters x).flag = x.flag :=
  rfl

/-- Swap as a reversible MAC-layout basis map. -/
def swapMacEquiv {N : ℕ} : Equiv.Perm (ModularMultiplyAccumulate.Data N) where
  toFun := swapMacRegisters
  invFun := swapMacRegisters
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

@[simp] theorem swapMacEquiv_apply {N : ℕ}
    (x : ModularMultiplyAccumulate.Data N) :
    swapMacEquiv x = swapMacRegisters x :=
  rfl

/-- MAC-register swap with an external work register, leaving work untouched. -/
def swapMacWithWorkEquiv {N : ℕ} (Work : Type) :
    Equiv.Perm (ModularMultiplyAccumulate.Data N × Work) :=
  Equiv.prodCongr swapMacEquiv (Equiv.refl Work)

@[simp] theorem swapMacWithWorkEquiv_apply {N : ℕ} {Work : Type}
    (x : ModularMultiplyAccumulate.Data N) (w : Work) :
    swapMacWithWorkEquiv Work (x, w) = (swapMacRegisters x, w) :=
  rfl

/-- The MAC-register swap leaves the external work register clean. -/
theorem swapMacWithWorkEquiv_preserves_work {N : ℕ} {Work : Type} :
    WorkRegister.Preserves
      (Data := ModularMultiplyAccumulate.Data N) (Work := Work)
      (swapMacWithWorkEquiv Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for the MAC-register swap. -/
def swapMacCleanMap {N : ℕ} (Work : Type) :
    WorkRegister.CleanReversibleMap (ModularMultiplyAccumulate.Data N) Work where
  perm := swapMacWithWorkEquiv Work
  preservesWork := swapMacWithWorkEquiv_preserves_work

@[simp] theorem swapMacCleanMap_perm_apply {N : ℕ} {Work : Type}
    (x : ModularMultiplyAccumulate.Data N) (w : Work) :
    (swapMacCleanMap (N := N) Work).perm (x, w) =
      (swapMacRegisters x, w) :=
  rfl

/-- Multiply by a unit through MAC, swap, and inverse uncomputation. -/
def macSwapUncompute {N : ℕ} (u : (ZMod N)ˣ)
    (x : ModularMultiplyAccumulate.Data N) : ModularMultiplyAccumulate.Data N :=
  (swapMacRegisters (x.addScaled (u : ZMod N))).subScaled ((u⁻¹ : (ZMod N)ˣ) : ZMod N)

/-- Certified clean reversible map for multiplication by a unit through MAC,
swap, and inverse uncomputation. -/
def macSwapUncomputeCleanMap {N : ℕ} (u : (ZMod N)ˣ) (Work : Type) :
    WorkRegister.CleanReversibleMap (ModularMultiplyAccumulate.Data N) Work :=
  WorkRegister.CleanReversibleMap.sequential
    (WorkRegister.CleanReversibleMap.sequential
      (ModularMultiplyAccumulate.Data.withWorkCleanMap (u : ZMod N) Work)
      (swapMacCleanMap (N := N) Work))
    (ModularMultiplyAccumulate.Data.withWorkCleanMap
      (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) Work).inverse

@[simp] theorem macSwapUncomputeCleanMap_perm_apply {N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type}
    (x : ModularMultiplyAccumulate.Data N) (w : Work) :
    (macSwapUncomputeCleanMap u Work).perm (x, w) =
      (macSwapUncompute u x, w) := by
  simp [macSwapUncomputeCleanMap, macSwapUncompute,
    WorkRegister.CleanReversibleMap.sequential_perm,
    WorkRegister.CleanReversibleMap.inverse_perm,
    ModularMultiplyAccumulate.Data.withWorkCleanMap,
    ModularMultiplyAccumulate.Data.withWorkEquiv,
    ModularMultiplyAccumulate.Data.macEquiv]

/-- Clean input state for the MAC/swap/uncompute construction. -/
def cleanInput {N : ℕ} (x : ZMod N) : ModularMultiplyAccumulate.Data N where
  multiplicand := x
  accumulator := 0
  flag := false

/-- Clean output state for multiplication by a unit. -/
def cleanOutput {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    ModularMultiplyAccumulate.Data N where
  multiplicand := (u : ZMod N) * x
  accumulator := 0
  flag := false

/-- Correctness of the MAC/swap/inverse-uncompute construction on clean input. -/
theorem macSwapUncompute_cleanInput {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    macSwapUncompute u (cleanInput x) = cleanOutput u x := by
  ext <;> simp [macSwapUncompute, cleanInput, cleanOutput, swapMacRegisters,
    ModularMultiplyAccumulate.Data.addScaled, ModularMultiplyAccumulate.Data.subScaled]

/-- The MAC/swap/inverse-uncompute wrapper realizes the residue multiplication
action while restoring the accumulator and clean flag. The exact structural
route is the VBE-style MAC support [VBE95, 9511018.tex:333-350]; Beauregard and
Gidney--Ekerå provide comparison/resource-envelope context, not theorem-node
promotion for this wrapper [Bea02, arxivfact.tex:129-146] [GE19,
main.tex:507-522]. -/
theorem macSwapUncompute_cleanInput_multiplyByUnit {N : ℕ}
    (u : (ZMod N)ˣ) (x : ZMod N) :
    macSwapUncompute u (cleanInput x) =
      ({ multiplicand := multiplyByUnit u x
         accumulator := 0
         flag := false } : ModularMultiplyAccumulate.Data N) := by
  simpa [cleanOutput, multiplyByUnit] using
    macSwapUncompute_cleanInput u x

/-- The certified clean map realizes multiplication by a unit on clean input
while preserving the external work register. -/
theorem macSwapUncomputeCleanMap_perm_cleanInput {N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type} (x : ZMod N) (w : Work) :
    (macSwapUncomputeCleanMap u Work).perm (cleanInput x, w) =
      (cleanOutput u x, w) := by
  rw [macSwapUncomputeCleanMap_perm_apply, macSwapUncompute_cleanInput]

/-- The certified clean map realizes the public multiplication-by-unit residue
action and restores the external work register, accumulator, and clean flag. -/
private theorem macSwapUncomputeCleanMap_perm_cleanInput_multiplyByUnit {N : ℕ}
    (u : (ZMod N)ˣ) {Work : Type} (x : ZMod N) (w : Work) :
    (macSwapUncomputeCleanMap u Work).perm (cleanInput x, w) =
      (({ multiplicand := multiplyByUnit u x
          accumulator := 0
          flag := false } : ModularMultiplyAccumulate.Data N), w) := by
  rw [macSwapUncomputeCleanMap_perm_apply, macSwapUncompute_cleanInput_multiplyByUnit]

/-! ### MAC / swap / uncompute circuit endpoint -/

/-- Typed circuit wrapper for the clean MAC/swap/inverse-uncompute
multiplication construction. -/
noncomputable def macSwapUncomputeCircuit {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register
      (ModularMultiplyAccumulate.Data N) Work) :=
  (macSwapUncomputeCleanMap u Work).circuit params.toProfile

@[simp] theorem macSwapUncomputeCircuit_resources {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (macSwapUncomputeCircuit u Work params).resources =
      params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem macSwapUncomputeCircuit_depth {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (macSwapUncomputeCircuit u Work params).depth =
      params.toProfile.circuitDepth :=
  rfl

@[simp] theorem macSwapUncomputeCircuit_queryDepth {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (macSwapUncomputeCircuit u Work params).queryDepth =
      params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for the typed clean MAC/swap/uncompute circuit. -/
theorem macSwapUncomputeCircuit_apply_ket {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters)
    (x : ModularMultiplyAccumulate.Data N) (w : Work) :
    Circuit.apply (macSwapUncomputeCircuit u Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register
          (ModularMultiplyAccumulate.Data N) Work) (x, w) :
        StateVector
          (WorkRegister.CleanReversibleMap.register
            (ModularMultiplyAccumulate.Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register
          (ModularMultiplyAccumulate.Data N) Work)
        (macSwapUncompute u x, w) :
        StateVector
          (WorkRegister.CleanReversibleMap.register
            (ModularMultiplyAccumulate.Data N) Work)) := by
  simpa [macSwapUncomputeCircuit] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := macSwapUncomputeCleanMap u Work)
      (profile := params.toProfile) (x := (x, w))

/-- Clean-input correctness for the typed MAC/swap/uncompute circuit. -/
private theorem macSwapUncomputeCircuit_apply_clean_ket {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : ZMod N) (w : Work) :
    Circuit.apply (macSwapUncomputeCircuit u Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register
          (ModularMultiplyAccumulate.Data N) Work) (cleanInput x, w) :
        StateVector
          (WorkRegister.CleanReversibleMap.register
            (ModularMultiplyAccumulate.Data N) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register
          (ModularMultiplyAccumulate.Data N) Work)
        (({ multiplicand := multiplyByUnit u x
            accumulator := 0
            flag := false } : ModularMultiplyAccumulate.Data N), w) :
        StateVector
          (WorkRegister.CleanReversibleMap.register
            (ModularMultiplyAccumulate.Data N) Work)) := by
  rw [macSwapUncomputeCircuit_apply_ket]
  simp [macSwapUncompute_cleanInput_multiplyByUnit]

/-- Resource-correct witness for the typed clean MAC/swap/uncompute circuit. -/
noncomputable def macSwapUncomputeCircuitResourceCorrectWitness
    {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register
        (ModularMultiplyAccumulate.Data N) Work)
      (∀ x : ModularMultiplyAccumulate.Data N × Work,
        Circuit.apply (macSwapUncomputeCircuit u Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register
              (ModularMultiplyAccumulate.Data N) Work) x :
            StateVector
              (WorkRegister.CleanReversibleMap.register
                (ModularMultiplyAccumulate.Data N) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register
              (ModularMultiplyAccumulate.Data N) Work)
            ((macSwapUncompute u x.1), x.2) :
            StateVector
              (WorkRegister.CleanReversibleMap.register
                (ModularMultiplyAccumulate.Data N) Work)))
      ((macSwapUncomputeCircuit u Work params).resources =
          params.toProfile.toResourceProfile ∧
        (macSwapUncomputeCircuit u Work params).depth =
          params.toProfile.circuitDepth ∧
        (macSwapUncomputeCircuit u Work params).queryDepth =
          params.toProfile.oracleQueries) := by
  exact
    { circuit := macSwapUncomputeCircuit u Work params
      correctness := fun x =>
        macSwapUncomputeCircuit_apply_ket u Work params x.1 x.2
      resources := ⟨rfl, rfl, rfl⟩ }

end ModularMultiplication
end QuantumAlg
