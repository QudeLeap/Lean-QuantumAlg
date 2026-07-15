/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Basic

/-!
# Generic affine point-addition endpoint

This module packages the uncontrolled generic affine ECADD endpoint, including
its staged slope/coordinate/target-update support model, clean external-work
interface, resource profile, and public-bounds witness.  The generic affine
route follows [PZ03, ecc.tex:525-640] and the RNSL17 affine point-addition
boundary [RNSL17, ECDLP.tex:488-580].
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass

variable {p : ℕ}

namespace GenericPointAddition

/-- Generic-addition input subtype shared by uncontrolled and controlled ECADD
endpoints. -/
abbrev Input (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) :=
  {P : AffinePoint E // GenericAddDomain P Q}

/-- The input subtype exposes the reusable generic-addition predicate. -/
theorem input_generic {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (P : Input E Q) :
    GenericAddDomain P.1 Q :=
  P.2

/-- Encode the finite affine point carried by a generic-addition input. -/
def encodeInput {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) (P : Input E Q) :
    Fin (2 ^ n) × Fin (2 ^ n) :=
  P.1.encode encoding

/-- Encoded generic-addition inputs are valid finite-point encodings. -/
theorem encodeInput_isValid {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) (P : Input E Q) :
    encoding.IsValidFiniteEncoding (encodeInput encoding P) :=
  P.1.encode_isValid encoding

/-- Decoding an encoded generic-addition input recovers its affine coordinates. -/
theorem encodeInput_decodes {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) (P : Input E Q) :
    encoding.decodeFiniteCoordinates (encodeInput encoding P) = (P.1.x, P.1.y) :=
  AffinePoint.decodeFiniteCoordinates_encode encoding P.1

/-- Equality of encoded generic-addition inputs gives equality of their affine
coordinates. -/
theorem encodeInput_ext {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) {P R : Input E Q}
    (h : encodeInput encoding P = encodeInput encoding R) :
    P.1.x = R.1.x ∧ P.1.y = R.1.y :=
  AffinePoint.encode_ext encoding h

/-- Encoded endpoint evidence for generic ECADD: the input encoding decodes to
the input coordinates, the output encoding decodes to the generic affine
endpoint coordinates, and that endpoint is the affine group-law sum. -/
structure EncodedEndpointEvidence (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {n : ℕ}
    (encoding : PointEncoding E n) (P : Input E Q) : Prop where
  inputValid :
    encoding.IsValidFiniteEncoding (encodeInput encoding P)
  inputDecodes :
    encoding.decodeFiniteCoordinates (encodeInput encoding P) = (P.1.x, P.1.y)
  outputValid :
    encoding.IsValidFiniteEncoding ((genericAddPoint E P.1 Q P.2).encode encoding)
  outputDecodes :
    encoding.decodeFiniteCoordinates ((genericAddPoint E P.1 Q P.2).encode encoding) =
      (genericAddX E P.1 Q, genericAddY E P.1 Q)
  outputGroupLaw :
    P.1.toMathlib + Q.toMathlib =
      WeierstrassCurve.Affine.Point.some
        (genericAddX E P.1 Q) (genericAddY E P.1 Q)
        (genericAdd_nonsingular E P.1 Q P.2)

/-- Encoded generic ECADD endpoint evidence follows from the finite coordinate
encoding and the generic affine group law [PZ03, ecc.tex:525-640]. -/
theorem encodedEndpointEvidence (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {n : ℕ}
    (encoding : PointEncoding E n) (P : Input E Q) :
    EncodedEndpointEvidence E Q encoding P := by
  exact
    { inputValid := encodeInput_isValid encoding P
      inputDecodes := encodeInput_decodes encoding P
      outputValid := (genericAddPoint E P.1 Q P.2).encode_isValid encoding
      outputDecodes := by
        simpa using
          AffinePoint.decodeFiniteCoordinates_encode encoding
            (genericAddPoint E P.1 Q P.2)
      outputGroupLaw := genericAdd_group_law_mathlib E P.1 Q P.2 }

/-- Data registers for generic affine point addition by a fixed finite point. -/
structure Data (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) where
  /-- Generic-domain input point for adding the fixed addend `Q`. -/
  input : Input E Q
  /-- Target `x` coordinate accumulator. -/
  targetX : ZMod p
  /-- Target `y` coordinate accumulator. -/
  targetY : ZMod p
  /-- Temporary cleanup flag carried by the addition endpoint. -/
  flag : Bool
deriving DecidableEq

noncomputable instance instFintypeData (E : PrimeFieldShortWeierstrass p) [NeZero p]
    (Q : AffinePoint E) : Fintype (Data E Q) := by
  classical
  let e : Data E Q ≃ (Input E Q × ZMod p × ZMod p × Bool) := {
    toFun := fun x => (x.input, (x.targetX, (x.targetY, x.flag)))
    invFun := fun x =>
      { input := x.1, targetX := x.2.1, targetY := x.2.2.1, flag := x.2.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨input, rest⟩
      rcases rest with ⟨targetX, rest'⟩
      rcases rest' with ⟨targetY, flag⟩
      rfl
  }
  exact Fintype.ofEquiv
    (Input E Q × ZMod p × ZMod p × Bool) e.symm

namespace Data

/-- Encode the finite affine input carried by a point-addition register label. -/
def encodedInput {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) (x : Data E Q) :
    Fin (2 ^ n) × Fin (2 ^ n) :=
  encodeInput encoding x.input

/-- Register-label inputs decode to valid finite affine encodings. -/
theorem encodedInput_isValid {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) (x : Data E Q) :
    encoding.IsValidFiniteEncoding (x.encodedInput encoding) :=
  encodeInput_isValid encoding x.input

/-- Equality of encoded register-label inputs gives equality of the underlying
affine coordinates at the circuit boundary. -/
theorem encodedInput_ext {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) {x y : Data E Q}
    (h : x.encodedInput encoding = y.encodedInput encoding) :
    x.input.1.x = y.input.1.x ∧ x.input.1.y = y.input.1.y :=
  encodeInput_ext encoding h

/-! #### Generic ECADD stage support -/

/-- Coarse stages of the generic affine ECADD support pipeline.  RNSL17's
controlled addition program computes the slope, updates coordinates, writes the
target registers, and uncomputes auxiliaries under the generic affine
assumption [RNSL17, ECDLP.tex:488-580,650-696]. -/
inductive Stage where
  | slope
  | coordinateUpdate
  | targetWrite
  | cleanup
deriving DecidableEq

/-- Intermediate state for the generic ECADD stage proof. -/
structure StageState (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) where
  /-- Generic-domain input point for the current staged addition. -/
  input : Input E Q
  /-- Target `x` coordinate accumulator. -/
  targetX : ZMod p
  /-- Target `y` coordinate accumulator. -/
  targetY : ZMod p
  /-- Scratch value holding the affine slope. -/
  slopeScratch : ZMod p
  /-- Scratch value holding the computed result `x` coordinate. -/
  resultX : ZMod p
  /-- Scratch value holding the computed result `y` coordinate. -/
  resultY : ZMod p
  /-- Temporary cleanup flag for the staged endpoint. -/
  flag : Bool
deriving DecidableEq

namespace StageState

/-- Initial clean state before slope computation. -/
def initial {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) : StageState E Q where
  input := P
  targetX := targetX
  targetY := targetY
  slopeScratch := 0
  resultX := 0
  resultY := 0
  flag := false

/-- Compute the generic affine slope into scratch. -/
def computeSlope {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} (s : StageState E Q) : StageState E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  slopeScratch := genericAddSlope E s.input.1 Q
  resultX := s.resultX
  resultY := s.resultY
  flag := s.flag

/-- Compute the affine output coordinates from the slope. -/
def computeCoordinates {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} (s : StageState E Q) : StageState E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  slopeScratch := s.slopeScratch
  resultX := genericAddXFromSlope E s.input.1 Q s.slopeScratch
  resultY := genericAddYFromSlope E s.input.1 Q s.slopeScratch
  flag := s.flag

@[simp] theorem computeCoordinates_after_computeSlope_resultX
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (s : StageState E Q) :
    (computeCoordinates (computeSlope s)).resultX = genericAddX E s.input.1 Q :=
  rfl

@[simp] theorem computeCoordinates_after_computeSlope_resultY
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (s : StageState E Q) :
    (computeCoordinates (computeSlope s)).resultY = genericAddY E s.input.1 Q :=
  rfl

/-- Write the computed coordinates into the target registers. -/
def writeTarget {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} (s : StageState E Q) : StageState E Q where
  input := s.input
  targetX := s.targetX + s.resultX
  targetY := s.targetY + s.resultY
  slopeScratch := s.slopeScratch
  resultX := s.resultX
  resultY := s.resultY
  flag := s.flag

/-- Uncompute the intermediate slope/result scratch registers. -/
def cleanup {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} (s : StageState E Q) : StageState E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  slopeScratch := 0
  resultX := 0
  resultY := 0
  flag := false

/-- Execute one named generic ECADD support stage. -/
def step {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} (stage : Stage) (s : StageState E Q) :
    StageState E Q :=
  match stage with
  | .slope => computeSlope s
  | .coordinateUpdate => computeCoordinates s
  | .targetWrite => writeTarget s
  | .cleanup => cleanup s

/-- Run the generic ECADD support pipeline. -/
def run {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) : StageState E Q :=
  step .cleanup
    (step .targetWrite
      (step .coordinateUpdate
        (step .slope (initial P targetX targetY))))

/-- Forget internal scratch and recover the endpoint data shape. -/
def toData {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (s : StageState E Q) : Data E Q where
  input := s.input
  targetX := s.targetX
  targetY := s.targetY
  flag := s.flag

@[simp] theorem run_targetX {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (run P targetX targetY).targetX = targetX + genericAddX E P.1 Q :=
  rfl

@[simp] theorem run_targetY {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (run P targetX targetY).targetY = targetY + genericAddY E P.1 Q :=
  rfl

@[simp] theorem run_slopeScratch {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (run P targetX targetY).slopeScratch = 0 :=
  rfl

@[simp] theorem run_resultX {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (run P targetX targetY).resultX = 0 :=
  rfl

@[simp] theorem run_resultY {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (run P targetX targetY).resultY = 0 :=
  rfl

@[simp] theorem run_flag {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (run P targetX targetY).flag = false :=
  rfl

/-- The generic ECADD stage pipeline reaches the public endpoint data shape. -/
theorem run_toData_eq_endpoint {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (run P targetX targetY).toData =
      ({ input := P
         targetX := targetX + genericAddX E P.1 Q
         targetY := targetY + genericAddY E P.1 Q
         flag := false } : Data E Q) :=
  rfl

end StageState

/-- Clean temporary flag convention for generic point addition. -/
def FlagClean {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (x : Data E Q) : Prop :=
  x.flag = false

/-- Add the generic affine sum coordinates into the target coordinate registers. -/
def addIntoTarget {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (x : Data E Q) : Data E Q where
  input := x.input
  targetX := x.targetX + genericAddX E x.input.1 Q
  targetY := x.targetY + genericAddY E x.input.1 Q
  flag := x.flag

/-- The generic ECADD stage pipeline agrees with the endpoint data update. -/
theorem StageState.run_toData_eq_addIntoTarget {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (targetX targetY : ZMod p) :
    (StageState.run P targetX targetY).toData =
      ({ input := P
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget :=
  rfl

/-- Subtract the generic affine sum coordinates from the target registers. -/
def subFromTarget {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (x : Data E Q) : Data E Q where
  input := x.input
  targetX := x.targetX - genericAddX E x.input.1 Q
  targetY := x.targetY - genericAddY E x.input.1 Q
  flag := x.flag

/-- Generic point addition as a reversible coordinate-target map. -/
def addEquiv (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Equiv.Perm (Data E Q) where
  toFun := addIntoTarget
  invFun := subFromTarget
  left_inv := by
    intro x
    cases x
    simp [addIntoTarget, subFromTarget]
  right_inv := by
    intro x
    cases x
    simp [addIntoTarget, subFromTarget]

@[simp] theorem addEquiv_apply {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E} (x : Data E Q) :
    addEquiv E Q x = x.addIntoTarget :=
  rfl

/-- Generic point addition with an external work register. -/
def withWorkEquiv (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    [Fact p.Prime] (Work : Type) : Equiv.Perm (Data E Q × Work) :=
  Equiv.prodCongr (addEquiv E Q) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E} {Work : Type} (x : Data E Q) (w : Work) :
    withWorkEquiv E Q Work (x, w) = (x.addIntoTarget, w) :=
  rfl

/-- The point-addition map leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E} {Work : Type} :
    WorkRegister.Preserves (Data := Data E Q) (Work := Work)
      (withWorkEquiv E Q Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for generic point addition. -/
def withWorkCleanMap (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    [Fact p.Prime] (Work : Type) :
    WorkRegister.CleanReversibleMap (Data E Q) Work where
  perm := withWorkEquiv E Q Work
  preservesWork := withWorkEquiv_preserves_work

end Data

/-- Register whose labels are generic point-addition data states. -/
noncomputable def register (E : PrimeFieldShortWeierstrass p) [NeZero p] (Q : AffinePoint E) :
    Register where
  Index := Data E Q
  fintype := inferInstance
  decEq := inferInstance

/-- The generic point-addition gate for a fixed addend `Q`. -/
noncomputable def addGate (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) : Gate (register E Q) :=
  Gate.ofPerm (Data.addEquiv E Q).symm

/-- Basis action of the generic point-addition gate. -/
theorem addGate_apply_ket (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) (x : Data E Q) :
    (addGate E Q).apply (PureState.ket (R := register E Q) x) =
      PureState.ket (R := register E Q) x.addIntoTarget := by
  rw [addGate, Gate.ofPerm_apply_ket]
  rfl

/-- Resource parameters attached to the generic affine point-addition endpoint. -/
structure ResourceParameters where
  /-- Resource profile for computing the affine slope. -/
  slopeProfile : ModularArithmeticResourceProfile
  /-- Resource profile for deriving output coordinates from the slope. -/
  coordinateProfile : ModularArithmeticResourceProfile
  /-- Resource profile for adding output coordinates into the target registers. -/
  targetUpdateProfile : ModularArithmeticResourceProfile
deriving DecidableEq

namespace ResourceParameters

/-- Compose the point-addition resource profile from slope, coordinate, and
target-update components. -/
def toProfile (params : ResourceParameters) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential params.slopeProfile
    (ModularArithmeticResourceProfile.sequential
      params.coordinateProfile params.targetUpdateProfile)

/-- Concrete component bounds for generic point addition. -/
structure PublicBaselineBounds where
  /-- Public bound for slope computation. -/
  slopeBound : ModularArithmeticResourceProfile
  /-- Public bound for coordinate computation. -/
  coordinateBound : ModularArithmeticResourceProfile
  /-- Public bound for the coordinate target update. -/
  targetUpdateBound : ModularArithmeticResourceProfile
deriving DecidableEq

namespace PublicBaselineBounds

/-- The composed bound profile for generic point addition. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential bounds.slopeBound
    (ModularArithmeticResourceProfile.sequential
      bounds.coordinateBound bounds.targetUpdateBound)

end PublicBaselineBounds

/-- Fieldwise source-bound certificate for generic point addition. -/
structure SourceBoundCertificate
    (params : ResourceParameters) (bounds : PublicBaselineBounds) : Prop where
  slope_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.slopeProfile bounds.slopeBound
  coordinate_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.coordinateProfile bounds.coordinateBound
  targetUpdate_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.targetUpdateProfile bounds.targetUpdateBound

/-- The component certificate implies the composed profile bound. -/
theorem SourceBoundCertificate.supportsUpperBound
    {params : ResourceParameters} {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound params.toProfile bounds.toProfile := by
  simpa [toProfile, PublicBaselineBounds.toProfile] using
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential cert.slope_le
      (ModularArithmeticResourceProfile.SupportsUpperBound.sequential
        cert.coordinate_le cert.targetUpdate_le)

end ResourceParameters

/-- Typed endpoint witness for generic affine point addition, modeled as one
permutation gate with an attached resource profile. -/
noncomputable def addCircuit (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) (params : ResourceParameters) :
    Circuit (register E Q) :=
  Circuit.ofGate "elliptic-curve-generic-addition" (addGate E Q)
    params.toProfile.toResourceProfile params.toProfile.circuitDepth
    params.toProfile.oracleQueries

/-- Clean-basis action for generic affine point addition by a fixed addend. -/
theorem addCircuit_apply_clean_ket (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) (params : ResourceParameters)
    (P : {P : AffinePoint E // P.x ≠ Q.x}) :
    Circuit.apply (addCircuit E Q params)
      (PureState.ket (R := register E Q)
        ({ input := P, targetX := 0, targetY := 0, flag := false } : Data E Q) :
          StateVector (register E Q)) =
      (PureState.ket (R := register E Q)
        ({ input := P
           targetX := genericAddX E P.1 Q
           targetY := genericAddY E P.1 Q
           flag := false } : Data E Q) :
          StateVector (register E Q)) := by
  simpa [addCircuit, Circuit.apply_ofGate, Gate.apply_coe, Data.addIntoTarget] using
    congrArg (fun psi : PureState (register E Q) => (psi : StateVector (register E Q)))
      (addGate_apply_ket E Q
        ({ input := P, targetX := 0, targetY := 0, flag := false } : Data E Q))

/-- The coordinate-target circuit output is the generic affine group-law sum. -/
theorem addCircuit_apply_group_law (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) (params : ResourceParameters)
    (P : {P : AffinePoint E // P.x ≠ Q.x}) :
    P.1.toMathlib + Q.toMathlib =
        WeierstrassCurve.Affine.Point.some
          (genericAddX E P.1 Q) (genericAddY E P.1 Q)
          (genericAdd_nonsingular E P.1 Q P.2) ∧
      Circuit.apply (addCircuit E Q params)
        (PureState.ket (R := register E Q)
          ({ input := P, targetX := 0, targetY := 0, flag := false } : Data E Q) :
            StateVector (register E Q)) =
        (PureState.ket (R := register E Q)
          ({ input := P
             targetX := genericAddX E P.1 Q
             targetY := genericAddY E P.1 Q
             flag := false } : Data E Q) :
            StateVector (register E Q)) := by
  exact ⟨genericAdd_group_law_mathlib E P.1 Q P.2,
    addCircuit_apply_clean_ket E Q params P⟩

/-! #### External work-register clean interface -/

/-- Generic point addition as an external-work clean reversible circuit. -/
noncomputable def addWithWorkCircuit (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data E Q) Work) :=
  (Data.withWorkCleanMap E Q Work).circuit params.toProfile

@[simp] theorem addWithWorkCircuit_resources (E : PrimeFieldShortWeierstrass p)
    [NeZero p] [Fact p.Prime] (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (addWithWorkCircuit E Q Work params).resources =
      params.toProfile.toResourceProfile :=
  rfl

@[simp] theorem addWithWorkCircuit_depth (E : PrimeFieldShortWeierstrass p)
    [NeZero p] [Fact p.Prime] (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (addWithWorkCircuit E Q Work params).depth = params.toProfile.circuitDepth :=
  rfl

@[simp] theorem addWithWorkCircuit_queryDepth (E : PrimeFieldShortWeierstrass p)
    [NeZero p] [Fact p.Prime] (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    (addWithWorkCircuit E Q Work params).queryDepth = params.toProfile.oracleQueries :=
  rfl

/-- Basis-state correctness for generic point addition with an external work register. -/
theorem addWithWorkCircuit_apply_ket (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (x : Data E Q) (w : Work) :
    Circuit.apply (addWithWorkCircuit E Q Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work) (x, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work)
          (x.addIntoTarget, w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)) := by
  simpa [addWithWorkCircuit, Data.withWorkCleanMap, Data.withWorkEquiv] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := Data.withWorkCleanMap E Q Work)
      (profile := params.toProfile) (x := (x, w))

/-- Clean public-form basis action with an external work register. -/
theorem addWithWorkCircuit_apply_clean_ket (E : PrimeFieldShortWeierstrass p)
    [NeZero p] [Fact p.Prime] (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) (P : {P : AffinePoint E // P.x ≠ Q.x}) (w : Work) :
    Circuit.apply (addWithWorkCircuit E Q Work params)
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work)
          (({ input := P, targetX := 0, targetY := 0, flag := false } : Data E Q), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work)
          (({ input := P
              targetX := genericAddX E P.1 Q
              targetY := genericAddY E P.1 Q
              flag := false } : Data E Q), w) :
          StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)) := by
  simpa [Data.addIntoTarget] using
    addWithWorkCircuit_apply_ket E Q Work params
      ({ input := P, targetX := 0, targetY := 0, flag := false } : Data E Q) w

/-- Generic ECADD clean-basis action with encoded finite-input evidence and
external work preservation [RNSL17, ECDLP.tex:488-580,650-696]. -/
theorem encodedWithWorkCircuit_apply_clean_ket
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    {n : ℕ} (encoding : PointEncoding E n)
    (params : ResourceParameters) (P : Input E Q) (w : Work) :
    EncodedEndpointEvidence E Q encoding P ∧
      Circuit.apply (addWithWorkCircuit E Q Work params)
        (PureState.ket
          (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work)
            (({ input := P
                targetX := 0
                targetY := 0
                flag := false } : Data E Q), w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)) =
        (PureState.ket
          (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work)
            (({ input := P
                targetX := genericAddX E P.1 Q
                targetY := genericAddY E P.1 Q
                flag := false } : Data E Q), w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)) := by
  constructor
  · exact encodedEndpointEvidence E Q encoding P
  · exact addWithWorkCircuit_apply_clean_ket E Q Work params P w

/-- Resource-correct witness for the external-work generic point-addition circuit. -/
noncomputable def addWithWorkCircuitResourceCorrectWitness
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (Q : AffinePoint E)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work)
      (∀ x : Data E Q, ∀ w : Work,
        Circuit.apply (addWithWorkCircuit E Q Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work) (x, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register (Data E Q) Work)
              (x.addIntoTarget, w) :
            StateVector (WorkRegister.CleanReversibleMap.register (Data E Q) Work)))
      ((addWithWorkCircuit E Q Work params).resources =
          params.toProfile.toResourceProfile ∧
        (addWithWorkCircuit E Q Work params).depth =
          params.toProfile.circuitDepth ∧
        (addWithWorkCircuit E Q Work params).queryDepth =
          params.toProfile.oracleQueries) := by
  exact
    { circuit := addWithWorkCircuit E Q Work params
      correctness := fun x w => addWithWorkCircuit_apply_ket E Q Work params x w
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Public-bounds endpoint for generic point addition. -/
theorem main_with_public_bounds (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds : ResourceParameters.SourceBoundCertificate params bounds) :
    (∀ P : {P : AffinePoint E // P.x ≠ Q.x},
      Circuit.apply (addCircuit E Q params)
        (PureState.ket (R := register E Q)
          ({ input := P, targetX := 0, targetY := 0, flag := false } : Data E Q) :
            StateVector (register E Q)) =
        (PureState.ket (R := register E Q)
          ({ input := P
             targetX := genericAddX E P.1 Q
             targetY := genericAddY E P.1 Q
             flag := false } : Data E Q) :
            StateVector (register E Q))) ∧
      ModularArithmeticResourceProfile.SupportsUpperBound
        params.toProfile bounds.toProfile ∧
      (addCircuit E Q params).resources = params.toProfile.toResourceProfile ∧
      (addCircuit E Q params).depth = params.toProfile.circuitDepth ∧
      (addCircuit E Q params).queryDepth = params.toProfile.oracleQueries := by
  constructor
  · intro P
    exact addCircuit_apply_clean_ket E Q params P
  constructor
  · exact componentBounds.supportsUpperBound
  · exact ⟨rfl, rfl, rfl⟩

end GenericPointAddition

end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg
