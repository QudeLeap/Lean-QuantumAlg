/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Generic.DirectSchedule.Semantics

/-!
# Clean direct-workspace generic point-addition pipeline

This module places the direct affine schedule behind the public point frame.
One physical arithmetic carrier is computed, copied to the public output, and
uncomputed.  No logical arithmetic bank or temporal workspace address is used.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace Pipeline

open Nat.FixedWidth

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

local instance modulusNeZero : NeZero params.modulus.val :=
  ⟨Nat.ne_of_gt params.modulusPos⟩

/-- The sole direct arithmetic workspace behind the public point frame. -/
abbrev AuxRegisters := ParameterizedPointAddition.RawRegisters

/-- Public point words, direct arithmetic workspace, and two framing bits. -/
abbrev RawRegisters :=
  PointAddition.PortFrame.RawRegisters AuxRegisters params.width

/-- Binary encoding of the direct arithmetic workspace. -/
abbrev auxEncoding : BinaryLabelEncoding AuxRegisters :=
  DirectSchedule.auxEncoding

/-- Binary encoding of the complete public frame and direct workspace. -/
abbrev rawEncoding : BinaryLabelEncoding RawRegisters :=
  DirectSchedule.rawEncoding

/-- Leading public control of the framed translation carrier. -/
def controlBit : EncodedBit rawEncoding :=
  PointAddition.PortFrame.controlBit auxEncoding params.width

/-- Clean work bit used to decompose one further control into native gates. -/
def controlWorkBit : EncodedBit rawEncoding :=
  PointAddition.PortFrame.controlWorkBit auxEncoding params.width

lemma controlBit_wire_ne_controlWorkBit :
    controlBit.wire ≠ controlWorkBit.wire := by
  exact PointAddition.PortFrame.controlBit_wire_ne_controlWorkBit
    auxEncoding params.width

/-- Exact width of the retained three-point frame and direct arithmetic
workspace. -/
lemma rawEncoding_width_exact :
    rawEncoding.width =
      Arithmetic.ModularInversion.physicalWidthFor params.width +
        19 * params.width + 9 := by
  change (PointAddition.PortFrame.rawEncoding
    ParameterizedPointAddition.rawEncoding params.width).width = _
  rw [PointAddition.PortFrame.rawEncoding_width,
    ParameterizedPointAddition.rawEncoding_width_exact]
  omega

variable {E : PrimeFieldShortWeierstrass params.modulus.val}
  [Fact params.modulus.val.Prime]
  {Q : AffinePoint E}

/-- Canonical public word pair for one affine point. -/
def pointWords (P : AffinePoint E) :
    PointAddition.PortFrame.PointWords params.width :=
  (ParameterizedPointAddition.residueWord P.x,
    ParameterizedPointAddition.residueWord P.y)

/-- Clean direct carrier under a caller-selected public output value. -/
def preloadInputRegistersAt
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) : RawRegisters :=
  DirectSchedule.initialRegistersAt output control P

/-- The generic affine result packaged as a finite point. -/
def resultPoint (P : GenericPointAddition.Input E Q) : AffinePoint E :=
  genericAddPoint E P.1 Q P.2

/-- The public point materialized by the pipeline is the generic group-law sum. -/
lemma resultPoint_group_law_mathlib
    (P : GenericPointAddition.Input E Q) :
    P.1.toMathlib + Q.toMathlib = (resultPoint P).toMathlib := by
  simpa [resultPoint, AffinePoint.toMathlib] using
    genericAdd_group_law_mathlib E P.1 Q P.2

/-- A valid generic subtraction by the fixed point recovers the input point. -/
lemma reverseResultPoint_eq
    (P : GenericPointAddition.Input E Q)
    (hreverse : GenericAddDomain (resultPoint P) (AffinePoint.negate Q)) :
    resultPoint (Q := AffinePoint.negate Q)
        (⟨resultPoint P, hreverse⟩ :
          GenericPointAddition.Input E (AffinePoint.negate Q)) =
      P.1 := by
  let reverseInput : GenericPointAddition.Input E (AffinePoint.negate Q) :=
    ⟨resultPoint P, hreverse⟩
  have hforward := resultPoint_group_law_mathlib P
  have hbackward :=
    resultPoint_group_law_mathlib (Q := AffinePoint.negate Q) reverseInput
  have hmathlib : (resultPoint reverseInput).toMathlib = P.1.toMathlib := by
    rw [← hbackward, AffinePoint.negate_toMathlib, ← hforward]
    simp [add_assoc]
  have hcoordinates := WeierstrassCurve.Affine.Point.some.inj hmathlib
  exact AffinePoint.ext_coordinates _ _ hcoordinates.1 hcoordinates.2

/-- Public words of the generic affine result. -/
def resultWords (P : GenericPointAddition.Input E Q) :
    PointAddition.PortFrame.PointWords params.width :=
  pointWords (resultPoint P)

/-- Intermediate public output after copying only the x coordinate. -/
private def copiedXWords (P : GenericPointAddition.Input E Q) :
    PointAddition.PortFrame.PointWords params.width :=
  (Arithmetic.ModularDivision.residueWord
      (ParameterizedPointAddition.xScratch P), 0)

/-- The two direct scratch coordinates viewed as public words. -/
private def scratchWords (P : GenericPointAddition.Input E Q) :
    PointAddition.PortFrame.PointWords params.width :=
  (Arithmetic.ModularDivision.residueWord
      (ParameterizedPointAddition.xScratch P),
    Arithmetic.ModularDivision.residueWord
      (ParameterizedPointAddition.yScratch P))

private lemma scratchWords_eq_resultWords
    (P : GenericPointAddition.Input E Q) :
    scratchWords P = resultWords P := by
  simp only [scratchWords, resultWords, resultPoint, pointWords,
    genericAddPoint_x, genericAddPoint_y,
    ParameterizedPointAddition.xScratch_eq_genericAddX,
    ParameterizedPointAddition.yScratch_eq_genericAddY]

/-- Literal CNOT copy from one auxiliary word to one public word. -/
private def auxToPublicGates
    (source : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (target : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  Arithmetic.BlockBank.WordPort.directCopyGates
    (DirectSchedule.liftAuxPort source)
    (PointAddition.PortFrame.liftPublicPort auxEncoding params.width target)
    (fun bit =>
      (DirectSchedule.public_aux_cross_ne target source bit bit).symm)

/-- Folded action of an auxiliary-to-public CNOT copy. -/
private def auxToPublicStep
    (source : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (target : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    RawRegisters → RawRegisters :=
  Arithmetic.BlockBank.WordPort.directCopyStep
    (DirectSchedule.liftAuxPort source)
    (PointAddition.PortFrame.liftPublicPort auxEncoding params.width target)
    (fun bit =>
      (DirectSchedule.public_aux_cross_ne target source bit bit).symm)

omit [Fact params.modulus.val.Prime] in
private lemma auxToPublicGates_stepList
    (source : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (target : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (auxToPublicGates source target) state =
      auxToPublicStep source target state :=
  rfl

omit [Fact params.modulus.val.Prime] in
private lemma auxToPublicStep_eq_set_of_clean
    (source : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (target : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width)
    (state : RawRegisters) (value : Word params.width)
    (hsource : (DirectSchedule.liftAuxPort source).read state = value)
    (htarget :
      (PointAddition.PortFrame.liftPublicPort auxEncoding params.width target).read
        state = 0) :
    auxToPublicStep source target state =
      (PointAddition.PortFrame.liftPublicPort auxEncoding params.width target).set
        state value := by
  exact Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_of_clean _ _ _
    (fun sourceBit targetBit =>
      DirectSchedule.public_aux_cross_ne target source targetBit sourceBit)
    state value hsource htarget

/-- Copy the two saved direct-workspace coordinates to the public output. -/
private def outputCopyGates : List (EncodedBit.GateSpec rawEncoding) :=
  auxToPublicGates ParameterizedPointAddition.Workspace.xPort
      (PointAddition.PortFrame.outputXPublicPort params.width) ++
    auxToPublicGates ParameterizedPointAddition.Workspace.yPort
      (PointAddition.PortFrame.outputYPublicPort params.width)

private def outputCopyStep : RawRegisters → RawRegisters := fun state =>
  auxToPublicStep ParameterizedPointAddition.Workspace.yPort
      (PointAddition.PortFrame.outputYPublicPort params.width)
    (auxToPublicStep ParameterizedPointAddition.Workspace.xPort
      (PointAddition.PortFrame.outputXPublicPort params.width) state)

omit [Fact params.modulus.val.Prime] in
@[simp] private lemma outputCopyGates_length :
    outputCopyGates.length = 2 * params.width := by
  simp [outputCopyGates, auxToPublicGates]
  omega

omit [Fact params.modulus.val.Prime] in
private lemma outputCopyGates_cnotMultiplicity_sum :
    (outputCopyGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * params.width := by
  simp only [outputCopyGates, List.map_append, List.sum_append,
    auxToPublicGates,
    Arithmetic.BlockBank.WordPort.directCopyGates_cnotMultiplicity_sum]
  omega

omit [Fact params.modulus.val.Prime] in
private lemma outputCopyGates_toffoliMultiplicity_sum :
    (outputCopyGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp only [outputCopyGates, List.map_append, List.sum_append,
    auxToPublicGates,
    Arithmetic.BlockBank.WordPort.directCopyGates_toffoliMultiplicity_sum,
    Nat.zero_add]

omit [Fact params.modulus.val.Prime] in
private lemma outputCopyGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList outputCopyGates state = outputCopyStep state := by
  rw [outputCopyGates, EncodedBit.GateSpec.stepList_append,
    auxToPublicGates_stepList, auxToPublicGates_stepList]
  rfl

private lemma xPort_read_computed
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    (DirectSchedule.liftAuxPort
      ParameterizedPointAddition.Workspace.xPort).read
        (DirectSchedule.computedRegistersAt output control P) =
      Arithmetic.ModularDivision.residueWord
        (ParameterizedPointAddition.xScratch P) := by
  rw [show ParameterizedPointAddition.Workspace.xPort =
      ParameterizedPointAddition.Workspace.thinPort
        ParameterizedPointAddition.Workspace.xThinPort from rfl]
  unfold DirectSchedule.computedRegistersAt
  rw [DirectSchedule.liftThinPort_read_framedProductRegisters]
  simp only [DirectSchedule.ySavedTail, DirectSchedule.xSavedTail,
    DirectSchedule.xCoordinateData_accumulator]
  rfl

private lemma yPort_read_computed
    (output : PointAddition.PortFrame.PointWords params.width)
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    (DirectSchedule.liftAuxPort
      ParameterizedPointAddition.Workspace.yPort).read
        (DirectSchedule.computedRegistersAt output control P) =
      Arithmetic.ModularDivision.residueWord
        (ParameterizedPointAddition.yScratch P) := by
  rw [show ParameterizedPointAddition.Workspace.yPort =
      ParameterizedPointAddition.Workspace.thinPort
        ParameterizedPointAddition.Workspace.yThinPort from rfl]
  unfold DirectSchedule.computedRegistersAt
  rw [DirectSchedule.liftThinPort_read_framedProductRegisters]
  simp only [DirectSchedule.ySavedTail,
    DirectSchedule.yCoordinateData_accumulator]
  exact ParameterizedPointAddition.Workspace.yThinPort.read_set _ _

private lemma outputCopyTransitionX (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    auxToPublicStep ParameterizedPointAddition.Workspace.xPort
        (PointAddition.PortFrame.outputXPublicPort params.width)
        (DirectSchedule.computedRegistersAt
          (PointAddition.PortFrame.zeroPoint params.width) control P) =
      DirectSchedule.computedRegistersAt (copiedXWords P) control P := by
  rw [auxToPublicStep_eq_set_of_clean _ _ _
    (Arithmetic.ModularDivision.residueWord
      (ParameterizedPointAddition.xScratch P))]
  · rfl
  · exact xPort_read_computed _ control P
  · rfl

private lemma outputCopyTransitionY (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    auxToPublicStep ParameterizedPointAddition.Workspace.yPort
        (PointAddition.PortFrame.outputYPublicPort params.width)
        (DirectSchedule.computedRegistersAt (copiedXWords P) control P) =
      DirectSchedule.computedRegistersAt (scratchWords P) control P := by
  rw [auxToPublicStep_eq_set_of_clean _ _ _
    (Arithmetic.ModularDivision.residueWord
      (ParameterizedPointAddition.yScratch P))]
  · rfl
  · exact yPort_read_computed _ control P
  · rfl

private lemma outputCopyStep_computed (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    outputCopyStep
        (DirectSchedule.computedRegistersAt
          (PointAddition.PortFrame.zeroPoint params.width) control P) =
      DirectSchedule.computedRegistersAt (resultWords P) control P := by
  change auxToPublicStep ParameterizedPointAddition.Workspace.yPort
      (PointAddition.PortFrame.outputYPublicPort params.width)
      (auxToPublicStep ParameterizedPointAddition.Workspace.xPort
        (PointAddition.PortFrame.outputXPublicPort params.width)
        (DirectSchedule.computedRegistersAt
          (PointAddition.PortFrame.zeroPoint params.width) control P)) = _
  rw [outputCopyTransitionX control P, outputCopyTransitionY control P,
    scratchWords_eq_resultWords P]

/-- One forward direct computation, public output copy, and exact uncompute. -/
def additionGates : List (EncodedBit.GateSpec rawEncoding) :=
  DirectSchedule.computeGates ++ outputCopyGates ++
    DirectSchedule.computeGates.reverse

omit [Fact params.modulus.val.Prime] in
/-- Exact primitive-leaf count of the clean direct addition schedule. -/
lemma additionGates_length :
    additionGates.length =
      76 * params.width + 20 +
        10 * (ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).length +
        6 * ParameterizedPointAddition.Workspace.multiplicationGates.length +
        2 * ParameterizedPointAddition.Workspace.divisionGates.length := by
  simp only [additionGates, List.length_append, List.length_reverse,
    DirectSchedule.computeGates_length, outputCopyGates_length]
  omega

/-- Closed field-width-only primitive-leaf bound for direct generic addition. -/
def additionGateLengthBoundFor (fieldWidth : Nat) : Nat :=
  76 * fieldWidth + 20 + 10 * (116 * fieldWidth + 15) +
    6 * Arithmetic.VariableModularMulSchedule.eventCountBoundFor fieldWidth +
    2 * (2 * Arithmetic.ModularInversion.gateLengthBoundFor fieldWidth +
      2 * fieldWidth +
      Arithmetic.VariableModularMulSchedule.eventCountBoundFor fieldWidth)

def additionGateLengthBound : Nat :=
  additionGateLengthBoundFor params.width

omit [Fact params.modulus.val.Prime] in
lemma additionGates_length_le :
    additionGates.length ≤ additionGateLengthBound := by
  have hselected :=
    ParameterizedPointAddition.Workspace.selectedAdditionGates_length_le
      ParameterizedPointAddition.Workspace.selectedAdditionBit
  have hmultiplication :
      ParameterizedPointAddition.Workspace.multiplicationGates.length ≤
        Arithmetic.VariableModularMulSchedule.eventCountBoundFor
          params.width := by
    simpa only [ParameterizedPointAddition.Workspace.multiplicationGateLengthBound]
      using ParameterizedPointAddition.Workspace.multiplicationGates_length_le
  have hdivision :
      ParameterizedPointAddition.Workspace.divisionGates.length ≤
        2 * Arithmetic.ModularInversion.gateLengthBoundFor params.width +
          2 * params.width +
          Arithmetic.VariableModularMulSchedule.eventCountBoundFor
            params.width := by
    simpa only [ParameterizedPointAddition.Workspace.divisionGateLengthBound,
      ParameterizedPointAddition.Workspace.multiplicationGateLengthBound,
      Arithmetic.ModularInversion.gateLengthBound] using
      ParameterizedPointAddition.Workspace.divisionGates_length_le
  rw [additionGates_length]
  unfold additionGateLengthBound additionGateLengthBoundFor
  omega

omit [Fact params.modulus.val.Prime] in
/-- Exact CNOT coordinate of the clean direct addition schedule. -/
lemma additionGates_cnotMultiplicity_sum :
    (additionGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      76 * params.width +
        10 * ((ParameterizedPointAddition.Workspace.selectedAdditionGates
          ParameterizedPointAddition.Workspace.selectedAdditionBit).map
            EncodedBit.GateSpec.cnotMultiplicity).sum +
        6 * (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum +
        2 * (ParameterizedPointAddition.Workspace.divisionGates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  simp only [additionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse,
    DirectSchedule.computeGates_cnotMultiplicity_sum,
    outputCopyGates_cnotMultiplicity_sum]
  omega

omit [Fact params.modulus.val.Prime] in
/-- Exact Toffoli coordinate of the clean direct addition schedule. -/
lemma additionGates_toffoliMultiplicity_sum :
    (additionGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      10 * ((ParameterizedPointAddition.Workspace.selectedAdditionGates
        ParameterizedPointAddition.Workspace.selectedAdditionBit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum +
        6 * (ParameterizedPointAddition.Workspace.multiplicationGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum +
        2 * (ParameterizedPointAddition.Workspace.divisionGates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  simp only [additionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse,
    DirectSchedule.computeGates_toffoliMultiplicity_sum,
    outputCopyGates_toffoliMultiplicity_sum]
  omega

/-- Closed CNOT-coordinate bound for direct generic addition. -/
def additionCnotBoundFor (fieldWidth : Nat) : Nat :=
  76 * fieldWidth + 10 * (8 * fieldWidth + 1) +
    6 * Arithmetic.VariableModularMulSchedule.cnotBoundFor fieldWidth +
    2 * (2 * Arithmetic.ModularInversion.cnotBoundFor fieldWidth +
      2 * fieldWidth +
      Arithmetic.VariableModularMulSchedule.cnotBoundFor fieldWidth)

def additionCnotBound : Nat :=
  additionCnotBoundFor params.width

/-- Closed Toffoli-coordinate bound for direct generic addition. -/
def additionToffoliBoundFor (fieldWidth : Nat) : Nat :=
  10 * (108 * fieldWidth + 14) +
    6 * Arithmetic.VariableModularMulSchedule.toffoliBoundFor fieldWidth +
    2 * (2 * Arithmetic.ModularInversion.toffoliBoundFor fieldWidth +
      Arithmetic.VariableModularMulSchedule.toffoliBoundFor fieldWidth)

def additionToffoliBound : Nat :=
  additionToffoliBoundFor params.width

omit [Fact params.modulus.val.Prime] in
lemma additionGates_cnotMultiplicity_sum_le :
    (additionGates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      additionCnotBound := by
  have hselected :=
    ParameterizedPointAddition.Workspace.selectedAdditionGates_cnotMultiplicity_sum
      ParameterizedPointAddition.Workspace.selectedAdditionBit
  have hmultiplication :
      (ParameterizedPointAddition.Workspace.multiplicationGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
        Arithmetic.VariableModularMulSchedule.cnotBoundFor params.width := by
    simpa only [ParameterizedPointAddition.Workspace.multiplicationCnotBound]
      using
        ParameterizedPointAddition.Workspace.multiplicationGates_cnotMultiplicity_sum_le
  have hdivision :
      (ParameterizedPointAddition.Workspace.divisionGates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
        2 * Arithmetic.ModularInversion.cnotBoundFor params.width +
          2 * params.width +
          Arithmetic.VariableModularMulSchedule.cnotBoundFor params.width := by
    simpa only [ParameterizedPointAddition.Workspace.divisionCnotBound,
      ParameterizedPointAddition.Workspace.multiplicationCnotBound,
      Arithmetic.ModularInversion.cnotBound] using
      ParameterizedPointAddition.Workspace.divisionGates_cnotMultiplicity_sum_le
  rw [additionGates_cnotMultiplicity_sum]
  unfold additionCnotBound additionCnotBoundFor
  omega

omit [Fact params.modulus.val.Prime] in
lemma additionGates_toffoliMultiplicity_sum_le :
    (additionGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      additionToffoliBound := by
  have hselected :=
    ParameterizedPointAddition.Workspace.selectedAdditionGates_toffoliMultiplicity_sum_le
      ParameterizedPointAddition.Workspace.selectedAdditionBit
  have hmultiplication :
      (ParameterizedPointAddition.Workspace.multiplicationGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
        Arithmetic.VariableModularMulSchedule.toffoliBoundFor params.width := by
    simpa only [ParameterizedPointAddition.Workspace.multiplicationToffoliBound]
      using
        ParameterizedPointAddition.Workspace.multiplicationGates_toffoliMultiplicity_sum_le
  have hdivision :
      (ParameterizedPointAddition.Workspace.divisionGates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
        2 * Arithmetic.ModularInversion.toffoliBoundFor params.width +
          Arithmetic.VariableModularMulSchedule.toffoliBoundFor params.width := by
    simpa only [ParameterizedPointAddition.Workspace.divisionToffoliBound,
      ParameterizedPointAddition.Workspace.multiplicationToffoliBound,
      Arithmetic.ModularInversion.toffoliBound] using
      ParameterizedPointAddition.Workspace.divisionGates_toffoliMultiplicity_sum_le
  rw [additionGates_toffoliMultiplicity_sum]
  unfold additionToffoliBound additionToffoliBoundFor
  omega

private def AllBitDisjoint (observed : EncodedBit rawEncoding)
    (gates : List (EncodedBit.GateSpec rawEncoding)) : Prop :=
  ∀ gate, gate ∈ gates → EncodedBit.GateSpec.bitDisjoint observed gate

omit [Fact params.modulus.val.Prime] in
private lemma AllBitDisjoint.append
    {observed : EncodedBit rawEncoding}
    {left right : List (EncodedBit.GateSpec rawEncoding)}
    (hleft : AllBitDisjoint observed left)
    (hright : AllBitDisjoint observed right) :
    AllBitDisjoint observed (left ++ right) := by
  intro gate hgate
  exact (List.mem_append.mp hgate).elim (hleft gate) (hright gate)

omit [Fact params.modulus.val.Prime] in
private lemma AllBitDisjoint.reverse
    {observed : EncodedBit rawEncoding}
    {gates : List (EncodedBit.GateSpec rawEncoding)}
    (hgates : AllBitDisjoint observed gates) :
    AllBitDisjoint observed gates.reverse := by
  intro gate hgate
  exact hgates gate (List.mem_reverse.mp hgate)

omit [Fact params.modulus.val.Prime] in
private lemma xorIntoGates_bitDisjoint {width : Nat}
    (observed : EncodedBit rawEncoding)
    (source target : EncodedBit.Word rawEncoding width)
    (hcross : ∀ bit, (source.bit bit).wire ≠ (target.bit bit).wire)
    (hsource : ∀ bit, (source.bit bit).wire ≠ observed.wire)
    (htarget : ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (gate : EncodedBit.GateSpec rawEncoding)
    (hgate : gate ∈ EncodedBit.Word.xorIntoGates source target hcross) :
    EncodedBit.GateSpec.bitDisjoint observed gate := by
  rw [EncodedBit.Word.xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  exact ⟨hsource bit, htarget bit⟩

omit [Fact params.modulus.val.Prime] in
private lemma auxToPublicGates_bitDisjoint_controlBit
    (source : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (target : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    AllBitDisjoint controlBit (auxToPublicGates source target) := by
  intro gate hgate
  unfold auxToPublicGates Arithmetic.BlockBank.WordPort.directCopyGates at hgate
  exact xorIntoGates_bitDisjoint _ _ _ _
    (fun bit => PointAddition.PortFrame.liftAuxBit_wire_ne_controlBit
      auxEncoding params.width (source.word.bit bit))
    (fun bit => PointAddition.PortFrame.liftPublicBit_wire_ne_controlBit
      auxEncoding params.width (target.word.bit bit)) gate hgate

omit [Fact params.modulus.val.Prime] in
private lemma auxToPublicGates_bitDisjoint_controlWorkBit
    (source : Arithmetic.BlockBank.WordPort auxEncoding params.width)
    (target : Arithmetic.BlockBank.WordPort
      (PointAddition.PortFrame.publicEncoding params.width) params.width) :
    AllBitDisjoint controlWorkBit (auxToPublicGates source target) := by
  intro gate hgate
  unfold auxToPublicGates Arithmetic.BlockBank.WordPort.directCopyGates at hgate
  exact xorIntoGates_bitDisjoint _ _ _ _
    (fun bit => PointAddition.PortFrame.liftAuxBit_wire_ne_controlWorkBit
      auxEncoding params.width (source.word.bit bit))
    (fun bit => PointAddition.PortFrame.liftPublicBit_wire_ne_controlWorkBit
      auxEncoding params.width (target.word.bit bit)) gate hgate

omit [Fact params.modulus.val.Prime] in
private lemma outputCopyGates_bitDisjoint_controlBit :
    AllBitDisjoint controlBit outputCopyGates := by
  unfold outputCopyGates
  exact AllBitDisjoint.append
    (auxToPublicGates_bitDisjoint_controlBit _ _)
    (auxToPublicGates_bitDisjoint_controlBit _ _)

omit [Fact params.modulus.val.Prime] in
private lemma outputCopyGates_bitDisjoint_controlWorkBit :
    AllBitDisjoint controlWorkBit outputCopyGates := by
  unfold outputCopyGates
  exact AllBitDisjoint.append
    (auxToPublicGates_bitDisjoint_controlWorkBit _ _)
    (auxToPublicGates_bitDisjoint_controlWorkBit _ _)

omit [Fact params.modulus.val.Prime] in
/-- The leading public control is disjoint from every direct addition gate. -/
lemma additionGates_bitDisjoint_controlBit :
    ∀ gate, gate ∈ additionGates →
      EncodedBit.GateSpec.bitDisjoint controlBit gate := by
  change AllBitDisjoint controlBit additionGates
  unfold additionGates
  have hcompute : AllBitDisjoint controlBit DirectSchedule.computeGates := by
    intro gate hgate
    exact DirectSchedule.computeGates_bitDisjoint_controlBit gate hgate
  exact AllBitDisjoint.append
    (AllBitDisjoint.append hcompute outputCopyGates_bitDisjoint_controlBit)
    (AllBitDisjoint.reverse hcompute)

omit [Fact params.modulus.val.Prime] in
/-- The clean control-work bit is disjoint from every direct addition gate. -/
lemma additionGates_bitDisjoint_controlWorkBit :
    ∀ gate, gate ∈ additionGates →
      EncodedBit.GateSpec.bitDisjoint controlWorkBit gate := by
  change AllBitDisjoint controlWorkBit additionGates
  unfold additionGates
  have hcompute : AllBitDisjoint controlWorkBit DirectSchedule.computeGates := by
    intro gate hgate
    exact DirectSchedule.computeGates_bitDisjoint_controlWorkBit gate hgate
  exact AllBitDisjoint.append
    (AllBitDisjoint.append hcompute outputCopyGates_bitDisjoint_controlWorkBit)
    (AllBitDisjoint.reverse hcompute)

/-- The direct schedule writes the affine result and restores its sole
arithmetic workspace to the input-independent blank state. -/
lemma additionGates_clean (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList additionGates
        (preloadInputRegistersAt
          (PointAddition.PortFrame.zeroPoint params.width) control P) =
      preloadInputRegistersAt (resultWords P) control P := by
  have hcompute := DirectSchedule.computeGates_initial
    (PointAddition.PortFrame.zeroPoint params.width) control P
  have hcopy :
      EncodedBit.GateSpec.stepList outputCopyGates
          (DirectSchedule.computedRegistersAt
            (PointAddition.PortFrame.zeroPoint params.width) control P) =
        DirectSchedule.computedRegistersAt (resultWords P) control P := by
    rw [outputCopyGates_stepList, outputCopyStep_computed]
  have huncompute :
      EncodedBit.GateSpec.stepList DirectSchedule.computeGates.reverse
          (DirectSchedule.computedRegistersAt (resultWords P) control P) =
        DirectSchedule.initialRegistersAt (resultWords P) control P := by
    rw [← DirectSchedule.computeGates_initial (resultWords P) control P]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      DirectSchedule.computeGates _
  simp only [additionGates, EncodedBit.GateSpec.stepList_append]
  rw [show preloadInputRegistersAt
      (PointAddition.PortFrame.zeroPoint params.width) control P =
      DirectSchedule.initialRegistersAt
        (PointAddition.PortFrame.zeroPoint params.width) control P from rfl,
    hcompute, hcopy, huncompute]
  rfl

/-- Reversing the clean schedule clears its result and restores the input. -/
lemma additionGates_reverse_clean (control : Bool)
    (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList additionGates.reverse
        (preloadInputRegistersAt (resultWords P) control P) =
      preloadInputRegistersAt
        (PointAddition.PortFrame.zeroPoint params.width) control P := by
  rw [← additionGates_clean control P]
  exact EncodedBit.GateSpec.stepList_reverse_stepList additionGates _

/-! ## Clean in-place translation prefix -/

/-- Input-independent boundary for the outer exceptional-case dispatcher. -/
def translationBoundaryRegisters
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width) : RawRegisters :=
  (control, (((mutable, (constant, output)),
    ParameterizedPointAddition.blankRegisters), false))

omit [Fact params.modulus.val.Prime] in
/-- Load the fixed point, add it, swap the result into the mutable point, and
replace the fixed point by its inverse. -/
def translationPrefixGates
    (positive inverse : PointAddition.PortFrame.PointWords params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  let loadGates : List (EncodedBit.GateSpec rawEncoding) :=
    PointAddition.PortFrame.loadConstantGates auxEncoding params.width positive
  let swapGates : List (EncodedBit.GateSpec rawEncoding) :=
    PointAddition.PortFrame.swapMutableOutputGates auxEncoding params.width
  let replaceGates : List (EncodedBit.GateSpec rawEncoding) :=
    PointAddition.PortFrame.replaceConstantGates auxEncoding params.width
      positive inverse
  loadGates ++ additionGates ++ swapGates ++ replaceGates

/-- The common prefix materializes `P+Q`, keeps `P` in the output port, loads
`-Q`, and leaves the direct workspace clean. -/
lemma translationPrefixGates_clean
    (control : Bool) (P : GenericPointAddition.Input E Q) :
    EncodedBit.GateSpec.stepList
        (translationPrefixGates (pointWords Q)
          (pointWords (AffinePoint.negate Q)))
        (translationBoundaryRegisters control (pointWords P.1)
          (PointAddition.PortFrame.zeroPoint params.width)
          (PointAddition.PortFrame.zeroPoint params.width)) =
      translationBoundaryRegisters control (resultWords P)
        (pointWords (AffinePoint.negate Q)) (pointWords P.1) := by
  let positive := pointWords Q
  let inverse := pointWords (AffinePoint.negate Q)
  let zero := PointAddition.PortFrame.zeroPoint params.width
  let blank := ParameterizedPointAddition.blankRegisters
  let loadGates : List (EncodedBit.GateSpec rawEncoding) :=
    PointAddition.PortFrame.loadConstantGates auxEncoding params.width positive
  let swapGates : List (EncodedBit.GateSpec rawEncoding) :=
    PointAddition.PortFrame.swapMutableOutputGates auxEncoding params.width
  let replaceGates : List (EncodedBit.GateSpec rawEncoding) :=
    PointAddition.PortFrame.replaceConstantGates auxEncoding params.width
      positive inverse
  have hload :
      EncodedBit.GateSpec.stepList loadGates
          (translationBoundaryRegisters control (pointWords P.1) zero zero) =
        preloadInputRegistersAt zero control P := by
    change PointAddition.PortFrame.loadConstantStep auxEncoding params.width
        positive
        (control, (((pointWords P.1, (zero, zero)), blank), false)) =
      DirectSchedule.initialRegistersAt zero control P
    exact PointAddition.PortFrame.loadConstantStep_at
      auxEncoding params.width positive control (pointWords P.1) zero blank false
  have hswap :
      EncodedBit.GateSpec.stepList swapGates
          (preloadInputRegistersAt (resultWords P) control P) =
        translationBoundaryRegisters control (resultWords P) positive
          (pointWords P.1) := by
    change PointAddition.PortFrame.swapMutableOutputStep auxEncoding params.width
        (control,
          (((pointWords P.1, (positive, resultWords P)), blank), false)) =
      (control,
        (((resultWords P, (positive, pointWords P.1)), blank), false))
    exact PointAddition.PortFrame.swapMutableOutputStep_at
      auxEncoding params.width control (pointWords P.1) positive (resultWords P)
      blank false
  have hreplace :
      EncodedBit.GateSpec.stepList replaceGates
          (translationBoundaryRegisters control (resultWords P) positive
            (pointWords P.1)) =
        translationBoundaryRegisters control (resultWords P) inverse
          (pointWords P.1) := by
    change PointAddition.PortFrame.replaceConstantStep auxEncoding params.width
        positive inverse
        (control,
          (((resultWords P, (positive, pointWords P.1)), blank), false)) =
      (control,
        (((resultWords P, (inverse, pointWords P.1)), blank), false))
    exact PointAddition.PortFrame.replaceConstantStep_at
      auxEncoding params.width positive inverse control (resultWords P)
      (pointWords P.1) blank false
  rw [show translationPrefixGates (pointWords Q)
      (pointWords (AffinePoint.negate Q)) =
    loadGates ++ additionGates ++ swapGates ++ replaceGates by rfl]
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [hload, additionGates_clean control P, hswap, hreplace]

end

end Pipeline
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
