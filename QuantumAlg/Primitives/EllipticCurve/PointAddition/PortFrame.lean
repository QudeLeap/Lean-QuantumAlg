/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.BlockBank

/-!
# Explicit ports for clean in-place elliptic-curve translation

This module fixes the structural public boundary used by the parameterized
ECADD translation.  The mutable point, temporarily loaded classical constant,
and clean output point each occupy two explicit width-indexed word ports.  The
arithmetic workspace is an abstract suffix whose clean value is chosen by the
caller and therefore does not depend on the input point.

The outer control and the single clean work bit are separate physical wires.
At the clean boundary the constant and output ports are zero, so later stages
must load and unload the classical constant with literal gates.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace PointAddition
namespace PortFrame

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Arithmetic

/-- One coordinate word at the selected field width. -/
abbrev Word (width : Nat) : Type :=
  Nat.FixedWidth.Word width

/-- Affine coordinates represented by two explicit words. -/
abbrev PointWords (width : Nat) : Type :=
  Word width × Word width

/-- Mutable point, loaded constant, and clean output point, in that order. -/
abbrev PublicWords (width : Nat) : Type :=
  PointWords width × (PointWords width × PointWords width)

/-- Public words followed by an arithmetic workspace. -/
abbrev CoreRegisters (Aux : Type) (width : Nat) : Type :=
  PublicWords width × Aux

/-- Outer control, core registers, and one clean control-decomposition bit. -/
abbrev RawRegisters (Aux : Type) (width : Nat) : Type :=
  Bool × (CoreRegisters Aux width × Bool)

/-- Canonical binary encoding of one coordinate word. -/
def wordEncoding (width : Nat) : BinaryLabelEncoding (Word width) :=
  BinaryLabelEncoding.finIdentity width

/-- Product encoding of one affine coordinate pair. -/
def pointEncoding (width : Nat) : BinaryLabelEncoding (PointWords width) :=
  BinaryLabelEncoding.prod (wordEncoding width) (wordEncoding width)

/-- Product encoding of the three explicit point ports. -/
def publicEncoding (width : Nat) : BinaryLabelEncoding (PublicWords width) :=
  BinaryLabelEncoding.prod (pointEncoding width)
    (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))

/-- Public point ports followed by the caller-supplied arithmetic encoding. -/
def coreEncoding {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BinaryLabelEncoding (CoreRegisters Aux width) :=
  BinaryLabelEncoding.prod (publicEncoding width) auxEncoding

/-- Complete encoding with distinct outer-control and clean-work wires. -/
def rawEncoding {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BinaryLabelEncoding (RawRegisters Aux width) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)

/-- Lift one public-carrier bit through the arithmetic suffix and framing bits. -/
def liftPublicBit {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (bit : EncodedBit (publicEncoding width)) :
    EncodedBit (rawEncoding auxEncoding width) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prodLeftBit (publicEncoding width) auxEncoding bit))

/-- Lift one arithmetic-suffix bit through the public carrier and framing bits. -/
def liftAuxBit {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (bit : EncodedBit auxEncoding) :
    EncodedBit (rawEncoding auxEncoding width) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prodRightBit (publicEncoding width) auxEncoding bit))

@[simp] lemma liftAuxBit_get {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (bit : EncodedBit auxEncoding) (state : RawRegisters Aux width) :
    (liftAuxBit auxEncoding width bit).get state = bit.get state.2.1.2 :=
  rfl

/-- Lift one arithmetic-suffix word to the complete translation carrier. -/
def liftAuxWord {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width wordWidth : Nat) (word : EncodedBit.Word auxEncoding wordWidth) :
    EncodedBit.Word (rawEncoding auxEncoding width) wordWidth where
  bit := fun bit => liftAuxBit auxEncoding width (word.bit bit)

/-- Lift auxiliary gates through the public carrier and both framing bits. -/
def liftAuxGates {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (gates : List (EncodedBit.GateSpec auxEncoding)) :
    List (EncodedBit.GateSpec (rawEncoding auxEncoding width)) :=
  ((gates.map (EncodedBit.GateSpec.prodRight (publicEncoding width))).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodRight BinaryLabelEncoding.bool)

/-- Lifting an auxiliary schedule through the public frame preserves its
complete ordered primitive-event trace. -/
lemma liftAuxGates_map_event {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (gates : List (EncodedBit.GateSpec auxEncoding)) :
    (liftAuxGates auxEncoding width gates).map (EncodedBit.GateSpec.event .empty) =
      gates.map (EncodedBit.GateSpec.event .empty) := by
  unfold liftAuxGates
  exact
    (EncodedBit.GateSpec.map_event_prodRight BinaryLabelEncoding.bool _).trans
      ((EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _).trans
        (EncodedBit.GateSpec.map_event_prodRight (publicEncoding width) gates))

/-- Public-frame lifting changes only wire addresses, not the number of
executed primitive gates. -/
lemma liftAuxGates_length {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (gates : List (EncodedBit.GateSpec auxEncoding)) :
    (liftAuxGates auxEncoding width gates).length = gates.length := by
  unfold liftAuxGates
  exact
    (EncodedBit.GateSpec.length_prodRight BinaryLabelEncoding.bool _).trans
      ((EncodedBit.GateSpec.length_prodLeft BinaryLabelEncoding.bool _).trans
        (EncodedBit.GateSpec.length_prodRight (publicEncoding width) gates))

/-- Public-frame lifting preserves the exact Toffoli coordinate of the
underlying auxiliary schedule. -/
lemma liftAuxGates_toffoliMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (gates : List (EncodedBit.GateSpec auxEncoding)) :
    ((liftAuxGates auxEncoding width gates).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (liftAuxGates_map_event auxEncoding width gates)

/-- Folding lifted auxiliary gates preserves the public carrier and framing
bits. -/
lemma liftAuxGates_stepList {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (gates : List (EncodedBit.GateSpec auxEncoding))
    (state : RawRegisters Aux width) :
    EncodedBit.GateSpec.stepList (liftAuxGates auxEncoding width gates) state =
      (state.1, ((state.2.1.1,
        EncodedBit.GateSpec.stepList gates state.2.1.2), state.2.2)) := by
  change EncodedBit.GateSpec.stepList
      (((gates.map (EncodedBit.GateSpec.prodRight (publicEncoding width))).map
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight BinaryLabelEncoding.bool)) state =
      (state.1, ((state.2.1.1,
        EncodedBit.GateSpec.stepList gates state.2.1.2), state.2.2))
  rw [EncodedBit.GateSpec.stepList_prodRight,
    EncodedBit.GateSpec.stepList_prodLeft,
    EncodedBit.GateSpec.stepList_prodRight]

/-- The literal auxiliary gate list realizes its lifted folded action. -/
lemma liftAuxGates_realizes {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (gates : List (EncodedBit.GateSpec auxEncoding)) :
    UnitaryCircuit.Realizes (rawEncoding auxEncoding width)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (liftAuxGates auxEncoding width gates)) environment
      (fun state =>
        (state.1, ((state.2.1.1,
          EncodedBit.GateSpec.stepList gates state.2.1.2), state.2.2))) :=
  EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty _
    (liftAuxGates_stepList auxEncoding width gates)

/-- Every public bit is physically separated from every arithmetic-suffix bit. -/
lemma liftPublicBit_liftAuxBit_wire_ne {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (publicBit : EncodedBit (publicEncoding width))
    (auxBit : EncodedBit auxEncoding) :
    (liftPublicBit auxEncoding width publicBit).wire ≠
      (liftAuxBit auxEncoding width auxBit).wire := by
  exact EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
    (EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
      (Ne.symm
        (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
          (publicEncoding width) auxEncoding auxBit publicBit)))

/-- Distinct arithmetic-suffix wires remain distinct after they are lifted
through the public carrier and both framing bits. -/
lemma liftAuxBit_wire_ne {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    {left right : EncodedBit auxEncoding}
    (hne : left.wire ≠ right.wire) :
    (liftAuxBit auxEncoding width left).wire ≠
      (liftAuxBit auxEncoding width right).wire := by
  exact EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
    (EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
      (EncodedBit.GateSpec.prodRightWire_ne (publicEncoding width) hne))

@[simp] lemma wordEncoding_width (width : Nat) :
    (wordEncoding width).width = width :=
  rfl

@[simp] lemma pointEncoding_width (width : Nat) :
    (pointEncoding width).width = 2 * width := by
  simp [pointEncoding]
  omega

@[simp] lemma publicEncoding_width (width : Nat) :
    (publicEncoding width).width = 6 * width := by
  simp [publicEncoding]
  omega

@[simp] lemma coreEncoding_width {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    (coreEncoding auxEncoding width).width = 6 * width + auxEncoding.width := by
  simp [coreEncoding]

@[simp] lemma rawEncoding_width {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    (rawEncoding auxEncoding width).width =
      6 * width + auxEncoding.width + 2 := by
  simp [rawEncoding]
  omega

/-- Canonical little-endian lens over one raw coordinate word. -/
def fixedWord (width : Nat) : EncodedBit.Word (wordEncoding width) width where
  bit := fun bit => BinaryLabelEncoding.finIdentityBit width
    (WireAddress.littleEndianWire bit)

@[simp] lemma fixedWord_get (width : Nat) (bit : Fin width)
    (word : Word width) :
    ((fixedWord width).bit bit).get word = word.val.testBit bit.val := by
  simp [fixedWord, wordEncoding, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit]

lemma fixedWord_pairwise_ne (width : Nat) (left right : Fin width)
    (hne : left ≠ right) :
    ((fixedWord width).bit left).wire ≠
      ((fixedWord width).bit right).wire := by
  intro hwire
  apply hne
  exact WireAddress.bitIndex_injective hwire

/-- Complete structural port for a standalone fixed-width word. -/
def fixedWordPort (width : Nat) :
    BlockBank.WordPort (wordEncoding width) width where
  word := fixedWord width
  read := id
  set := fun _ value => value
  set_read := by intro state; rfl
  read_set := by intro state value; rfl
  set_set := by intro state first second; rfl
  get_bit := fixedWord_get width
  pairwise_ne := fixedWord_pairwise_ne width
  clear_flip := by intro bit state; rfl

/-- X-coordinate port of one affine coordinate pair. -/
def pointXPort (width : Nat) :
    BlockBank.WordPort (pointEncoding width) width :=
  (fixedWordPort width).prodLeft (wordEncoding width)

/-- Y-coordinate port of one affine coordinate pair. -/
def pointYPort (width : Nat) :
    BlockBank.WordPort (pointEncoding width) width :=
  BlockBank.WordPort.prodRight (wordEncoding width) (fixedWordPort width)

/-- Mutable X-coordinate within the three-point public carrier. -/
def mutableXPublicPort (width : Nat) :
    BlockBank.WordPort (publicEncoding width) width :=
  (pointXPort width).prodLeft
    (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))

/-- Mutable Y-coordinate within the three-point public carrier. -/
def mutableYPublicPort (width : Nat) :
    BlockBank.WordPort (publicEncoding width) width :=
  (pointYPort width).prodLeft
    (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))

/-- Loaded-constant X-coordinate within the three-point public carrier. -/
def constantXPublicPort (width : Nat) :
    BlockBank.WordPort (publicEncoding width) width :=
  BlockBank.WordPort.prodRight (pointEncoding width)
    ((pointXPort width).prodLeft (pointEncoding width))

/-- Loaded-constant Y-coordinate within the three-point public carrier. -/
def constantYPublicPort (width : Nat) :
    BlockBank.WordPort (publicEncoding width) width :=
  BlockBank.WordPort.prodRight (pointEncoding width)
    ((pointYPort width).prodLeft (pointEncoding width))

/-- Clean-output X-coordinate within the three-point public carrier. -/
def outputXPublicPort (width : Nat) :
    BlockBank.WordPort (publicEncoding width) width :=
  BlockBank.WordPort.prodRight (pointEncoding width)
    (BlockBank.WordPort.prodRight (pointEncoding width) (pointXPort width))

/-- Clean-output Y-coordinate within the three-point public carrier. -/
def outputYPublicPort (width : Nat) :
    BlockBank.WordPort (publicEncoding width) width :=
  BlockBank.WordPort.prodRight (pointEncoding width)
    (BlockBank.WordPort.prodRight (pointEncoding width) (pointYPort width))

/-- Lift one public word port through the arithmetic workspace and framing bits. -/
def liftPublicPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat)
    (port : BlockBank.WordPort (publicEncoding width) width) :
    BlockBank.WordPort (rawEncoding auxEncoding width) width :=
  BlockBank.WordPort.prodRight BinaryLabelEncoding.bool
    ((port.prodLeft auxEncoding).prodLeft BinaryLabelEncoding.bool)

/-- Lift one arithmetic-suffix word port through the public carrier and both
framing bits. -/
def liftAuxPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width wordWidth : Nat)
    (port : BlockBank.WordPort auxEncoding wordWidth) :
    BlockBank.WordPort (rawEncoding auxEncoding width) wordWidth :=
  BlockBank.WordPort.prodRight BinaryLabelEncoding.bool
    ((BlockBank.WordPort.prodRight (publicEncoding width) port).prodLeft
      BinaryLabelEncoding.bool)

@[simp] lemma liftPublicPort_read {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (port : BlockBank.WordPort (publicEncoding width) width)
    (state : RawRegisters Aux width) :
    (liftPublicPort auxEncoding width port).read state = port.read state.2.1.1 :=
  rfl

@[simp] lemma liftAuxPort_read {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width wordWidth : Nat)
    (port : BlockBank.WordPort auxEncoding wordWidth)
    (state : RawRegisters Aux width) :
    (liftAuxPort auxEncoding width wordWidth port).read state =
      port.read state.2.1.2 :=
  rfl

@[simp] lemma liftPublicPort_word_bit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (port : BlockBank.WordPort (publicEncoding width) width)
    (bit : Fin width) :
    (liftPublicPort auxEncoding width port).word.bit bit =
      liftPublicBit auxEncoding width (port.word.bit bit) :=
  rfl

@[simp] lemma liftAuxPort_word_bit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width wordWidth : Nat)
    (port : BlockBank.WordPort auxEncoding wordWidth)
    (bit : Fin wordWidth) :
    (liftAuxPort auxEncoding width wordWidth port).word.bit bit =
      liftAuxBit auxEncoding width (port.word.bit bit) :=
  rfl

/-- Public ports and lifted arithmetic ports are physically disjoint. -/
lemma liftPublicPort_liftAuxPort_wire_ne {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width wordWidth : Nat)
    (publicPort : BlockBank.WordPort (publicEncoding width) width)
    (auxPort : BlockBank.WordPort auxEncoding wordWidth)
    (publicBit : Fin width) (auxBit : Fin wordWidth) :
    ((liftPublicPort auxEncoding width publicPort).word.bit publicBit).wire ≠
      ((liftAuxPort auxEncoding width wordWidth auxPort).word.bit auxBit).wire := by
  exact liftPublicBit_liftAuxBit_wire_ne auxEncoding width
    (publicPort.word.bit publicBit) (auxPort.word.bit auxBit)

/-- Mutable X-coordinate on the complete translation carrier. -/
def mutableXPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BlockBank.WordPort (rawEncoding auxEncoding width) width :=
  liftPublicPort auxEncoding width (mutableXPublicPort width)

/-- Mutable Y-coordinate on the complete translation carrier. -/
def mutableYPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BlockBank.WordPort (rawEncoding auxEncoding width) width :=
  liftPublicPort auxEncoding width (mutableYPublicPort width)

/-- Temporarily loaded classical X-coordinate on the complete carrier. -/
def constantXPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BlockBank.WordPort (rawEncoding auxEncoding width) width :=
  liftPublicPort auxEncoding width (constantXPublicPort width)

/-- Temporarily loaded classical Y-coordinate on the complete carrier. -/
def constantYPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BlockBank.WordPort (rawEncoding auxEncoding width) width :=
  liftPublicPort auxEncoding width (constantYPublicPort width)

/-- Clean-output X-coordinate on the complete translation carrier. -/
def outputXPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BlockBank.WordPort (rawEncoding auxEncoding width) width :=
  liftPublicPort auxEncoding width (outputXPublicPort width)

/-- Clean-output Y-coordinate on the complete translation carrier. -/
def outputYPort {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : BlockBank.WordPort (rawEncoding auxEncoding width) width :=
  liftPublicPort auxEncoding width (outputYPublicPort width)

/-- The public control is the leading physical wire. -/
def controlBit {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : EncodedBit (rawEncoding auxEncoding width) :=
  BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    BinaryLabelEncoding.boolBit

/-- The trailing bit is reserved for literal controlled-gate decomposition. -/
def controlWorkBit {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) : EncodedBit (rawEncoding auxEncoding width) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodRightBit (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)

/-- Every lifted public-carrier bit is physically disjoint from the leading
translation control. -/
lemma liftPublicBit_wire_ne_controlBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (bit : EncodedBit (publicEncoding width)) :
    (liftPublicBit auxEncoding width bit).wire ≠
      (controlBit auxEncoding width).wire := by
  exact EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prodLeftBit (publicEncoding width) auxEncoding bit))
    BinaryLabelEncoding.boolBit

/-- Every lifted arithmetic-suffix bit is physically disjoint from the leading
translation control. -/
lemma liftAuxBit_wire_ne_controlBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (bit : EncodedBit auxEncoding) :
    (liftAuxBit auxEncoding width bit).wire ≠
      (controlBit auxEncoding width).wire := by
  exact EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prodRightBit (publicEncoding width) auxEncoding bit))
    BinaryLabelEncoding.boolBit

/-- Every lifted public-carrier bit is physically disjoint from the trailing
clean work bit. -/
lemma liftPublicBit_wire_ne_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (bit : EncodedBit (publicEncoding width)) :
    (liftPublicBit auxEncoding width bit).wire ≠
      (controlWorkBit auxEncoding width).wire := by
  exact EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
    ((EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (coreEncoding auxEncoding width) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit
      (BinaryLabelEncoding.prodLeftBit (publicEncoding width) auxEncoding bit)).symm)

/-- Every lifted arithmetic-suffix bit is physically disjoint from the trailing
clean work bit. -/
lemma liftAuxBit_wire_ne_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (bit : EncodedBit auxEncoding) :
    (liftAuxBit auxEncoding width bit).wire ≠
      (controlWorkBit auxEncoding width).wire := by
  exact EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
    ((EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (coreEncoding auxEncoding width) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit
      (BinaryLabelEncoding.prodRightBit (publicEncoding width) auxEncoding bit)).symm)

/-- The leading translation control and trailing clean work bit occupy
different outer product branches. -/
lemma controlBit_wire_ne_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    (controlBit auxEncoding width).wire ≠
      (controlWorkBit auxEncoding width).wire := by
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodRightBit (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)
    BinaryLabelEncoding.boolBit).symm

/-- Every gate lifted from the arithmetic suffix is disjoint from the leading
translation control. -/
lemma liftAuxGates_bitDisjoint_controlBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (gates : List (EncodedBit.GateSpec auxEncoding))
    (gate : EncodedBit.GateSpec (rawEncoding auxEncoding width))
    (hgate : gate ∈ liftAuxGates auxEncoding width gates) :
    EncodedBit.GateSpec.bitDisjoint (controlBit auxEncoding width) gate := by
  unfold liftAuxGates at hgate
  rcases List.mem_map.mp hgate with ⟨inner, _hinner, rfl⟩
  exact EncodedBit.GateSpec.bitDisjoint_prodRight_leftBit
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool)
    BinaryLabelEncoding.boolBit inner

/-- Every gate lifted from the arithmetic suffix is disjoint from the trailing
clean work bit. -/
lemma liftAuxGates_bitDisjoint_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (gates : List (EncodedBit.GateSpec auxEncoding))
    (gate : EncodedBit.GateSpec (rawEncoding auxEncoding width))
    (hgate : gate ∈ liftAuxGates auxEncoding width gates) :
    EncodedBit.GateSpec.bitDisjoint (controlWorkBit auxEncoding width) gate := by
  unfold liftAuxGates at hgate
  rcases List.mem_map.mp hgate with ⟨inner, hinner, rfl⟩
  rcases List.mem_map.mp hinner with ⟨coreGate, _hcoreGate, rfl⟩
  exact EncodedBit.GateSpec.bitDisjoint_prodRight_of_bitDisjoint
    BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodRightBit (coreEncoding auxEncoding width)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool coreGate)
    (EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit
      (coreEncoding auxEncoding width) BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit coreGate)

/-- All-zero affine word pair. -/
def zeroPoint (width : Nat) : PointWords width :=
  (0, 0)

/-- Clean boundary state.  Only the control and mutable point vary with the
public input; the loaded constant, output, work bit, and caller-selected clean
arithmetic state are fixed. -/
def cleanRegisters {Aux : Type} (cleanAux : Aux) (width : Nat)
    (control : Bool) (mutable : PointWords width) : RawRegisters Aux width :=
  (control,
    (((mutable, (zeroPoint width, zeroPoint width)), cleanAux), false))

@[simp] lemma cleanRegisters_control {Aux : Type} (cleanAux : Aux)
    (width : Nat) (control : Bool) (mutable : PointWords width) :
    (cleanRegisters cleanAux width control mutable).1 = control :=
  rfl

@[simp] lemma cleanRegisters_mutable {Aux : Type} (cleanAux : Aux)
    (width : Nat) (control : Bool) (mutable : PointWords width) :
    (cleanRegisters cleanAux width control mutable).2.1.1.1 = mutable :=
  rfl

@[simp] lemma cleanRegisters_constant {Aux : Type} (cleanAux : Aux)
    (width : Nat) (control : Bool) (mutable : PointWords width) :
    (cleanRegisters cleanAux width control mutable).2.1.1.2.1 =
      zeroPoint width :=
  rfl

@[simp] lemma cleanRegisters_output {Aux : Type} (cleanAux : Aux)
    (width : Nat) (control : Bool) (mutable : PointWords width) :
    (cleanRegisters cleanAux width control mutable).2.1.1.2.2 =
      zeroPoint width :=
  rfl

@[simp] lemma cleanRegisters_aux {Aux : Type} (cleanAux : Aux)
    (width : Nat) (control : Bool) (mutable : PointWords width) :
    (cleanRegisters cleanAux width control mutable).2.1.2 = cleanAux :=
  rfl

@[simp] lemma cleanRegisters_controlWork {Aux : Type} (cleanAux : Aux)
    (width : Nat) (control : Bool) (mutable : PointWords width) :
    (cleanRegisters cleanAux width control mutable).2.2 = false :=
  rfl

/-- Fixed-width xor mask replacing one classical word by another. -/
def wordDelta {width : Nat} (source target : Word width) : Fin (2 ^ width) :=
  ⟨source.val ^^^ target.val,
    Nat.xor_lt_two_pow source.isLt target.isLt⟩

@[simp] lemma wordDelta_testBit {width : Nat} (source target : Word width)
    (bit : Fin width) :
    (wordDelta source target).val.testBit bit.val =
      (source.val.testBit bit.val ^^ target.val.testBit bit.val) := by
  simp [wordDelta, Nat.testBit_xor]

/-! ## Literal load, replace, and swap stages -/

/-- Lifting two distinct public-port wires through the common framing layers
preserves their physical separation. -/
lemma liftPublicPort_wire_ne {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (left right : BlockBank.WordPort (publicEncoding width) width)
    (leftBit rightBit : Fin width)
    (hne : (left.word.bit leftBit).wire ≠
      (right.word.bit rightBit).wire) :
    (((liftPublicPort auxEncoding width left).word.bit leftBit).wire ≠
      ((liftPublicPort auxEncoding width right).word.bit rightBit).wire) := by
  exact EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
    (EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
      (EncodedBit.GateSpec.prodLeftWire_ne auxEncoding hne))

/-- Mutable and output X-coordinate wires occupy different outer product
branches, for every pair of word indices. -/
lemma mutableXPublic_outputXPublic_wire_ne (width : Nat)
    (left right : Fin width) :
    ((mutableXPublicPort width).word.bit left).wire ≠
      ((outputXPublicPort width).word.bit right).wire := by
  change
    (BinaryLabelEncoding.prodLeftBit (pointEncoding width)
      (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))
      ((pointXPort width).word.bit left)).wire ≠
    (BinaryLabelEncoding.prodRightBit (pointEncoding width)
      (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))
      (BinaryLabelEncoding.prodRightBit (pointEncoding width)
        (pointEncoding width) ((pointXPort width).word.bit right))).wire
  exact Ne.symm
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (pointEncoding width)
      (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))
      (BinaryLabelEncoding.prodRightBit (pointEncoding width)
        (pointEncoding width) ((pointXPort width).word.bit right))
      ((pointXPort width).word.bit left))

/-- Mutable and output Y-coordinate wires occupy different outer product
branches, for every pair of word indices. -/
lemma mutableYPublic_outputYPublic_wire_ne (width : Nat)
    (left right : Fin width) :
    ((mutableYPublicPort width).word.bit left).wire ≠
      ((outputYPublicPort width).word.bit right).wire := by
  change
    (BinaryLabelEncoding.prodLeftBit (pointEncoding width)
      (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))
      ((pointYPort width).word.bit left)).wire ≠
    (BinaryLabelEncoding.prodRightBit (pointEncoding width)
      (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))
      (BinaryLabelEncoding.prodRightBit (pointEncoding width)
        (pointEncoding width) ((pointYPort width).word.bit right))).wire
  exact Ne.symm
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (pointEncoding width)
      (BinaryLabelEncoding.prod (pointEncoding width) (pointEncoding width))
      (BinaryLabelEncoding.prodRightBit (pointEncoding width)
        (pointEncoding width) ((pointYPort width).word.bit right))
      ((pointYPort width).word.bit left))

/-- Mutable and output X-coordinate wires remain separated on the complete
translation carrier. -/
lemma mutableX_outputX_wire_ne {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (left right : Fin width) :
    ((mutableXPort auxEncoding width).word.bit left).wire ≠
      ((outputXPort auxEncoding width).word.bit right).wire :=
  liftPublicPort_wire_ne auxEncoding width _ _ left right
    (mutableXPublic_outputXPublic_wire_ne width left right)

/-- Mutable and output Y-coordinate wires remain separated on the complete
translation carrier. -/
lemma mutableY_outputY_wire_ne {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (left right : Fin width) :
    ((mutableYPort auxEncoding width).word.bit left).wire ≠
      ((outputYPort auxEncoding width).word.bit right).wire :=
  liftPublicPort_wire_ne auxEncoding width _ _ left right
    (mutableYPublic_outputYPublic_wire_ne width left right)

private lemma xorConstantGates_bitDisjoint
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (observed : EncodedBit encoding) (target : EncodedBit.Word encoding width)
    (constant : Fin (2 ^ width))
    (htarget : ∀ bit, (target.bit bit).wire ≠ observed.wire)
    (gate : EncodedBit.GateSpec encoding)
    (hgate : gate ∈ EncodedBit.Word.xorConstantGates target constant) :
    EncodedBit.GateSpec.bitDisjoint observed gate := by
  rw [EncodedBit.Word.xorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  exact htarget bit

private lemma wordSwapGates_bitDisjoint
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (observed : EncodedBit encoding)
    (left right : EncodedBit.Word encoding width)
    (hleftRight : ∀ bit, (left.bit bit).wire ≠ (right.bit bit).wire)
    (hleft : ∀ bit, (left.bit bit).wire ≠ observed.wire)
    (hright : ∀ bit, (right.bit bit).wire ≠ observed.wire)
    (gate : EncodedBit.GateSpec encoding)
    (hgate : gate ∈ EncodedBit.Word.swapGates left right hleftRight) :
    EncodedBit.GateSpec.bitDisjoint observed gate := by
  rw [EncodedBit.Word.swapGates] at hgate
  simp only [List.mem_flatMap] at hgate
  rcases hgate with ⟨bit, _hbit, hgate⟩
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact ⟨hleft bit, hright bit⟩
  · exact ⟨hright bit, hleft bit⟩
  · exact ⟨hleft bit, hright bit⟩

/-- Literal X-gate list loading a fixed classical point into its clean ports. -/
def loadConstantGates {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (constant : PointWords width) :
    List (EncodedBit.GateSpec (rawEncoding auxEncoding width)) :=
  EncodedBit.Word.xorConstantGates
      (constantXPort auxEncoding width).word constant.1 ++
    EncodedBit.Word.xorConstantGates
      (constantYPort auxEncoding width).word constant.2

/-- Loading a literal point never reads or writes the leading translation
control. -/
lemma loadConstantGates_bitDisjoint_controlBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ∀ gate, gate ∈ loadConstantGates auxEncoding width constant →
      EncodedBit.GateSpec.bitDisjoint (controlBit auxEncoding width) gate := by
  intro gate hgate
  unfold loadConstantGates at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact xorConstantGates_bitDisjoint _ _ constant.1
      (fun bit => by
        simpa only [constantXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((constantXPublicPort width).word.bit bit)) gate hgate
  · exact xorConstantGates_bitDisjoint _ _ constant.2
      (fun bit => by
        simpa only [constantYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((constantYPublicPort width).word.bit bit)) gate hgate

/-- Loading a literal point never reads or writes the clean control-work bit. -/
lemma loadConstantGates_bitDisjoint_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ∀ gate, gate ∈ loadConstantGates auxEncoding width constant →
      EncodedBit.GateSpec.bitDisjoint
        (controlWorkBit auxEncoding width) gate := by
  intro gate hgate
  unfold loadConstantGates at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact xorConstantGates_bitDisjoint _ _ constant.1
      (fun bit => by
        simpa only [constantXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((constantXPublicPort width).word.bit bit)) gate hgate
  · exact xorConstantGates_bitDisjoint _ _ constant.2
      (fun bit => by
        simpa only [constantYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((constantYPublicPort width).word.bit bit)) gate hgate

/-- Actual base-gate program loading a fixed classical point. -/
def loadConstantProgram {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (constant : PointWords width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (rawEncoding auxEncoding width).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (loadConstantGates auxEncoding width constant)

/-- Folded action of the fixed-point loader. -/
def loadConstantStep {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (constant : PointWords width) :
    RawRegisters Aux width → RawRegisters Aux width :=
  EncodedBit.GateSpec.stepList
    (loadConstantGates auxEncoding width constant)

lemma loadConstant_realizes {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    UnitaryCircuit.Realizes (rawEncoding auxEncoding width)
      (loadConstantProgram auxEncoding width constant) environment
      (loadConstantStep auxEncoding width constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

/-- A literal constant xor updates one structural word port to a word whose
bits have the corresponding xor values. -/
lemma xorConstantStep_eq_set_of_testBit
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (port : BlockBank.WordPort encoding width)
    (constant : Fin (2 ^ width)) (state : Data)
    (value : Nat.FixedWidth.Word width)
    (hvalue : ∀ bit : Fin width, value.val.testBit bit.val =
      ((port.read state).val.testBit bit.val ^^
        constant.val.testBit bit.val)) :
    EncodedBit.Word.xorConstantStep port.word constant state =
      port.set state value := by
  have hframe :
      port.set (EncodedBit.Word.xorConstantStep port.word constant state) 0 =
        port.set state 0 := by
    unfold EncodedBit.Word.xorConstantStep
    apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project := fun next => port.set next 0)
    intro gate hgate
    rw [EncodedBit.Word.xorConstantGates] at hgate
    rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
    exact port.clear_flip bit
  have hresult :
      port.read (EncodedBit.Word.xorConstantStep port.word constant state) =
        value := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← port.get_bit bit
      (EncodedBit.Word.xorConstantStep port.word constant state)]
    rw [EncodedBit.Word.xorConstantStep_get_target port.word constant bit
      (fun other hne => port.pairwise_ne other bit hne)]
    rw [port.get_bit bit state]
    exact (hvalue bit).symm
  calc
    EncodedBit.Word.xorConstantStep port.word constant state =
        port.set
          (port.set
            (EncodedBit.Word.xorConstantStep port.word constant state) 0)
          (port.read (EncodedBit.Word.xorConstantStep port.word constant state)) := by
            rw [port.set_set, port.set_read]
    _ = port.set (port.set state 0) value := by rw [hframe, hresult]
    _ = port.set state value := by rw [port.set_set]

/-- A controlled literal constant xor updates one structural word port to the
word whose bits are toggled by the conjunction of the control and constant. -/
lemma controlledXorConstantStep_eq_set_of_testBit
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (port : BlockBank.WordPort encoding width)
    (control : EncodedBit encoding)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : ∀ bit, control.wire ≠ (port.word.bit bit).wire)
    (state : Data) (value : Nat.FixedWidth.Word width)
    (hvalue : ∀ bit : Fin width, value.val.testBit bit.val =
      ((port.read state).val.testBit bit.val ^^
        (control.get state && constant.val.testBit bit.val))) :
    EncodedBit.Word.controlledXorConstantStep control port.word constant
        hcontrolTarget state =
      port.set state value := by
  have hframe :
      port.set
          (EncodedBit.Word.controlledXorConstantStep control port.word constant
            hcontrolTarget state) 0 =
        port.set state 0 := by
    unfold EncodedBit.Word.controlledXorConstantStep
    apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project := fun next => port.set next 0)
    intro gate hgate
    rw [EncodedBit.Word.controlledXorConstantGates] at hgate
    rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
    exact port.clear_flip bit
  have hresult :
      port.read
          (EncodedBit.Word.controlledXorConstantStep control port.word constant
            hcontrolTarget state) = value := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← port.get_bit bit]
    rw [EncodedBit.Word.controlledXorConstantStep_get_target control port.word
      constant hcontrolTarget bit
      (fun other hne => port.pairwise_ne other bit hne)]
    rw [port.get_bit bit state]
    exact (hvalue bit).symm
  calc
    EncodedBit.Word.controlledXorConstantStep control port.word constant
        hcontrolTarget state =
        port.set
          (port.set
            (EncodedBit.Word.controlledXorConstantStep control port.word
              constant hcontrolTarget state) 0)
          (port.read
            (EncodedBit.Word.controlledXorConstantStep control port.word
              constant hcontrolTarget state)) := by
            rw [port.set_set, port.set_read]
    _ = port.set (port.set state 0) value := by rw [hframe, hresult]
    _ = port.set state value := by rw [port.set_set]

/-- Loading a literal point updates only the previously clean constant port. -/
lemma loadConstantStep_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) (control : Bool)
    (mutable output : PointWords width) (aux : Aux) (controlWork : Bool) :
    loadConstantStep auxEncoding width constant
        (control, (((mutable, (zeroPoint width, output)), aux), controlWork)) =
      (control, (((mutable, (constant, output)), aux), controlWork)) := by
  let input : RawRegisters Aux width :=
    (control, (((mutable, (zeroPoint width, output)), aux), controlWork))
  let outputState : RawRegisters Aux width :=
    (control, (((mutable, (constant, output)), aux), controlWork))
  change loadConstantStep auxEncoding width constant input = outputState
  unfold loadConstantStep loadConstantGates
  rw [EncodedBit.GateSpec.stepList_append]
  change EncodedBit.Word.xorConstantStep
      (constantYPort auxEncoding width).word constant.2
      (EncodedBit.Word.xorConstantStep
        (constantXPort auxEncoding width).word constant.1 input) = outputState
  have hx := xorConstantStep_eq_set_of_testBit
    (constantXPort auxEncoding width) constant.1 input constant.1 (by
      intro bit
      rw [show (constantXPort auxEncoding width).read input = 0 by rfl]
      simp)
  rw [hx]
  have hy := xorConstantStep_eq_set_of_testBit
    (constantYPort auxEncoding width) constant.2
    ((constantXPort auxEncoding width).set input constant.1) constant.2 (by
      intro bit
      rw [show (constantYPort auxEncoding width).read
        ((constantXPort auxEncoding width).set input constant.1) = 0 by rfl]
      simp)
  rw [hy]
  rfl

/-- The literal point loader maps the corresponding encoded basis ket. -/
lemma loadConstantProgram_applyNormalized_encoded_ket_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) (control : Bool)
    (mutable output : PointWords width) (aux : Aux) (controlWork : Bool) :
    (loadConstantProgram auxEncoding width constant).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
            ((rawEncoding auxEncoding width).encode
            (control,
              (((mutable, (zeroPoint width, output)), aux), controlWork))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
          ((rawEncoding auxEncoding width).encode
            (control, (((mutable, (constant, output)), aux), controlWork)))) := by
  rw [(loadConstant_realizes (environment := environment)
    auxEncoding width constant).apply_encoded_ket]
  rw [loadConstantStep_at auxEncoding width constant control mutable output aux
    controlWork]

/-- Literal X-gate list replacing one loaded classical point by another. -/
def replaceConstantGates {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (source target : PointWords width) :
    List (EncodedBit.GateSpec (rawEncoding auxEncoding width)) :=
  EncodedBit.Word.xorConstantGates
      (constantXPort auxEncoding width).word
      (wordDelta source.1 target.1) ++
    EncodedBit.Word.xorConstantGates
      (constantYPort auxEncoding width).word
      (wordDelta source.2 target.2)

/-- Replacing a loaded point never reads or writes the leading translation
control. -/
lemma replaceConstantGates_bitDisjoint_controlBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    ∀ gate, gate ∈ replaceConstantGates auxEncoding width source target →
      EncodedBit.GateSpec.bitDisjoint (controlBit auxEncoding width) gate := by
  intro gate hgate
  unfold replaceConstantGates at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact xorConstantGates_bitDisjoint _ _ (wordDelta source.1 target.1)
      (fun bit => by
        simpa only [constantXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((constantXPublicPort width).word.bit bit)) gate hgate
  · exact xorConstantGates_bitDisjoint _ _ (wordDelta source.2 target.2)
      (fun bit => by
        simpa only [constantYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((constantYPublicPort width).word.bit bit)) gate hgate

/-- Replacing a loaded point never reads or writes the clean control-work bit. -/
lemma replaceConstantGates_bitDisjoint_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    ∀ gate, gate ∈ replaceConstantGates auxEncoding width source target →
      EncodedBit.GateSpec.bitDisjoint
        (controlWorkBit auxEncoding width) gate := by
  intro gate hgate
  unfold replaceConstantGates at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact xorConstantGates_bitDisjoint _ _ (wordDelta source.1 target.1)
      (fun bit => by
        simpa only [constantXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((constantXPublicPort width).word.bit bit)) gate hgate
  · exact xorConstantGates_bitDisjoint _ _ (wordDelta source.2 target.2)
      (fun bit => by
        simpa only [constantYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((constantYPublicPort width).word.bit bit)) gate hgate

/-- Actual base-gate program replacing one loaded point constant. -/
def replaceConstantProgram {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (rawEncoding auxEncoding width).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (replaceConstantGates auxEncoding width source target)

/-- Folded action of the point-constant replacement. -/
def replaceConstantStep {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    RawRegisters Aux width → RawRegisters Aux width :=
  EncodedBit.GateSpec.stepList
    (replaceConstantGates auxEncoding width source target)

lemma replaceConstant_realizes {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    UnitaryCircuit.Realizes (rawEncoding auxEncoding width)
      (replaceConstantProgram auxEncoding width source target) environment
      (replaceConstantStep auxEncoding width source target) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

/-- Replacing a loaded literal point updates only the constant port. -/
lemma replaceConstantStep_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) (control : Bool)
    (mutable output : PointWords width) (aux : Aux) (controlWork : Bool) :
    replaceConstantStep auxEncoding width source target
        (control, (((mutable, (source, output)), aux), controlWork)) =
      (control, (((mutable, (target, output)), aux), controlWork)) := by
  let input : RawRegisters Aux width :=
    (control, (((mutable, (source, output)), aux), controlWork))
  let outputState : RawRegisters Aux width :=
    (control, (((mutable, (target, output)), aux), controlWork))
  change replaceConstantStep auxEncoding width source target input = outputState
  unfold replaceConstantStep replaceConstantGates
  rw [EncodedBit.GateSpec.stepList_append]
  change EncodedBit.Word.xorConstantStep
      (constantYPort auxEncoding width).word (wordDelta source.2 target.2)
      (EncodedBit.Word.xorConstantStep
        (constantXPort auxEncoding width).word (wordDelta source.1 target.1)
        input) = outputState
  have hdeltaX (bit : Fin width) :
      target.1.val.testBit bit.val =
        (source.1.val.testBit bit.val ^^
          (wordDelta source.1 target.1).val.testBit bit.val) := by
    rw [wordDelta_testBit]
    cases source.1.val.testBit bit.val <;>
      cases target.1.val.testBit bit.val <;> rfl
  have hdeltaY (bit : Fin width) :
      target.2.val.testBit bit.val =
        (source.2.val.testBit bit.val ^^
          (wordDelta source.2 target.2).val.testBit bit.val) := by
    rw [wordDelta_testBit]
    cases source.2.val.testBit bit.val <;>
      cases target.2.val.testBit bit.val <;> rfl
  have hx := xorConstantStep_eq_set_of_testBit
    (constantXPort auxEncoding width) (wordDelta source.1 target.1) input
    target.1 (by
      intro bit
      rw [show (constantXPort auxEncoding width).read input = source.1 by rfl]
      exact hdeltaX bit)
  rw [hx]
  have hy := xorConstantStep_eq_set_of_testBit
    (constantYPort auxEncoding width) (wordDelta source.2 target.2)
    ((constantXPort auxEncoding width).set input target.1) target.2 (by
      intro bit
      rw [show (constantYPort auxEncoding width).read
        ((constantXPort auxEncoding width).set input target.1) = source.2 by rfl]
      exact hdeltaY bit)
  rw [hy]
  rfl

/-- The literal point replacement maps the corresponding encoded basis ket. -/
lemma replaceConstantProgram_applyNormalized_encoded_ket_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) (control : Bool)
    (mutable output : PointWords width) (aux : Aux) (controlWork : Bool) :
    (replaceConstantProgram auxEncoding width source target).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
            ((rawEncoding auxEncoding width).encode
              (control, (((mutable, (source, output)), aux), controlWork))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
          ((rawEncoding auxEncoding width).encode
            (control, (((mutable, (target, output)), aux), controlWork)))) := by
  rw [(replaceConstant_realizes (environment := environment)
    auxEncoding width source target).apply_encoded_ket]
  rw [replaceConstantStep_at auxEncoding width source target control mutable
    output aux controlWork]

/-- Reverse literal gate list unloading the final classical point constant. -/
def unloadConstantGates {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (constant : PointWords width) :
    List (EncodedBit.GateSpec (rawEncoding auxEncoding width)) :=
  (loadConstantGates auxEncoding width constant).reverse

/-- Unloading a literal point never reads or writes the leading translation
control. -/
lemma unloadConstantGates_bitDisjoint_controlBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ∀ gate, gate ∈ unloadConstantGates auxEncoding width constant →
      EncodedBit.GateSpec.bitDisjoint (controlBit auxEncoding width) gate := by
  intro gate hgate
  unfold unloadConstantGates at hgate
  exact loadConstantGates_bitDisjoint_controlBit auxEncoding width constant gate
    (List.mem_reverse.mp hgate)

/-- Unloading a literal point never reads or writes the clean control-work bit. -/
lemma unloadConstantGates_bitDisjoint_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ∀ gate, gate ∈ unloadConstantGates auxEncoding width constant →
      EncodedBit.GateSpec.bitDisjoint
        (controlWorkBit auxEncoding width) gate := by
  intro gate hgate
  unfold unloadConstantGates at hgate
  exact loadConstantGates_bitDisjoint_controlWorkBit auxEncoding width constant
    gate (List.mem_reverse.mp hgate)

/-- Actual reverse base-gate program unloading a fixed classical point. -/
def unloadConstantProgram {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (rawEncoding auxEncoding width).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (unloadConstantGates auxEncoding width constant)

/-- Folded action of the fixed-point unloader. -/
def unloadConstantStep {Aux : Type} (auxEncoding : BinaryLabelEncoding Aux)
    (width : Nat) (constant : PointWords width) :
    RawRegisters Aux width → RawRegisters Aux width :=
  EncodedBit.GateSpec.stepList
    (unloadConstantGates auxEncoding width constant)

lemma unloadConstant_realizes {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    UnitaryCircuit.Realizes (rawEncoding auxEncoding width)
      (unloadConstantProgram auxEncoding width constant) environment
      (unloadConstantStep auxEncoding width constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

/-- Unloading a literal point restores the clean constant port while leaving
the other raw-register fields unchanged. -/
lemma unloadConstantStep_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) (control : Bool)
    (mutable output : PointWords width) (aux : Aux) (controlWork : Bool) :
    unloadConstantStep auxEncoding width constant
        (control, (((mutable, (constant, output)), aux), controlWork)) =
      (control, (((mutable, (zeroPoint width, output)), aux), controlWork)) := by
  let clean : RawRegisters Aux width :=
    (control, (((mutable, (zeroPoint width, output)), aux), controlWork))
  let loaded : RawRegisters Aux width :=
    (control, (((mutable, (constant, output)), aux), controlWork))
  change unloadConstantStep auxEncoding width constant loaded = clean
  have hload : loadConstantStep auxEncoding width constant clean = loaded := by
    exact loadConstantStep_at auxEncoding width constant control mutable output
      aux controlWork
  have hinverse := EncodedBit.GateSpec.stepList_reverse_stepList
    (loadConstantGates auxEncoding width constant) clean
  change unloadConstantStep auxEncoding width constant
      (loadConstantStep auxEncoding width constant clean) = clean at hinverse
  rw [hload] at hinverse
  exact hinverse

/-- The literal point unloader maps the corresponding encoded basis ket. -/
lemma unloadConstantProgram_applyNormalized_encoded_ket_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) (control : Bool)
    (mutable output : PointWords width) (aux : Aux) (controlWork : Bool) :
    (unloadConstantProgram auxEncoding width constant).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
            ((rawEncoding auxEncoding width).encode
              (control, (((mutable, (constant, output)), aux), controlWork))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
          ((rawEncoding auxEncoding width).encode
            (control,
              (((mutable, (zeroPoint width, output)), aux), controlWork)))) := by
  rw [(unloadConstant_realizes (environment := environment)
    auxEncoding width constant).apply_encoded_ket]
  rw [unloadConstantStep_at auxEncoding width constant control mutable output aux
    controlWork]

/-- Six CNOTs per field bit swap the mutable and output coordinate pairs. -/
def swapMutableOutputGates {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    List (EncodedBit.GateSpec (rawEncoding auxEncoding width)) :=
  EncodedBit.Word.swapGates
      (mutableXPort auxEncoding width).word
      (outputXPort auxEncoding width).word
      (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit) ++
    EncodedBit.Word.swapGates
      (mutableYPort auxEncoding width).word
      (outputYPort auxEncoding width).word
      (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit)

/-- Swapping the mutable and output points never reads or writes the leading
translation control. -/
lemma swapMutableOutputGates_bitDisjoint_controlBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    ∀ gate, gate ∈ swapMutableOutputGates auxEncoding width →
      EncodedBit.GateSpec.bitDisjoint (controlBit auxEncoding width) gate := by
  intro gate hgate
  unfold swapMutableOutputGates at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact wordSwapGates_bitDisjoint (controlBit auxEncoding width)
      (mutableXPort auxEncoding width).word
      (outputXPort auxEncoding width).word
      (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit)
      (fun bit => by
        simpa only [mutableXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((mutableXPublicPort width).word.bit bit))
      (fun bit => by
        simpa only [outputXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((outputXPublicPort width).word.bit bit)) gate hgate
  · exact wordSwapGates_bitDisjoint (controlBit auxEncoding width)
      (mutableYPort auxEncoding width).word
      (outputYPort auxEncoding width).word
      (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit)
      (fun bit => by
        simpa only [mutableYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((mutableYPublicPort width).word.bit bit))
      (fun bit => by
        simpa only [outputYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlBit auxEncoding width
            ((outputYPublicPort width).word.bit bit)) gate hgate

/-- Swapping the mutable and output points never reads or writes the clean
control-work bit. -/
lemma swapMutableOutputGates_bitDisjoint_controlWorkBit {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    ∀ gate, gate ∈ swapMutableOutputGates auxEncoding width →
      EncodedBit.GateSpec.bitDisjoint
        (controlWorkBit auxEncoding width) gate := by
  intro gate hgate
  unfold swapMutableOutputGates at hgate
  rcases List.mem_append.mp hgate with hgate | hgate
  · exact wordSwapGates_bitDisjoint (controlWorkBit auxEncoding width)
      (mutableXPort auxEncoding width).word
      (outputXPort auxEncoding width).word
      (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit)
      (fun bit => by
        simpa only [mutableXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((mutableXPublicPort width).word.bit bit))
      (fun bit => by
        simpa only [outputXPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((outputXPublicPort width).word.bit bit)) gate hgate
  · exact wordSwapGates_bitDisjoint (controlWorkBit auxEncoding width)
      (mutableYPort auxEncoding width).word
      (outputYPort auxEncoding width).word
      (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit)
      (fun bit => by
        simpa only [mutableYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((mutableYPublicPort width).word.bit bit))
      (fun bit => by
        simpa only [outputYPort, liftPublicPort_word_bit] using
          liftPublicBit_wire_ne_controlWorkBit auxEncoding width
            ((outputYPublicPort width).word.bit bit)) gate hgate

/-- Actual three-CNOT-per-word-bit swap program for both coordinates. -/
def swapMutableOutputProgram {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (rawEncoding auxEncoding width).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (swapMutableOutputGates auxEncoding width)

/-- Folded action of the mutable/output point swap. -/
def swapMutableOutputStep {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    RawRegisters Aux width → RawRegisters Aux width :=
  EncodedBit.GateSpec.stepList
    (swapMutableOutputGates auxEncoding width)

lemma swapMutableOutput_realizes {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    UnitaryCircuit.Realizes (rawEncoding auxEncoding width)
      (swapMutableOutputProgram auxEncoding width) environment
      (swapMutableOutputStep auxEncoding width) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

/-- The X-coordinate word swap preserves every other raw-register field. -/
private lemma swapMutableOutputXStep_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (control : Bool) (mutable constant output : PointWords width)
    (aux : Aux) (controlWork : Bool) :
    EncodedBit.Word.swapStep
        (mutableXPort auxEncoding width).word
        (outputXPort auxEncoding width).word
        (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit)
        (control, (((mutable, (constant, output)), aux), controlWork)) =
      (control,
        ((((output.1, mutable.2),
          (constant, (mutable.1, output.2))), aux), controlWork)) := by
  let state : RawRegisters Aux width :=
    (control, (((mutable, (constant, output)), aux), controlWork))
  let result := EncodedBit.Word.swapStep
    (mutableXPort auxEncoding width).word
    (outputXPort auxEncoding width).word
    (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit) state
  change result =
    (control,
      ((((output.1, mutable.2),
        (constant, (mutable.1, output.2))), aux), controlWork))
  have hframe :
      (result.1,
        (result.2.1.1.1.2,
          (result.2.1.1.2.1,
            (result.2.1.1.2.2.2, (result.2.1.2, result.2.2))))) =
      (control, (mutable.2, (constant, (output.2, (aux, controlWork))))) := by
    exact EncodedBit.Word.swapStep_preserves_projection
      (mutableXPort auxEncoding width).word
      (outputXPort auxEncoding width).word
      (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit)
      (fun current : RawRegisters Aux width =>
        (current.1,
          (current.2.1.1.1.2,
            (current.2.1.1.2.1,
              (current.2.1.1.2.2.2, (current.2.1.2, current.2.2))))))
      (by intro _bit current; rfl)
      (by intro _bit current; rfl) state
  have hcontrol : result.1 = control :=
    congrArg Prod.fst hframe
  have hmutableY : result.2.1.1.1.2 = mutable.2 :=
    congrArg (fun frame => frame.2.1) hframe
  have hconstant : result.2.1.1.2.1 = constant :=
    congrArg (fun frame => frame.2.2.1) hframe
  have houtputY : result.2.1.1.2.2.2 = output.2 :=
    congrArg (fun frame => frame.2.2.2.1) hframe
  have haux : result.2.1.2 = aux :=
    congrArg (fun frame => frame.2.2.2.2.1) hframe
  have hcontrolWork : result.2.2 = controlWork :=
    congrArg (fun frame => frame.2.2.2.2.2) hframe
  have hmutableX : result.2.1.1.1.1 = output.1 := by
    change (mutableXPort auxEncoding width).read result = output.1
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← (mutableXPort auxEncoding width).get_bit bit result]
    have hbit := congrFun (EncodedBit.Word.swapStep_get_left_word
      (mutableXPort auxEncoding width).word
      (outputXPort auxEncoding width).word
      (fun index => mutableX_outputX_wire_ne auxEncoding width index index)
      (mutableXPort auxEncoding width).pairwise_ne
      (outputXPort auxEncoding width).pairwise_ne
      (fun left right => mutableX_outputX_wire_ne auxEncoding width left right)
      state) bit
    rw [hbit]
    exact (outputXPort auxEncoding width).get_bit bit state
  have houtputX : result.2.1.1.2.2.1 = mutable.1 := by
    change (outputXPort auxEncoding width).read result = mutable.1
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← (outputXPort auxEncoding width).get_bit bit result]
    have hbit := congrFun (EncodedBit.Word.swapStep_get_right_word
      (mutableXPort auxEncoding width).word
      (outputXPort auxEncoding width).word
      (fun index => mutableX_outputX_wire_ne auxEncoding width index index)
      (mutableXPort auxEncoding width).pairwise_ne
      (outputXPort auxEncoding width).pairwise_ne
      (fun left right => mutableX_outputX_wire_ne auxEncoding width left right)
      state) bit
    rw [hbit]
    exact (mutableXPort auxEncoding width).get_bit bit state
  apply Prod.ext
  · exact hcontrol
  · apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact Prod.ext hmutableX hmutableY
        · exact Prod.ext hconstant (Prod.ext houtputX houtputY)
      · exact haux
    · exact hcontrolWork

/-- The Y-coordinate word swap preserves every other raw-register field. -/
private lemma swapMutableOutputYStep_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (control : Bool) (mutable constant output : PointWords width)
    (aux : Aux) (controlWork : Bool) :
    EncodedBit.Word.swapStep
        (mutableYPort auxEncoding width).word
        (outputYPort auxEncoding width).word
        (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit)
        (control, (((mutable, (constant, output)), aux), controlWork)) =
      (control,
        ((((mutable.1, output.2),
          (constant, (output.1, mutable.2))), aux), controlWork)) := by
  let state : RawRegisters Aux width :=
    (control, (((mutable, (constant, output)), aux), controlWork))
  let result := EncodedBit.Word.swapStep
    (mutableYPort auxEncoding width).word
    (outputYPort auxEncoding width).word
    (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit) state
  change result =
    (control,
      ((((mutable.1, output.2),
        (constant, (output.1, mutable.2))), aux), controlWork))
  have hframe :
      (result.1,
        (result.2.1.1.1.1,
          (result.2.1.1.2.1,
            (result.2.1.1.2.2.1, (result.2.1.2, result.2.2))))) =
      (control, (mutable.1, (constant, (output.1, (aux, controlWork))))) := by
    exact EncodedBit.Word.swapStep_preserves_projection
      (mutableYPort auxEncoding width).word
      (outputYPort auxEncoding width).word
      (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit)
      (fun current : RawRegisters Aux width =>
        (current.1,
          (current.2.1.1.1.1,
            (current.2.1.1.2.1,
              (current.2.1.1.2.2.1, (current.2.1.2, current.2.2))))))
      (by intro _bit current; rfl)
      (by intro _bit current; rfl) state
  have hcontrol : result.1 = control :=
    congrArg Prod.fst hframe
  have hmutableX : result.2.1.1.1.1 = mutable.1 :=
    congrArg (fun frame => frame.2.1) hframe
  have hconstant : result.2.1.1.2.1 = constant :=
    congrArg (fun frame => frame.2.2.1) hframe
  have houtputX : result.2.1.1.2.2.1 = output.1 :=
    congrArg (fun frame => frame.2.2.2.1) hframe
  have haux : result.2.1.2 = aux :=
    congrArg (fun frame => frame.2.2.2.2.1) hframe
  have hcontrolWork : result.2.2 = controlWork :=
    congrArg (fun frame => frame.2.2.2.2.2) hframe
  have hmutableY : result.2.1.1.1.2 = output.2 := by
    change (mutableYPort auxEncoding width).read result = output.2
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← (mutableYPort auxEncoding width).get_bit bit result]
    have hbit := congrFun (EncodedBit.Word.swapStep_get_left_word
      (mutableYPort auxEncoding width).word
      (outputYPort auxEncoding width).word
      (fun index => mutableY_outputY_wire_ne auxEncoding width index index)
      (mutableYPort auxEncoding width).pairwise_ne
      (outputYPort auxEncoding width).pairwise_ne
      (fun left right => mutableY_outputY_wire_ne auxEncoding width left right)
      state) bit
    rw [hbit]
    exact (outputYPort auxEncoding width).get_bit bit state
  have houtputY : result.2.1.1.2.2.2 = mutable.2 := by
    change (outputYPort auxEncoding width).read result = mutable.2
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← (outputYPort auxEncoding width).get_bit bit result]
    have hbit := congrFun (EncodedBit.Word.swapStep_get_right_word
      (mutableYPort auxEncoding width).word
      (outputYPort auxEncoding width).word
      (fun index => mutableY_outputY_wire_ne auxEncoding width index index)
      (mutableYPort auxEncoding width).pairwise_ne
      (outputYPort auxEncoding width).pairwise_ne
      (fun left right => mutableY_outputY_wire_ne auxEncoding width left right)
      state) bit
    rw [hbit]
    exact (mutableYPort auxEncoding width).get_bit bit state
  apply Prod.ext
  · exact hcontrol
  · apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact Prod.ext hmutableX hmutableY
        · exact Prod.ext hconstant (Prod.ext houtputX houtputY)
      · exact haux
    · exact hcontrolWork

/-- Swapping the two public point ports leaves the constant port and framing
fields untouched. -/
lemma swapMutableOutputStep_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (control : Bool) (mutable constant output : PointWords width)
    (aux : Aux) (controlWork : Bool) :
    swapMutableOutputStep auxEncoding width
        (control, (((mutable, (constant, output)), aux), controlWork)) =
      (control, (((output, (constant, mutable)), aux), controlWork)) := by
  let input : RawRegisters Aux width :=
    (control, (((mutable, (constant, output)), aux), controlWork))
  let outputState : RawRegisters Aux width :=
    (control, (((output, (constant, mutable)), aux), controlWork))
  change swapMutableOutputStep auxEncoding width input = outputState
  unfold swapMutableOutputStep swapMutableOutputGates
  rw [EncodedBit.GateSpec.stepList_append]
  change EncodedBit.Word.swapStep
      (mutableYPort auxEncoding width).word
      (outputYPort auxEncoding width).word
      (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit)
      (EncodedBit.Word.swapStep
        (mutableXPort auxEncoding width).word
        (outputXPort auxEncoding width).word
        (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit) input) =
      outputState
  rw [swapMutableOutputXStep_at auxEncoding width control mutable constant output
    aux controlWork]
  simpa [outputState] using
    swapMutableOutputYStep_at auxEncoding width control
      (output.1, mutable.2) constant (mutable.1, output.2) aux controlWork

/-- The mutable/output swap maps the corresponding encoded basis ket. -/
lemma swapMutableOutputProgram_applyNormalized_encoded_ket_at {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (control : Bool) (mutable constant output : PointWords width)
    (aux : Aux) (controlWork : Bool) :
    (swapMutableOutputProgram auxEncoding width).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
            ((rawEncoding auxEncoding width).encode
              (control, (((mutable, (constant, output)), aux), controlWork))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (rawEncoding auxEncoding width).width).basisEquiv.symm
          ((rawEncoding auxEncoding width).encode
            (control, (((output, (constant, mutable)), aux), controlWork)))) := by
  rw [(swapMutableOutput_realizes (environment := environment) auxEncoding width).apply_encoded_ket]
  rw [swapMutableOutputStep_at auxEncoding width control mutable constant output
    aux controlWork]

lemma loadConstantGates_length_le {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    (loadConstantGates auxEncoding width constant).length ≤ 2 * width := by
  simp only [loadConstantGates, List.length_append,
    EncodedBit.Word.xorConstantGates, List.length_map]
  have hx := EncodedBit.Word.constantOneIndices_length_le constant.1
  have hy := EncodedBit.Word.constantOneIndices_length_le constant.2
  omega

lemma replaceConstantGates_length_le {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    (replaceConstantGates auxEncoding width source target).length ≤
      2 * width := by
  simp only [replaceConstantGates, List.length_append,
    EncodedBit.Word.xorConstantGates, List.length_map]
  have hx := EncodedBit.Word.constantOneIndices_length_le
    (wordDelta source.1 target.1)
  have hy := EncodedBit.Word.constantOneIndices_length_le
    (wordDelta source.2 target.2)
  omega

lemma unloadConstantGates_length_le {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    (unloadConstantGates auxEncoding width constant).length ≤ 2 * width := by
  simpa [unloadConstantGates] using
    loadConstantGates_length_le auxEncoding width constant

lemma swapMutableOutputGates_length {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    (swapMutableOutputGates auxEncoding width).length = 6 * width := by
  rw [swapMutableOutputGates, List.length_append,
    EncodedBit.Word.swapGates_length, EncodedBit.Word.swapGates_length]
  omega

/-- Loading a classical point contributes no source CNOT gates. -/
lemma loadConstantGates_cnotMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ((loadConstantGates auxEncoding width constant).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  rw [loadConstantGates, List.map_append, List.sum_append,
    EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum,
    EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum, Nat.zero_add]

/-- Loading a classical point contributes no source Toffoli gates. -/
lemma loadConstantGates_toffoliMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ((loadConstantGates auxEncoding width constant).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  rw [loadConstantGates, List.map_append, List.sum_append,
    EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum,
    EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum, Nat.zero_add]

/-- Replacing one classical point contributes no source CNOT gates. -/
lemma replaceConstantGates_cnotMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    ((replaceConstantGates auxEncoding width source target).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  rw [replaceConstantGates, List.map_append, List.sum_append,
    EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum,
    EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum, Nat.zero_add]

/-- Replacing one classical point contributes no source Toffoli gates. -/
lemma replaceConstantGates_toffoliMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (source target : PointWords width) :
    ((replaceConstantGates auxEncoding width source target).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  rw [replaceConstantGates, List.map_append, List.sum_append,
    EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum,
    EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum, Nat.zero_add]

/-- Unloading a classical point contributes no source CNOT gates. -/
lemma unloadConstantGates_cnotMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ((unloadConstantGates auxEncoding width constant).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simpa only [unloadConstantGates, List.map_reverse, List.sum_reverse] using
    loadConstantGates_cnotMultiplicity_sum auxEncoding width constant

/-- Unloading a classical point contributes no source Toffoli gates. -/
lemma unloadConstantGates_toffoliMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat)
    (constant : PointWords width) :
    ((unloadConstantGates auxEncoding width constant).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simpa only [unloadConstantGates, List.map_reverse, List.sum_reverse] using
    loadConstantGates_toffoliMultiplicity_sum auxEncoding width constant

/-- The mutable/output point swap contributes exactly six source CNOTs per
field bit. -/
lemma swapMutableOutputGates_cnotMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    ((swapMutableOutputGates auxEncoding width).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 6 * width := by
  unfold swapMutableOutputGates
  rw [List.map_append, List.sum_append]
  have hx := EncodedBit.Word.swapGates_cnotMultiplicity_sum
    (mutableXPort auxEncoding width).word
    (outputXPort auxEncoding width).word
    (fun bit => mutableX_outputX_wire_ne auxEncoding width bit bit)
  have hy := EncodedBit.Word.swapGates_cnotMultiplicity_sum
    (mutableYPort auxEncoding width).word
    (outputYPort auxEncoding width).word
    (fun bit => mutableY_outputY_wire_ne auxEncoding width bit bit)
  omega

/-- The mutable/output point swap contributes no source Toffoli gates. -/
lemma swapMutableOutputGates_toffoliMultiplicity_sum {Aux : Type}
    (auxEncoding : BinaryLabelEncoding Aux) (width : Nat) :
    ((swapMutableOutputGates auxEncoding width).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  have hlength := swapMutableOutputGates_length auxEncoding width
  have hcnot := swapMutableOutputGates_cnotMultiplicity_sum auxEncoding width
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (swapMutableOutputGates auxEncoding width)
  omega

end

end PortFrame
end PointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
