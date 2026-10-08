/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Generic.Pipeline
import all QuantumAlg.Components.Encoded.BitGates.Word.ZeroTest

/-!
# Exceptional-cleanup physical layout

This leaf extends the clean generic point-addition pipeline by a small,
explicit selector carrier.  The selector carrier is deliberately a product
field, so every cleanup wire is physically separated from the pipeline before
any exceptional branch semantics are introduced.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace ExceptionalCleanup
namespace Layout

open Nat.FixedWidth

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

/-- The cleanup suffix consists of an `f`-bit zero-test chain, its predicate
bit, one clean controlled-branch work bit, and two clean source padding bits. -/
abbrev SelectorRegisters : Type :=
  Nat.FixedWidth.Word params.width × (Bool × (Bool × (Bool × Bool)))

/-- The complete cleanup carrier keeps the generic pipeline as its left product
field and puts all exceptional-cleanup storage in the right field. -/
abbrev RawRegisters : Type :=
  Pipeline.RawRegisters × SelectorRegisters

/-- Binary encoding of the field-width zero-test workspace. -/
def zeroWorkEncoding : BinaryLabelEncoding (Nat.FixedWidth.Word params.width) :=
  BinaryLabelEncoding.finIdentity params.width

/-- Encoding of the two clean source-padding bits. -/
def paddingEncoding : BinaryLabelEncoding (Bool × Bool) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool

/-- Encoding of the branch work bit paired with both padding bits. -/
def branchTailEncoding : BinaryLabelEncoding (Bool × (Bool × Bool)) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool paddingEncoding

/-- Encoding of the selector bit and the complete branch-control suffix. -/
def selectorTailEncoding : BinaryLabelEncoding
    (Bool × (Bool × (Bool × Bool))) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool branchTailEncoding

/-- Exact product encoding of the cleanup suffix. -/
def selectorEncoding : BinaryLabelEncoding SelectorRegisters :=
  BinaryLabelEncoding.prod zeroWorkEncoding selectorTailEncoding

/-- The selector suffix has one zero-test work wire per field bit and four
additional Boolean wires. -/
theorem selectorEncoding_width_exact :
    selectorEncoding.width = params.width + 4 := by
  simp [selectorEncoding, zeroWorkEncoding, selectorTailEncoding,
    branchTailEncoding, paddingEncoding]

/-- Encoding for the exceptional-cleanup carrier. -/
def rawEncoding : BinaryLabelEncoding RawRegisters :=
  BinaryLabelEncoding.prod Pipeline.rawEncoding selectorEncoding

/-- Exact width of the direct generic pipeline and selector suffix. -/
theorem rawEncoding_width_exact :
    rawEncoding.width =
      Arithmetic.ModularInversion.physicalWidthFor params.width +
        20 * params.width + 13 := by
  change Pipeline.rawEncoding.width + selectorEncoding.width =
    Arithmetic.ModularInversion.physicalWidthFor params.width +
      20 * params.width + 13
  rw [Pipeline.rawEncoding_width_exact, selectorEncoding_width_exact]
  omega

/-- The all-clean exceptional-cleanup suffix. -/
def blankSelectorRegisters : SelectorRegisters :=
  (0, (false, (false, (false, false))))

/-- Public clean boundary of the exceptional-cleanup translation. -/
def selectedBoundaryRegisters
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) : RawRegisters :=
  (Pipeline.translationBoundaryRegisters control mutable constant output,
    (0, (selector, (false, (false, false)))))

/-- Public clean boundary with a false exceptional selector. -/
def translationBoundaryRegisters
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width) : RawRegisters :=
  selectedBoundaryRegisters control mutable constant output false

/-- Input-independent blank boundary for the extended carrier. -/
def blank : RawRegisters :=
  translationBoundaryRegisters false
      (PointAddition.PortFrame.zeroPoint params.width)
      (PointAddition.PortFrame.zeroPoint params.width)
      (PointAddition.PortFrame.zeroPoint params.width)

/-- Lift a physical bit of the generic pipeline to the extended carrier. -/
def liftPipelineBit (bit : EncodedBit Pipeline.rawEncoding) :
    EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodLeftBit Pipeline.rawEncoding selectorEncoding bit

/-- Leading public translation control on the complete carrier. -/
def controlBit : EncodedBit rawEncoding :=
  liftPipelineBit Pipeline.controlBit

/-- Clean work bit used only by the final public-control decomposition. -/
def controlWorkBit : EncodedBit rawEncoding :=
  liftPipelineBit Pipeline.controlWorkBit

@[simp] theorem controlBit_get_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    controlBit.get
        (selectedBoundaryRegisters control mutable constant output selector) =
      control :=
  rfl

@[simp] theorem controlWorkBit_get_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    controlWorkBit.get
        (selectedBoundaryRegisters control mutable constant output selector) =
      false :=
  rfl

/-- The public control and its decomposition work bit remain distinct after
lifting into the exceptional-cleanup carrier. -/
theorem controlBit_wire_ne_controlWorkBit :
    controlBit.wire ≠ controlWorkBit.wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  exact Pipeline.controlBit_wire_ne_controlWorkBit

/-- Lift a literal generic-pipeline gate list to the left product field. -/
def liftPipelineGates
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    List (EncodedBit.GateSpec rawEncoding) :=
  gates.map (EncodedBit.GateSpec.prodLeft selectorEncoding)

/-- Extending the carrier changes only wire addresses, not the ordered
primitive-event trace. -/
theorem liftPipelineGates_map_event
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    (liftPipelineGates gates).map (EncodedBit.GateSpec.event .empty) =
      gates.map (EncodedBit.GateSpec.event .empty) := by
  unfold liftPipelineGates
  exact EncodedBit.GateSpec.map_event_prodLeft selectorEncoding gates

/-- Extending the carrier preserves the literal primitive-leaf count. -/
theorem liftPipelineGates_length
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    (liftPipelineGates gates).length = gates.length := by
  unfold liftPipelineGates
  exact EncodedBit.GateSpec.length_prodLeft selectorEncoding gates

/-- Extending the carrier preserves the exact X coordinate. -/
theorem liftPipelineGates_xMultiplicity_sum
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    ((liftPipelineGates gates).map
      EncodedBit.GateSpec.xMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.xMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    (liftPipelineGates_map_event gates)

/-- Extending the carrier preserves the exact CNOT coordinate. -/
theorem liftPipelineGates_cnotMultiplicity_sum
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    ((liftPipelineGates gates).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (liftPipelineGates_map_event gates)

/-- Extending the carrier preserves the exact Toffoli coordinate. -/
theorem liftPipelineGates_toffoliMultiplicity_sum
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    ((liftPipelineGates gates).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (liftPipelineGates_map_event gates)

/-- A lifted pipeline list acts only on the pipeline component and preserves
the exceptional-cleanup suffix verbatim. -/
theorem stepList_liftPipelineGates
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding))
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (liftPipelineGates gates) state =
      (EncodedBit.GateSpec.stepList gates state.1, state.2) := by
  simpa only [liftPipelineGates, rawEncoding] using
    EncodedBit.GateSpec.stepList_prodLeft selectorEncoding gates state

/-- Lifting a pipeline bit and a pipeline gate list preserves any
bit-disjointness proof from the pipeline carrier. -/
theorem liftPipelineGates_bitDisjoint_liftPipelineBit
    (observed : EncodedBit Pipeline.rawEncoding)
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding))
    (hdisjoint : ∀ gate, gate ∈ gates →
      EncodedBit.GateSpec.bitDisjoint observed gate) :
    ∀ gate, gate ∈ liftPipelineGates gates →
      EncodedBit.GateSpec.bitDisjoint (liftPipelineBit observed) gate := by
  intro gate hgate
  rcases List.mem_map.mp hgate with ⟨source, hsource, rfl⟩
  exact EncodedBit.GateSpec.bitDisjoint_prodLeft_of_bitDisjoint
    selectorEncoding observed source (hdisjoint source hsource)

/-- Lift a generic-pipeline word to the extended carrier. -/
def liftPipelineWord {wordWidth : Nat}
    (word : EncodedBit.Word Pipeline.rawEncoding wordWidth) :
    EncodedBit.Word rawEncoding wordWidth where
  bit := fun bit => liftPipelineBit (word.bit bit)

/-- Mutable X-coordinate port before the exceptional suffix is added. -/
def pipelineMutableXPort : Arithmetic.BlockBank.WordPort
    Pipeline.rawEncoding params.width :=
  PointAddition.PortFrame.liftPublicPort Pipeline.auxEncoding params.width
    (PointAddition.PortFrame.mutableXPublicPort params.width)

/-- Mutable Y-coordinate port before the exceptional suffix is added. -/
def pipelineMutableYPort : Arithmetic.BlockBank.WordPort
    Pipeline.rawEncoding params.width :=
  PointAddition.PortFrame.liftPublicPort Pipeline.auxEncoding params.width
    (PointAddition.PortFrame.mutableYPublicPort params.width)

/-- Clean-output X-coordinate port before the exceptional suffix is added. -/
def pipelineOutputXPort : Arithmetic.BlockBank.WordPort
    Pipeline.rawEncoding params.width :=
  PointAddition.PortFrame.liftPublicPort Pipeline.auxEncoding params.width
    (PointAddition.PortFrame.outputXPublicPort params.width)

/-- Clean-output Y-coordinate port before the exceptional suffix is added. -/
def pipelineOutputYPort : Arithmetic.BlockBank.WordPort
    Pipeline.rawEncoding params.width :=
  PointAddition.PortFrame.liftPublicPort Pipeline.auxEncoding params.width
    (PointAddition.PortFrame.outputYPublicPort params.width)

/-- Mutable X-coordinate port on the complete exceptional-cleanup carrier. -/
def mutableXPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  (pipelineMutableXPort (params := params)).prodLeft selectorEncoding

/-- Mutable Y-coordinate port on the complete exceptional-cleanup carrier. -/
def mutableYPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  (pipelineMutableYPort (params := params)).prodLeft selectorEncoding

/-- Clean-output X-coordinate port on the complete exceptional-cleanup carrier. -/
def outputXPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  (pipelineOutputXPort (params := params)).prodLeft selectorEncoding

/-- Clean-output Y-coordinate port on the complete exceptional-cleanup carrier. -/
def outputYPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  (pipelineOutputYPort (params := params)).prodLeft selectorEncoding

/-- Mutable input X-coordinate on the extended carrier. -/
def mutableXWord : EncodedBit.Word rawEncoding params.width :=
  (mutableXPort (params := params)).word

/-- Mutable input Y-coordinate on the extended carrier. -/
def mutableYWord : EncodedBit.Word rawEncoding params.width :=
  (mutableYPort (params := params)).word

/-- Clean output X-coordinate on the extended carrier. -/
def outputXWord : EncodedBit.Word rawEncoding params.width :=
  (outputXPort (params := params)).word

/-- Clean output Y-coordinate on the extended carrier. -/
def outputYWord : EncodedBit.Word rawEncoding params.width :=
  (outputYPort (params := params)).word

@[simp] theorem mutableXPort_read_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    (mutableXPort (params := params)).read
        (selectedBoundaryRegisters control mutable constant output selector) =
      mutable.1 :=
  rfl

@[simp] theorem outputXPort_read_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    (outputXPort (params := params)).read
        (selectedBoundaryRegisters control mutable constant output selector) =
      output.1 :=
  rfl

@[simp] theorem outputYPort_read_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    (outputYPort (params := params)).read
        (selectedBoundaryRegisters control mutable constant output selector) =
      output.2 :=
  rfl

@[simp] theorem outputXPort_set_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) (value : Nat.FixedWidth.Word params.width) :
    (outputXPort (params := params)).set
        (selectedBoundaryRegisters control mutable constant output selector)
        value =
      selectedBoundaryRegisters control mutable constant (value, output.2)
        selector :=
  rfl

@[simp] theorem outputYPort_set_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) (value : Nat.FixedWidth.Word params.width) :
    (outputYPort (params := params)).set
        (selectedBoundaryRegisters control mutable constant output selector)
        value =
      selectedBoundaryRegisters control mutable constant (output.1, value)
        selector :=
  rfl

/-- Lift a selector-suffix bit through the outer pipeline product. -/
def liftSelectorBit (bit : EncodedBit selectorEncoding) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodRightBit Pipeline.rawEncoding selectorEncoding bit

/-- Lift a zero-test work bit into the selector suffix. -/
def liftZeroWorkLocal (bit : EncodedBit zeroWorkEncoding) :
    EncodedBit selectorEncoding :=
  BinaryLabelEncoding.prodLeftBit zeroWorkEncoding selectorTailEncoding bit

/-- Lift a non-work selector-tail bit into the selector suffix. -/
def liftSelectorTailLocal (bit : EncodedBit selectorTailEncoding) :
    EncodedBit selectorEncoding :=
  BinaryLabelEncoding.prodRightBit zeroWorkEncoding selectorTailEncoding bit

/-- Lift a selector-tail bit all the way to the extended carrier. -/
def liftTailBit (bit : EncodedBit selectorTailEncoding) : EncodedBit rawEncoding :=
  liftSelectorBit (liftSelectorTailLocal bit)

/-- The `i`th raw zero-test work bit. -/
def zeroWorkRawBit (bit : Fin params.width) : EncodedBit zeroWorkEncoding :=
  BinaryLabelEncoding.finIdentityBit params.width
    (WireAddress.littleEndianWire bit)

/-- The `i`th clean zero-test work bit on the extended carrier. -/
def zeroWorkBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  liftSelectorBit (liftZeroWorkLocal (zeroWorkRawBit bit))

/-- Complete word of clean zero-test work bits. -/
def zeroWorkWord : EncodedBit.Word rawEncoding params.width where
  bit := zeroWorkBit

/-- Local selector predicate bit, before the zero-work prefix is added. -/
def selectorTailBit : EncodedBit selectorTailEncoding :=
  BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool branchTailEncoding
    BinaryLabelEncoding.boolBit

/-- Local clean branch-control decomposition bit. -/
def branchControlTailBit : EncodedBit selectorTailEncoding :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool branchTailEncoding
    (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool paddingEncoding
      BinaryLabelEncoding.boolBit)

/-- First local clean source-padding bit. -/
def paddingLeftTailBit : EncodedBit selectorTailEncoding :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool branchTailEncoding
    (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool paddingEncoding
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- Second local clean source-padding bit. -/
def paddingRightTailBit : EncodedBit selectorTailEncoding :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool branchTailEncoding
    (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool paddingEncoding
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- Zero-test predicate bit on the extended carrier. -/
def selectorBit : EncodedBit rawEncoding :=
  liftTailBit selectorTailBit

/-- Clean work bit for a future controlled exceptional branch. -/
def branchControlWorkBit : EncodedBit rawEncoding :=
  liftTailBit branchControlTailBit

/-- First clean source-padding bit on the extended carrier. -/
def paddingLeftBit : EncodedBit rawEncoding :=
  liftTailBit paddingLeftTailBit

/-- Second clean source-padding bit on the extended carrier. -/
def paddingRightBit : EncodedBit rawEncoding :=
  liftTailBit paddingRightTailBit

@[simp] theorem selectorBit_get_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    selectorBit.get
        (selectedBoundaryRegisters control mutable constant output selector) =
      selector :=
  rfl

@[simp] theorem zeroWorkBit_get_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) (work : Fin params.width) :
    (zeroWorkBit work).get
        (selectedBoundaryRegisters control mutable constant output selector) =
      false := by
  change (BinaryLabelEncoding.finIdentityBit params.width
      (WireAddress.littleEndianWire work)).get
        (0 : Nat.FixedWidth.Word params.width) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero params.width
    (WireAddress.littleEndianWire work)

@[simp] theorem selectorBit_flip_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    selectorBit.flip
        (selectedBoundaryRegisters control mutable constant output selector) =
      selectedBoundaryRegisters control mutable constant output (!selector) :=
  rfl

@[simp] theorem branchControlWorkBit_get_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    branchControlWorkBit.get
        (selectedBoundaryRegisters control mutable constant output selector) =
      false :=
  rfl

@[simp] theorem paddingLeftBit_get_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    paddingLeftBit.get
        (selectedBoundaryRegisters control mutable constant output selector) =
      false :=
  rfl

@[simp] theorem paddingRightBit_get_selectedBoundary
    (control : Bool)
    (mutable constant output :
      PointAddition.PortFrame.PointWords params.width)
    (selector : Bool) :
    paddingRightBit.get
        (selectedBoundaryRegisters control mutable constant output selector) =
      false :=
  rfl

private theorem liftPipelineBit_wire_ne_liftSelectorBit
    (left : EncodedBit Pipeline.rawEncoding)
    (right : EncodedBit selectorEncoding) :
    (liftPipelineBit left).wire ≠ (liftSelectorBit right).wire := by
  simpa only [liftPipelineBit, liftSelectorBit, rawEncoding] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      Pipeline.rawEncoding selectorEncoding right left).symm

/-- Every selector-suffix bit is disjoint from the lifted public control. -/
theorem liftSelectorBit_wire_ne_controlBit
    (bit : EncodedBit selectorEncoding) :
    (liftSelectorBit bit).wire ≠ controlBit.wire :=
  (liftPipelineBit_wire_ne_liftSelectorBit Pipeline.controlBit bit).symm

/-- Every selector-suffix bit is disjoint from the lifted outer-control work
bit. -/
theorem liftSelectorBit_wire_ne_controlWorkBit
    (bit : EncodedBit selectorEncoding) :
    (liftSelectorBit bit).wire ≠ controlWorkBit.wire :=
  (liftPipelineBit_wire_ne_liftSelectorBit Pipeline.controlWorkBit bit).symm

/-- Every mutable-X wire is disjoint from the lifted public control. -/
theorem mutableXWord_wire_ne_controlBit (bit : Fin params.width) :
    (mutableXWord.bit bit).wire ≠ controlBit.wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  simpa only [pipelineMutableXPort,
    PointAddition.PortFrame.liftPublicPort_word_bit, Pipeline.controlBit,
    Pipeline.rawEncoding] using
    PointAddition.PortFrame.liftPublicBit_wire_ne_controlBit
      Pipeline.auxEncoding params.width
      ((PointAddition.PortFrame.mutableXPublicPort params.width).word.bit bit)

/-- Every mutable-X wire is disjoint from the lifted outer-control work bit. -/
theorem mutableXWord_wire_ne_controlWorkBit (bit : Fin params.width) :
    (mutableXWord.bit bit).wire ≠ controlWorkBit.wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  simpa only [pipelineMutableXPort,
    PointAddition.PortFrame.liftPublicPort_word_bit,
    Pipeline.controlWorkBit, Pipeline.rawEncoding] using
    PointAddition.PortFrame.liftPublicBit_wire_ne_controlWorkBit
      Pipeline.auxEncoding params.width
      ((PointAddition.PortFrame.mutableXPublicPort params.width).word.bit bit)

/-- Every output-X wire is disjoint from the lifted public control. -/
theorem outputXWord_wire_ne_controlBit (bit : Fin params.width) :
    (outputXWord.bit bit).wire ≠ controlBit.wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  simpa only [pipelineOutputXPort,
    PointAddition.PortFrame.liftPublicPort_word_bit, Pipeline.controlBit,
    Pipeline.rawEncoding] using
    PointAddition.PortFrame.liftPublicBit_wire_ne_controlBit
      Pipeline.auxEncoding params.width
      ((PointAddition.PortFrame.outputXPublicPort params.width).word.bit bit)

/-- Every output-X wire is disjoint from the lifted outer-control work bit. -/
theorem outputXWord_wire_ne_controlWorkBit (bit : Fin params.width) :
    (outputXWord.bit bit).wire ≠ controlWorkBit.wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  simpa only [pipelineOutputXPort,
    PointAddition.PortFrame.liftPublicPort_word_bit,
    Pipeline.controlWorkBit, Pipeline.rawEncoding] using
    PointAddition.PortFrame.liftPublicBit_wire_ne_controlWorkBit
      Pipeline.auxEncoding params.width
      ((PointAddition.PortFrame.outputXPublicPort params.width).word.bit bit)

/-- Every output-Y wire is disjoint from the lifted public control. -/
theorem outputYWord_wire_ne_controlBit (bit : Fin params.width) :
    (outputYWord.bit bit).wire ≠ controlBit.wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  simpa only [pipelineOutputYPort,
    PointAddition.PortFrame.liftPublicPort_word_bit, Pipeline.controlBit,
    Pipeline.rawEncoding] using
    PointAddition.PortFrame.liftPublicBit_wire_ne_controlBit
      Pipeline.auxEncoding params.width
      ((PointAddition.PortFrame.outputYPublicPort params.width).word.bit bit)

/-- Every output-Y wire is disjoint from the lifted outer-control work bit. -/
theorem outputYWord_wire_ne_controlWorkBit (bit : Fin params.width) :
    (outputYWord.bit bit).wire ≠ controlWorkBit.wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  simpa only [pipelineOutputYPort,
    PointAddition.PortFrame.liftPublicPort_word_bit,
    Pipeline.controlWorkBit, Pipeline.rawEncoding] using
    PointAddition.PortFrame.liftPublicBit_wire_ne_controlWorkBit
      Pipeline.auxEncoding params.width
      ((PointAddition.PortFrame.outputYPublicPort params.width).word.bit bit)

theorem zeroWorkBit_wire_ne_controlBit (work : Fin params.width) :
    (zeroWorkBit work).wire ≠ controlBit.wire := by
  exact liftSelectorBit_wire_ne_controlBit
    (liftZeroWorkLocal (zeroWorkRawBit work))

theorem zeroWorkBit_wire_ne_controlWorkBit (work : Fin params.width) :
    (zeroWorkBit work).wire ≠ controlWorkBit.wire := by
  exact liftSelectorBit_wire_ne_controlWorkBit
    (liftZeroWorkLocal (zeroWorkRawBit work))

theorem selectorBit_wire_ne_controlBit :
    selectorBit.wire ≠ controlBit.wire := by
  exact liftSelectorBit_wire_ne_controlBit
    (liftSelectorTailLocal selectorTailBit)

theorem selectorBit_wire_ne_controlWorkBit :
    selectorBit.wire ≠ controlWorkBit.wire := by
  exact liftSelectorBit_wire_ne_controlWorkBit
    (liftSelectorTailLocal selectorTailBit)

theorem branchControlWorkBit_wire_ne_controlBit :
    branchControlWorkBit.wire ≠ controlBit.wire := by
  exact liftSelectorBit_wire_ne_controlBit
    (liftSelectorTailLocal branchControlTailBit)

theorem branchControlWorkBit_wire_ne_controlWorkBit :
    branchControlWorkBit.wire ≠ controlWorkBit.wire := by
  exact liftSelectorBit_wire_ne_controlWorkBit
    (liftSelectorTailLocal branchControlTailBit)

theorem paddingLeftBit_wire_ne_controlBit :
    paddingLeftBit.wire ≠ controlBit.wire := by
  exact liftSelectorBit_wire_ne_controlBit
    (liftSelectorTailLocal paddingLeftTailBit)

theorem paddingLeftBit_wire_ne_controlWorkBit :
    paddingLeftBit.wire ≠ controlWorkBit.wire := by
  exact liftSelectorBit_wire_ne_controlWorkBit
    (liftSelectorTailLocal paddingLeftTailBit)

theorem paddingRightBit_wire_ne_controlBit :
    paddingRightBit.wire ≠ controlBit.wire := by
  exact liftSelectorBit_wire_ne_controlBit
    (liftSelectorTailLocal paddingRightTailBit)

theorem paddingRightBit_wire_ne_controlWorkBit :
    paddingRightBit.wire ≠ controlWorkBit.wire := by
  exact liftSelectorBit_wire_ne_controlWorkBit
    (liftSelectorTailLocal paddingRightTailBit)

/-- Every lifted pipeline wire is disjoint from the selector predicate. -/
theorem liftPipelineBit_wire_ne_selectorBit
    (bit : EncodedBit Pipeline.rawEncoding) :
    (liftPipelineBit bit).wire ≠ selectorBit.wire := by
  exact liftPipelineBit_wire_ne_liftSelectorBit bit
    (liftSelectorTailLocal selectorTailBit)

/-- Every lifted pipeline wire is disjoint from the branch-control work bit. -/
theorem liftPipelineBit_wire_ne_branchControlWorkBit
    (bit : EncodedBit Pipeline.rawEncoding) :
    (liftPipelineBit bit).wire ≠ branchControlWorkBit.wire := by
  exact liftPipelineBit_wire_ne_liftSelectorBit bit
    (liftSelectorTailLocal branchControlTailBit)

/-- The selector predicate is disjoint from each lifted output-X wire. -/
theorem selectorBit_wire_ne_outputXWord (bit : Fin params.width) :
    selectorBit.wire ≠ (outputXWord.bit bit).wire := by
  exact (liftPipelineBit_wire_ne_selectorBit
    ((pipelineOutputXPort (params := params)).word.bit bit)).symm

/-- The selector predicate is disjoint from each lifted output-Y wire. -/
theorem selectorBit_wire_ne_outputYWord (bit : Fin params.width) :
    selectorBit.wire ≠ (outputYWord.bit bit).wire := by
  exact (liftPipelineBit_wire_ne_selectorBit
    ((pipelineOutputYPort (params := params)).word.bit bit)).symm

/-- The selector predicate is disjoint from every gate lifted from the generic
pipeline. -/
theorem liftPipelineGates_bitDisjoint_selectorBit
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    ∀ gate, gate ∈ liftPipelineGates gates →
      EncodedBit.GateSpec.bitDisjoint selectorBit gate := by
  intro gate hgate
  rcases List.mem_map.mp hgate with ⟨source, hsource, rfl⟩
  exact EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit
    Pipeline.rawEncoding selectorEncoding
    (liftSelectorTailLocal selectorTailBit) source

/-- The branch-control work bit is disjoint from every gate lifted from the
generic pipeline. -/
theorem liftPipelineGates_bitDisjoint_branchControlWorkBit
    (gates : List (EncodedBit.GateSpec Pipeline.rawEncoding)) :
    ∀ gate, gate ∈ liftPipelineGates gates →
      EncodedBit.GateSpec.bitDisjoint branchControlWorkBit gate := by
  intro gate hgate
  rcases List.mem_map.mp hgate with ⟨source, hsource, rfl⟩
  exact EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit
    Pipeline.rawEncoding selectorEncoding
    (liftSelectorTailLocal branchControlTailBit) source

private theorem liftSelectorBit_wire_ne {left right : EncodedBit selectorEncoding}
    (hwire : left.wire ≠ right.wire) :
    (liftSelectorBit left).wire ≠ (liftSelectorBit right).wire := by
  simpa only [liftSelectorBit, rawEncoding] using
    EncodedBit.GateSpec.prodRightWire_ne Pipeline.rawEncoding hwire

private theorem liftZeroWorkLocal_wire_ne_liftSelectorTailLocal
    (work : EncodedBit zeroWorkEncoding)
    (tail : EncodedBit selectorTailEncoding) :
    (liftZeroWorkLocal work).wire ≠ (liftSelectorTailLocal tail).wire := by
  simpa only [liftZeroWorkLocal, liftSelectorTailLocal, selectorEncoding] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      zeroWorkEncoding selectorTailEncoding tail work).symm

private theorem liftTailBit_wire_ne
    {left right : EncodedBit selectorTailEncoding}
    (hwire : left.wire ≠ right.wire) :
    (liftTailBit left).wire ≠ (liftTailBit right).wire := by
  apply liftSelectorBit_wire_ne
  exact EncodedBit.GateSpec.prodRightWire_ne zeroWorkEncoding hwire

private theorem zeroWorkRawBit_pairwise_ne (left right : Fin params.width)
    (hne : left ≠ right) :
    (zeroWorkRawBit left).wire ≠ (zeroWorkRawBit right).wire := by
  simpa [zeroWorkRawBit, zeroWorkEncoding, PointAddition.PortFrame.fixedWord,
    PointAddition.PortFrame.wordEncoding] using
    PointAddition.PortFrame.fixedWord_pairwise_ne params.width left right hne

/-- The clean zero-test work word uses distinct physical wires. -/
theorem zeroWorkWord_pairwise_ne (left right : Fin params.width)
    (hne : left ≠ right) :
    (zeroWorkWord.bit left).wire ≠ (zeroWorkWord.bit right).wire := by
  apply liftSelectorBit_wire_ne
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorTailEncoding
  exact zeroWorkRawBit_pairwise_ne left right hne

/-- The lifted mutable X-coordinate retains the port's pairwise wire
separation. -/
theorem mutableXWord_pairwise_ne (left right : Fin params.width)
    (hne : left ≠ right) :
    (mutableXWord.bit left).wire ≠ (mutableXWord.bit right).wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne selectorEncoding
  exact (PointAddition.PortFrame.mutableXPort
    Pipeline.auxEncoding params.width).pairwise_ne left right hne

private theorem mutableXWord_wire_ne_liftSelectorBit (bit : Fin params.width)
    (selector : EncodedBit selectorEncoding) :
    (mutableXWord.bit bit).wire ≠ (liftSelectorBit selector).wire := by
  exact liftPipelineBit_wire_ne_liftSelectorBit
    ((PointAddition.PortFrame.mutableXPort
      Pipeline.auxEncoding params.width).word.bit bit) selector

private theorem zeroWorkBit_wire_ne_liftTailBit (work : Fin params.width)
    (tail : EncodedBit selectorTailEncoding) :
    (zeroWorkBit work).wire ≠ (liftTailBit tail).wire := by
  apply liftSelectorBit_wire_ne
  exact liftZeroWorkLocal_wire_ne_liftSelectorTailLocal
    (zeroWorkRawBit work) tail

private theorem mutableXWord_wire_ne_zeroWorkBit
    (source work : Fin params.width) :
    (mutableXWord.bit source).wire ≠ (zeroWorkBit work).wire := by
  exact mutableXWord_wire_ne_liftSelectorBit source
    (liftZeroWorkLocal (zeroWorkRawBit work))

private theorem mutableXWord_wire_ne_selectorBit (source : Fin params.width) :
    (mutableXWord.bit source).wire ≠ selectorBit.wire := by
  exact mutableXWord_wire_ne_liftSelectorBit source
    (liftSelectorTailLocal selectorTailBit)

private theorem mutableXWord_wire_ne_paddingLeftBit
    (source : Fin params.width) :
    (mutableXWord.bit source).wire ≠ paddingLeftBit.wire := by
  exact mutableXWord_wire_ne_liftSelectorBit source
    (liftSelectorTailLocal paddingLeftTailBit)

private theorem mutableXWord_wire_ne_paddingRightBit
    (source : Fin params.width) :
    (mutableXWord.bit source).wire ≠ paddingRightBit.wire := by
  exact mutableXWord_wire_ne_liftSelectorBit source
    (liftSelectorTailLocal paddingRightTailBit)

omit params in
private theorem selectorTailBit_wire_ne_branchTailBit
    (branch : EncodedBit branchTailEncoding) :
    selectorTailBit.wire ≠
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        branchTailEncoding branch).wire := by
  simpa only [selectorTailBit, selectorTailEncoding] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      BinaryLabelEncoding.bool branchTailEncoding branch
      BinaryLabelEncoding.boolBit).symm

omit params in
private theorem branchControlTailBit_wire_ne_paddingBit
    (padding : EncodedBit paddingEncoding) :
    branchControlTailBit.wire ≠
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        branchTailEncoding
        (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
          paddingEncoding padding)).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  simpa only [branchControlTailBit, branchTailEncoding] using
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      BinaryLabelEncoding.bool paddingEncoding padding
      BinaryLabelEncoding.boolBit).symm

omit params in
private theorem paddingLeftTailBit_wire_ne_paddingRightTailBit :
    paddingLeftTailBit.wire ≠ paddingRightTailBit.wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    BinaryLabelEncoding.bool BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit BinaryLabelEncoding.boolBit).symm

/-- The selector predicate and branch-control work bit are distinct. -/
theorem selectorBit_wire_ne_branchControlWorkBit :
    selectorBit.wire ≠ branchControlWorkBit.wire := by
  apply liftTailBit_wire_ne
  simpa only [branchControlTailBit] using
    selectorTailBit_wire_ne_branchTailBit
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool paddingEncoding
        BinaryLabelEncoding.boolBit)

/-- The selector predicate is disjoint from the first clean padding bit. -/
theorem selectorBit_wire_ne_paddingLeftBit :
    selectorBit.wire ≠ paddingLeftBit.wire := by
  apply liftTailBit_wire_ne
  simpa only [paddingLeftTailBit] using
    selectorTailBit_wire_ne_branchTailBit
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool paddingEncoding
        (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
          BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- The selector predicate is disjoint from the second clean padding bit. -/
theorem selectorBit_wire_ne_paddingRightBit :
    selectorBit.wire ≠ paddingRightBit.wire := by
  apply liftTailBit_wire_ne
  simpa only [paddingRightTailBit] using
    selectorTailBit_wire_ne_branchTailBit
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool paddingEncoding
        (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
          BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- The branch-control work bit is disjoint from the first clean padding bit. -/
theorem branchControlWorkBit_wire_ne_paddingLeftBit :
    branchControlWorkBit.wire ≠ paddingLeftBit.wire := by
  apply liftTailBit_wire_ne
  simpa only [paddingLeftTailBit] using
    branchControlTailBit_wire_ne_paddingBit
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)

/-- The branch-control work bit is disjoint from the second clean padding bit. -/
theorem branchControlWorkBit_wire_ne_paddingRightBit :
    branchControlWorkBit.wire ≠ paddingRightBit.wire := by
  apply liftTailBit_wire_ne
  simpa only [paddingRightTailBit] using
    branchControlTailBit_wire_ne_paddingBit
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)

/-- The two clean source padding bits use distinct wires. -/
theorem paddingLeftBit_wire_ne_paddingRightBit :
    paddingLeftBit.wire ≠ paddingRightBit.wire := by
  exact liftTailBit_wire_ne paddingLeftTailBit_wire_ne_paddingRightTailBit

private theorem paddingLeftBit_wire_ne_zeroWorkBit (work : Fin params.width) :
    paddingLeftBit.wire ≠ (zeroWorkBit work).wire := by
  exact (zeroWorkBit_wire_ne_liftTailBit work paddingLeftTailBit).symm

private theorem paddingRightBit_wire_ne_zeroWorkBit (work : Fin params.width) :
    paddingRightBit.wire ≠ (zeroWorkBit work).wire := by
  exact (zeroWorkBit_wire_ne_liftTailBit work paddingRightTailBit).symm

/-- A width-`f+2` zero-test source consisting of mutable X followed by two
dedicated clean padding wires. -/
def sourceWord : EncodedBit.Word rawEncoding (params.width + 2) where
  bit := fun bit =>
    Fin.lastCases paddingRightBit
      (fun lower =>
        Fin.lastCases paddingLeftBit
          (fun mutable => mutableXWord.bit mutable) lower) bit

/-- Every widened comparison-source wire is disjoint from the public
translation control. -/
theorem sourceWord_wire_ne_controlBit
    (source : Fin (params.width + 2)) :
    (sourceWord.bit source).wire ≠ controlBit.wire := by
  revert source
  refine Fin.lastCases ?_ ?_
  · simpa [sourceWord] using paddingRightBit_wire_ne_controlBit
  · intro lower
    refine Fin.lastCases ?_ ?_ lower
    · simpa [sourceWord] using paddingLeftBit_wire_ne_controlBit
    · intro mutable
      simpa [sourceWord] using mutableXWord_wire_ne_controlBit mutable

/-- Every widened comparison-source wire is disjoint from the outer-control
work bit. -/
theorem sourceWord_wire_ne_controlWorkBit
    (source : Fin (params.width + 2)) :
    (sourceWord.bit source).wire ≠ controlWorkBit.wire := by
  revert source
  refine Fin.lastCases ?_ ?_
  · simpa [sourceWord] using paddingRightBit_wire_ne_controlWorkBit
  · intro lower
    refine Fin.lastCases ?_ ?_ lower
    · simpa [sourceWord] using paddingLeftBit_wire_ne_controlWorkBit
    · intro mutable
      simpa [sourceWord] using mutableXWord_wire_ne_controlWorkBit mutable

/-- Distinct source indices select distinct physical wires. -/
theorem sourceWord_pairwise_ne (left right : Fin (params.width + 2))
    (hne : left ≠ right) :
    (sourceWord.bit left).wire ≠ (sourceWord.bit right).wire := by
  revert hne
  revert right
  refine Fin.lastCases ?_ ?_ left
  · intro right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · intro hsame _
      exact hsame rfl
    · intro right hne
      revert hne
      refine Fin.lastCases ?_ ?_ right
      · intro _
        simpa [sourceWord] using paddingLeftBit_wire_ne_paddingRightBit.symm
      · intro mutable _
        simpa [sourceWord] using
          (mutableXWord_wire_ne_paddingRightBit mutable).symm
  · intro lower right hne
    revert hne
    refine Fin.lastCases ?_ ?_ lower
    · intro hne
      revert hne
      refine Fin.lastCases ?_ ?_ right
      · intro _
        simpa [sourceWord] using paddingLeftBit_wire_ne_paddingRightBit
      · intro right hne
        revert hne
        refine Fin.lastCases ?_ ?_ right
        · intro hsame _
          exact hsame rfl
        · intro mutable _
          simpa [sourceWord] using
            (mutableXWord_wire_ne_paddingLeftBit mutable).symm
    · intro mutable hne
      revert hne
      refine Fin.lastCases ?_ ?_ right
      · intro _
        simpa [sourceWord] using mutableXWord_wire_ne_paddingRightBit mutable
      · intro right hne
        revert hne
        refine Fin.lastCases ?_ ?_ right
        · intro _
          simpa [sourceWord] using
            mutableXWord_wire_ne_paddingLeftBit mutable
        · intro other hne
          have hmutable : mutable ≠ other := by
            intro heq
            apply hne
            subst other
            rfl
          simpa [sourceWord] using
            mutableXWord_pairwise_ne mutable other hmutable

/-- Every source wire is disjoint from the selector predicate output. -/
theorem sourceWord_wire_ne_selectorBit (bit : Fin (params.width + 2)) :
    (sourceWord.bit bit).wire ≠ selectorBit.wire := by
  refine Fin.lastCases ?_ ?_ bit
  · simpa [sourceWord] using selectorBit_wire_ne_paddingRightBit.symm
  · intro lower
    refine Fin.lastCases ?_ ?_ lower
    · simpa [sourceWord] using selectorBit_wire_ne_paddingLeftBit.symm
    · intro mutable
      simpa [sourceWord] using mutableXWord_wire_ne_selectorBit mutable

/-- Every source wire is disjoint from every clean zero-test work wire. -/
theorem sourceWord_wire_ne_zeroWorkWord
    (source : Fin (params.width + 2)) (work : Fin params.width) :
    (sourceWord.bit source).wire ≠ (zeroWorkWord.bit work).wire := by
  refine Fin.lastCases ?_ ?_ source
  · simpa [sourceWord, zeroWorkWord] using
      paddingRightBit_wire_ne_zeroWorkBit work
  · intro lower
    refine Fin.lastCases ?_ ?_ lower
    · simpa [sourceWord, zeroWorkWord] using
        paddingLeftBit_wire_ne_zeroWorkBit work
    · intro mutable
      simpa [sourceWord, zeroWorkWord] using
        mutableXWord_wire_ne_zeroWorkBit mutable work

/-- Every zero-test work wire is disjoint from the selector predicate output. -/
theorem zeroWorkWord_wire_ne_selectorBit (work : Fin params.width) :
    (zeroWorkWord.bit work).wire ≠ selectorBit.wire := by
  exact zeroWorkBit_wire_ne_liftTailBit work selectorTailBit

/-- Fully instantiated physical layout for a clean zero test of mutable X
with two dedicated high padding wires. -/
def mutableXZeroTestLayout :
    EncodedBit.Word.ZeroTestLayout (encoding := rawEncoding) params.width where
  source := sourceWord
  output := selectorBit
  work := zeroWorkWord
  source_source_ne := sourceWord_pairwise_ne
  source_output_ne := sourceWord_wire_ne_selectorBit
  source_work_ne := sourceWord_wire_ne_zeroWorkWord
  work_work_ne := zeroWorkWord_pairwise_ne
  work_output_ne := zeroWorkWord_wire_ne_selectorBit

end

end Layout
end ExceptionalCleanup
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
