/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
import all QuantumAlg.Components.Encoded.BitGates.Realization
public import Mathlib.Algebra.Ring.Parity
-- Intentional exception: machine-readable source-owner markers keep full module names on one line.
set_option linter.style.longLine false

/-!
# Width-parameterized variable modular multiplication

This module fixes one common carrier for variable modular multiplication at
an arbitrary positive width and odd positive modulus. It keeps the existing VBE in-place
multiplication workspace intact, adds a preserved multiplier and an external
accumulator, and exposes three actual primitive programs: a word swap, a
copy/unload xor, and one clean-work-controlled modular-add stage.  The
width-indexed fold and the source-doubling schedule are assembled separately.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic
namespace VariableModularMul

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Parameters needed by the fixed-schedule shift-and-add circuit. -/
public class Parameters where
  /-- Number of bits in each canonical residue word. -/
  width : Nat
  /-- Positive widths provide a final multiplier-bit index. -/
  widthPos : 0 < width
  /-- Odd positive modulus stored in one width-sized word. -/
  modulus : PlainAdder.Word width
  /-- The modulus is nontrivial, so unit inputs have positive canonical
  representatives and logarithmic inversion counters cannot wrap. -/
  one_lt_modulus : 1 < modulus.val
  /-- Positivity is needed by the canonical `ZMod` endpoint. -/
  modulusPos : 0 < modulus.val
  /-- Oddness makes multiplication by two reversible modulo the modulus. -/
  modulusOdd : Odd modulus.val

variable [params : Parameters]

/-- The stored modulus fits in its declared word width. -/
lemma modulus_lt_capacity : params.modulus.val < 2 ^ params.width :=
  ZMod.val_lt params.modulus

/-- One externally visible data word. -/
abbrev Word : Type :=
  PlainAdder.Word params.width

/-- The canonical binary encoding of one external residue word. -/
abbrev wordEncoding : BinaryLabelEncoding Word :=
  PlainAdder.Schedule.PowerOfTwo.wordEncoding params.width

/-- The already concrete VBE in-place multiplication carrier.  Its
`multiplicand` field is used as the variable source, while its arithmetic
field supplies the clean VBE workspace. -/
abbrev InPlaceRegisters : Type :=
  MAU.Multiplication.VBECircuit.Registers params.width

/-- The existing faithful `5 * width + 4` VBE in-place layout. -/
abbrev inPlaceEncoding : BinaryLabelEncoding InPlaceRegisters :=
  MAU.Multiplication.VBECircuit.encoding params.width

/-- The in-place carrier together with the single work bit used only by the
clean-work control decomposition. -/
abbrev InPlaceWithWork : Type :=
  InPlaceRegisters × Bool

/-- Binary layout of the in-place carrier followed by the clean control work
bit. -/
abbrev inPlaceWithWorkEncoding : BinaryLabelEncoding InPlaceWithWork :=
  BinaryLabelEncoding.prod inPlaceEncoding BinaryLabelEncoding.bool

/-- The external accumulator followed by the in-place arithmetic suffix. -/
abbrev AccumulatorSuffix : Type :=
  Word × InPlaceWithWork

/-- Binary layout of the external accumulator and arithmetic suffix. -/
abbrev accumulatorSuffixEncoding : BinaryLabelEncoding AccumulatorSuffix :=
  BinaryLabelEncoding.prod wordEncoding inPlaceWithWorkEncoding

/-- Complete common carrier for the first variable-multiplication slice.
The multiplier is never a target of the primitive programs in this module;
each selected bit is only a control for its modular-add stage. -/
structure Registers where
  /-- Preserved variable multiplier whose bits select modular-add stages. -/
  multiplier : Word
  /-- External low-width accumulator exchanged with the VBE target on demand. -/
  accumulator : Word
  /-- Reused concrete VBE in-place source and its clean arithmetic workspace. -/
  inPlace : InPlaceRegisters
  /-- One clean bit shared by every controlled modular-add decomposition. -/
  work : Bool
deriving DecidableEq

/-- Semantic data carried by the clean variable-multiplication layout.  The
multiplier and multiplicand are preserved, while the accumulator receives the
product at the full schedule endpoint. -/
structure Data where
  /-- The variable multiplier whose bits control the selected-add stages. -/
  multiplier : ZMod params.modulus.val
  /-- The variable multiplicand stored in the reused VBE carrier. -/
  multiplicand : ZMod params.modulus.val
  /-- The external modular accumulator. -/
  accumulator : ZMod params.modulus.val
deriving DecidableEq

namespace Data

/-- The semantic result of accumulating the complete variable product. -/
def addProduct (x : Data) : Data where
  multiplier := x.multiplier
  multiplicand := x.multiplicand
  accumulator := x.accumulator + x.multiplier * x.multiplicand

/-- The semantic result of one multiplier-bit-selected accumulation. -/
def addSelected (bit : Fin params.width) (x : Data) : Data where
  multiplier := x.multiplier
  multiplicand := x.multiplicand
  accumulator := x.accumulator +
    if x.multiplier.val.testBit bit.val then x.multiplicand else 0

/-- The semantic source update implemented by one shift/reduce doubling
block. -/
def doubleMultiplicand (x : Data) : Data where
  multiplier := x.multiplier
  multiplicand := 2 * x.multiplicand
  accumulator := x.accumulator

end Data

/-- Raw physical field order: multiplier, accumulator, in-place workspace,
then the clean control-work bit. -/
abbrev RawRegisters : Type :=
  Word × AccumulatorSuffix

/-- Fieldwise equivalence between the named carrier and its physical product
layout. -/
def registersEquiv : Registers ≃ RawRegisters where
  toFun := fun x => (x.multiplier, (x.accumulator, (x.inPlace, x.work)))
  invFun := fun x =>
    { multiplier := x.1
      accumulator := x.2.1
      inPlace := x.2.2.1
      work := x.2.2.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    rintro ⟨multiplier, accumulator, inPlace, work⟩
    rfl

/-- Raw binary encoding before restoring the named fields. -/
def rawEncoding : BinaryLabelEncoding RawRegisters :=
  BinaryLabelEncoding.prod wordEncoding accumulatorSuffixEncoding

/-- Faithful named binary encoding of the complete common carrier. -/
abbrev encoding : BinaryLabelEncoding Registers :=
  rawEncoding.relabel registersEquiv

/-- Relabeling only restores field names and leaves the physical width fixed. -/
@[simp] lemma encoding_width : encoding.width = rawEncoding.width :=
  rfl

set_option exponentiation.threshold 2048 in
/-- Canonical clean physical placement of variable multiplication data.  The
active VBE source, target, arithmetic work, and shared control-work bit start
clean; the modulus is parked in the standard VBE location. -/
def cleanRegisters (x : Data) : Registers where
  multiplier := (x.multiplier.val : Word)
  accumulator := (x.accumulator.val : Word)
  inPlace := MAU.Multiplication.Accumulate.VBECircuit.workspaceState
    params.width (x.multiplicand.val : Word) 0
    (params.modulus.val : Word)
    (MAU.Addition.VBECircuit.widenWord params.width (0 : Word)) false
  work := false

/-! ## Encoded-bit views -/

/-- One external multiplier bit in the raw physical layout. -/
def rawMultiplierBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodLeftBit wordEncoding accumulatorSuffixEncoding
    (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit)

/-- One external accumulator bit in the raw physical layout. -/
def rawAccumulatorBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodRightBit wordEncoding accumulatorSuffixEncoding
    (BinaryLabelEncoding.prodLeftBit wordEncoding inPlaceWithWorkEncoding
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit))

/-- Lift an addressed bit of the existing VBE in-place layout into the common
raw physical carrier. -/
def rawInPlaceBit (bit : EncodedBit inPlaceEncoding) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodRightBit wordEncoding accumulatorSuffixEncoding
    (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
      (BinaryLabelEncoding.prodLeftBit inPlaceEncoding BinaryLabelEncoding.bool
        bit))

/-- The common clean work bit in the raw physical layout. -/
def rawWorkBit : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodRightBit wordEncoding accumulatorSuffixEncoding
    (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
      (BinaryLabelEncoding.prodRightBit inPlaceEncoding BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

/-- Embed an ordinary low source index in the one-bit-wider VBE active-source
word. -/
def lowSourceIndex (bit : Fin params.width) :
    Fin (MAU.Addition.VBECircuit.AdderWidth params.width) :=
  ⟨bit.val, Nat.lt_succ_of_lt bit.isLt⟩

/-- One bit of the variable source already stored in the in-place VBE carrier. -/
def rawInPlaceMultiplicandBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  rawInPlaceBit
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit params.width bit)

/-- One low bit of the VBE active source used to load and unload the in-place
variable source.  Its dedicated high overflow bit is left clean. -/
def rawInPlaceActiveSourceBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  rawInPlaceBit
    ((MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord params.width).bit
      (lowSourceIndex bit))

/-- One low bit of the VBE arithmetic target that exchanges with the external
accumulator. -/
def rawInPlaceAccumulatorBit (bit : Fin params.width) : EncodedBit rawEncoding :=
  rawInPlaceBit (MAU.Multiplication.VBECircuit.accumulatorBit params.width bit)

/-- External multiplier word view. -/
def rawMultiplierWord : EncodedBit.Word rawEncoding params.width where
  bit := rawMultiplierBit

/-- External accumulator word view. -/
def rawAccumulatorWord : EncodedBit.Word rawEncoding params.width where
  bit := rawAccumulatorBit

/-- Variable source word inside the reused VBE in-place carrier. -/
def rawInPlaceMultiplicandWord : EncodedBit.Word rawEncoding params.width where
  bit := rawInPlaceMultiplicandBit

/-- Low VBE active-source word used for xor copy and unload. -/
def rawInPlaceActiveSourceWord : EncodedBit.Word rawEncoding params.width where
  bit := rawInPlaceActiveSourceBit

/-- Low VBE target word used for the external accumulator swap. -/
def rawInPlaceAccumulatorWord : EncodedBit.Word rawEncoding params.width where
  bit := rawInPlaceAccumulatorBit

/-- Named multiplier-bit view. -/
def multiplierBit (bit : Fin params.width) : EncodedBit encoding :=
  (rawMultiplierBit bit).relabel registersEquiv

/-- Named external-accumulator-bit view. -/
def accumulatorBit (bit : Fin params.width) : EncodedBit encoding :=
  (rawAccumulatorBit bit).relabel registersEquiv

/-- Named in-place multiplicand-bit view. -/
def inPlaceMultiplicandBit (bit : Fin params.width) : EncodedBit encoding :=
  (rawInPlaceMultiplicandBit bit).relabel registersEquiv

/-- Named low active-source-bit view. -/
def inPlaceActiveSourceBit (bit : Fin params.width) : EncodedBit encoding :=
  (rawInPlaceActiveSourceBit bit).relabel registersEquiv

/-- Named low VBE target-bit view. -/
def inPlaceAccumulatorBit (bit : Fin params.width) : EncodedBit encoding :=
  (rawInPlaceAccumulatorBit bit).relabel registersEquiv

/-- Named clean control-work-bit view. -/
def workBit : EncodedBit encoding :=
  rawWorkBit.relabel registersEquiv

/-- Distinct named multiplier bits occupy distinct physical wires. -/
lemma multiplierBit_pairwise_ne
    (left right : Fin params.width) (h : left ≠ right) :
    (multiplierBit left).wire ≠ (multiplierBit right).wire := by
  have hbase :
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width left).wire ≠
        (PlainAdder.Schedule.PowerOfTwo.wordBit params.width right).wire := by
    change
      (WireAddress.littleEndianWire left : Fin params.width) ≠
        WireAddress.littleEndianWire right
    intro hw
    apply h
    exact WireAddress.bitIndex_injective hw
  have hraw := EncodedBit.GateSpec.prodLeftWire_ne
    accumulatorSuffixEncoding hbase
  intro hw
  apply hraw
  apply Fin.ext
  simpa only [multiplierBit, rawMultiplierBit, EncodedBit.relabel] using
    congrArg Fin.val hw

/-- Distinct named in-place multiplicand bits occupy distinct physical wires. -/
lemma inPlaceMultiplicandBit_pairwise_ne
    (left right : Fin params.width) (h : left ≠ right) :
    (inPlaceMultiplicandBit left).wire ≠
      (inPlaceMultiplicandBit right).wire := by
  have hbase :=
    MAU.Multiplication.VBECircuit.multiplicand_pairwise_ne
      params.width left right h
  have hwork := EncodedBit.GateSpec.prodLeftWire_ne
    BinaryLabelEncoding.bool hbase
  have hsuffix := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hwork
  have hraw := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hsuffix
  intro hw
  apply hraw
  apply Fin.ext
  simpa only [inPlaceMultiplicandBit, rawInPlaceMultiplicandBit,
    rawInPlaceBit, accumulatorSuffixEncoding, inPlaceWithWorkEncoding,
    inPlaceEncoding,
    MAU.Multiplication.VBECircuit.multiplicandWord,
    MAU.Multiplication.Accumulate.VBECircuit.multiplicandWord,
    EncodedBit.relabel] using congrArg Fin.val hw

/-- Every named multiplier bit is physically separated from every named
in-place multiplicand bit. -/
lemma multiplierBit_inPlaceMultiplicandBit_ne
    (left right : Fin params.width) :
    (multiplierBit left).wire ≠ (inPlaceMultiplicandBit right).wire := by
  have hraw :
      (rawMultiplierBit left).wire ≠
        (rawInPlaceMultiplicandBit right).wire := by
    exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      wordEncoding accumulatorSuffixEncoding
      (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
        (BinaryLabelEncoding.prodLeftBit
          inPlaceEncoding BinaryLabelEncoding.bool
          (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
            params.width right)))
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width left)).symm
  intro hw
  apply hraw
  apply Fin.ext
  simpa only [multiplierBit, inPlaceMultiplicandBit, EncodedBit.relabel] using
    congrArg Fin.val hw

@[simp] lemma rawMultiplierBit_get (bit : Fin params.width) (x : RawRegisters) :
    (rawMultiplierBit bit).get x = x.1.val.testBit bit.val := by
  change (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit).get x.1 = _
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get params.width bit x.1

@[simp] lemma rawWorkBit_get (x : RawRegisters) :
    rawWorkBit.get x = x.2.2.2 :=
  rfl

lemma rawAccumulatorBit_get (bit : Fin params.width) (x : RawRegisters) :
    (rawAccumulatorBit bit).get x = x.2.1.val.testBit bit.val := by
  change (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit).get x.2.1 = _
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get params.width bit x.2.1

lemma rawInPlaceMultiplicandBit_get
    (bit : Fin params.width) (x : RawRegisters) :
    (rawInPlaceMultiplicandBit bit).get x =
      x.2.2.1.multiplicand.val.testBit bit.val := by
  change (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
    params.width bit).get x.2.2.1 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit_get
    params.width bit x.2.2.1

@[simp] lemma inPlaceMultiplicandBit_get
    (bit : Fin params.width) (x : Registers) :
    (inPlaceMultiplicandBit bit).get x =
      x.inPlace.multiplicand.val.testBit bit.val := by
  change
    (rawInPlaceMultiplicandBit bit).get (registersEquiv x) = _
  exact rawInPlaceMultiplicandBit_get bit (registersEquiv x)

set_option exponentiation.threshold 2048 in
private lemma rawInPlaceActiveSourceBit_get
    (bit : Fin params.width) (x : RawRegisters) :
    (rawInPlaceActiveSourceBit bit).get x =
      x.2.2.1.arithmetic.activeSource.val.testBit bit.val := by
  change (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit
    params.width (lowSourceIndex bit)).get x.2.2.1 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get
    params.width (lowSourceIndex bit) x.2.2.1

set_option exponentiation.threshold 2048 in
private lemma rawInPlaceAccumulatorBit_get
    (bit : Fin params.width) (x : RawRegisters) :
    (rawInPlaceAccumulatorBit bit).get x =
      x.2.2.1.arithmetic.target.val.testBit bit.val := by
  change (MAU.Multiplication.VBECircuit.accumulatorBit params.width bit).get
    x.2.2.1 = _
  exact MAU.Multiplication.VBECircuit.accumulatorBit_get params.width bit x.2.2.1

set_option exponentiation.threshold 2048 in
private lemma rawInPlaceActiveSourceHighBit_get (x : RawRegisters) :
    (rawInPlaceBit
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
        (Fin.last params.width))).get x =
      x.2.2.1.arithmetic.activeSource.val.testBit params.width := by
  change (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
    (Fin.last params.width)).get x.2.2.1 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get
    params.width (Fin.last params.width) x.2.2.1

set_option exponentiation.threshold 2048 in
private lemma rawInPlaceAccumulatorHighBit_get (x : RawRegisters) :
    (rawInPlaceBit
      (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
        (Fin.last params.width))).get x =
      x.2.2.1.arithmetic.target.val.testBit params.width := by
  change (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
    (Fin.last params.width)).get x.2.2.1 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.targetBit_get
    params.width (Fin.last params.width) x.2.2.1

private lemma rawInPlaceBit_wire_ne
    {left right : EncodedBit inPlaceEncoding} (h : left.wire ≠ right.wire) :
    (rawInPlaceBit left).wire ≠ (rawInPlaceBit right).wire := by
  have hwithWork :=
    EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool h
  have hsuffix := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hwithWork
  have hraw := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hsuffix
  simpa only [rawInPlaceBit, rawEncoding, accumulatorSuffixEncoding] using hraw

lemma rawAccumulator_pairwise_ne :
    ∀ i j : Fin params.width, i ≠ j →
      (rawAccumulatorBit i).wire ≠ (rawAccumulatorBit j).wire := by
  intro i j hij
  have hbase :
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width i).wire ≠
        (PlainAdder.Schedule.PowerOfTwo.wordBit params.width j).wire := by
    change (WireAddress.littleEndianWire i : Fin params.width) ≠
      WireAddress.littleEndianWire j
    intro hwire
    apply hij
    exact WireAddress.bitIndex_injective hwire
  have hsuffix :=
    EncodedBit.GateSpec.prodLeftWire_ne inPlaceWithWorkEncoding hbase
  have hraw := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hsuffix
  simpa only [rawAccumulatorBit, rawEncoding, accumulatorSuffixEncoding] using hraw

private lemma rawAccumulator_inPlaceBit_ne
    (accumulatorBit : Fin params.width) (inPlaceBit : EncodedBit inPlaceEncoding) :
    (rawAccumulatorBit accumulatorBit).wire ≠ (rawInPlaceBit inPlaceBit).wire := by
  have hinner :
      (BinaryLabelEncoding.prodLeftBit wordEncoding inPlaceWithWorkEncoding
        (PlainAdder.Schedule.PowerOfTwo.wordBit params.width accumulatorBit)).wire ≠
        (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
          (BinaryLabelEncoding.prodLeftBit inPlaceEncoding BinaryLabelEncoding.bool
            inPlaceBit)).wire :=
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      wordEncoding inPlaceWithWorkEncoding
      (BinaryLabelEncoding.prodLeftBit inPlaceEncoding BinaryLabelEncoding.bool
        inPlaceBit)
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width accumulatorBit)).symm
  have hraw := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hinner
  simpa only [rawAccumulatorBit, rawInPlaceBit, rawEncoding,
    accumulatorSuffixEncoding] using hraw

private lemma rawInPlaceAccumulator_pairwise_ne :
    ∀ i j : Fin params.width, i ≠ j →
      (rawInPlaceAccumulatorBit i).wire ≠
        (rawInPlaceAccumulatorBit j).wire := by
  intro i j hij
  exact rawInPlaceBit_wire_ne
    (MAU.Multiplication.VBECircuit.accumulator_pairwise_ne params.width i j hij)

private lemma rawAccumulator_inPlaceAccumulator_cross_ne :
    ∀ accumulatorBit targetBit : Fin params.width,
      (rawAccumulatorBit accumulatorBit).wire ≠
        (rawInPlaceAccumulatorBit targetBit).wire := by
  intro accumulatorBit targetBit
  exact rawAccumulator_inPlaceBit_ne accumulatorBit
    (MAU.Multiplication.VBECircuit.accumulatorBit params.width targetBit)

private lemma rawInPlaceActiveSource_pairwise_ne :
    ∀ i j : Fin params.width, i ≠ j →
      (rawInPlaceActiveSourceBit i).wire ≠
        (rawInPlaceActiveSourceBit j).wire := by
  intro i j hij
  have hindices : lowSourceIndex i ≠ lowSourceIndex j := by
    intro hindices
    apply hij
    apply Fin.ext
    simpa only [lowSourceIndex] using
      congrArg
        (fun k : Fin (MAU.Addition.VBECircuit.AdderWidth params.width) => k.val)
        hindices
  exact rawInPlaceBit_wire_ne
    (MAU.Multiplication.Accumulate.VBECircuit.activeSource_pairwise_ne
      params.width (lowSourceIndex i) (lowSourceIndex j) hindices)

private lemma rawInPlaceMultiplicand_activeSource_cross_ne :
    ∀ multiplicandBit sourceBit : Fin params.width,
      (rawInPlaceMultiplicandBit multiplicandBit).wire ≠
        (rawInPlaceActiveSourceBit sourceBit).wire := by
  intro multiplicandBit sourceBit
  exact rawInPlaceBit_wire_ne
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      params.width multiplicandBit (lowSourceIndex sourceBit))

private lemma rawInPlaceActiveSource_activeHigh_ne (bit : Fin params.width) :
    (rawInPlaceActiveSourceBit bit).wire ≠
      (rawInPlaceBit
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
          (Fin.last params.width))).wire := by
  have hindex : lowSourceIndex bit ≠ Fin.last params.width := by
    intro hindex
    have hvalue := congrArg Fin.val hindex
    have hbit := bit.isLt
    simp only [lowSourceIndex, Fin.val_last] at hvalue
    omega
  exact rawInPlaceBit_wire_ne
    (MAU.Multiplication.Accumulate.VBECircuit.activeSource_pairwise_ne
      params.width (lowSourceIndex bit) (Fin.last params.width) hindex)

private lemma rawInPlaceAccumulator_targetHigh_ne (bit : Fin params.width) :
    (rawInPlaceAccumulatorBit bit).wire ≠
      (rawInPlaceBit
        (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
          (Fin.last params.width))).wire := by
  apply rawInPlaceBit_wire_ne
  apply MAU.Multiplication.VBECircuit.liftArithmeticBit_ne params.width
  exact MAU.Multiplication.VBECircuit.accumulator_targetHigh_ne params.width bit

/-! ## Actual routing primitives -/

/-- The external accumulator wire is distinct from its counterpart in the
low VBE target word. -/
lemma rawAccumulator_inPlaceAccumulator_ne (bit : Fin params.width) :
    (rawAccumulatorBit bit).wire ≠ (rawInPlaceAccumulatorBit bit).wire := by
  have hinner :
      (BinaryLabelEncoding.prodLeftBit wordEncoding inPlaceWithWorkEncoding
        (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit)).wire ≠
        (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
          (BinaryLabelEncoding.prodLeftBit inPlaceEncoding
            BinaryLabelEncoding.bool
            (MAU.Multiplication.VBECircuit.accumulatorBit params.width bit))).wire :=
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      wordEncoding inPlaceWithWorkEncoding
      (BinaryLabelEncoding.prodLeftBit inPlaceEncoding BinaryLabelEncoding.bool
        (MAU.Multiplication.VBECircuit.accumulatorBit params.width bit))
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit)).symm
  unfold rawAccumulatorBit rawInPlaceAccumulatorBit rawInPlaceBit
  unfold rawEncoding accumulatorSuffixEncoding
  exact EncodedBit.GateSpec.prodRightWire_ne wordEncoding hinner

/-- The in-place source word is wire-disjoint from the low active VBE source
word into which it is copied or unloaded. -/
lemma rawInPlaceMultiplicand_activeSource_ne (bit : Fin params.width) :
    (rawInPlaceMultiplicandBit bit).wire ≠
      (rawInPlaceActiveSourceBit bit).wire := by
  have hinPlace :=
    MAU.Multiplication.Accumulate.VBECircuit.multiplicand_activeSource_ne
      params.width bit (lowSourceIndex bit)
  have hwithWork :=
    EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool hinPlace
  have hsuffix :=
    EncodedBit.GateSpec.prodRightWire_ne wordEncoding hwithWork
  have hraw :=
    EncodedBit.GateSpec.prodRightWire_ne wordEncoding hsuffix
  unfold rawInPlaceMultiplicandBit rawInPlaceActiveSourceBit rawInPlaceBit
  unfold rawEncoding accumulatorSuffixEncoding
  exact hraw

/-- Actual three-CNOT-per-bit exchange of the external accumulator with the
low VBE target word. -/
def accumulatorSwapGates : List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.swapGates rawAccumulatorWord rawInPlaceAccumulatorWord
    rawAccumulator_inPlaceAccumulator_ne

/-- Circuit compiled from the literal external-accumulator exchange list. -/
def accumulatorSwapCircuit : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty accumulatorSwapGates

/-- Folded semantic action of the external-accumulator exchange. -/
def rawAccumulatorSwapStep : RawRegisters → RawRegisters :=
  EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
    rawAccumulator_inPlaceAccumulator_ne

/-- Named semantic action of the external-accumulator exchange. -/
def accumulatorSwapStep : Registers → Registers :=
  fun x => registersEquiv.symm (rawAccumulatorSwapStep (registersEquiv x))

set_option exponentiation.threshold 2048 in
/-- The physical three-CNOT word swap realizes its displayed named action. -/
lemma accumulatorSwap_realizes :
    UnitaryCircuit.Realizes encoding accumulatorSwapCircuit environment accumulatorSwapStep := by
  exact UnitaryCircuit.Realizes.relabel registersEquiv
    (EncodedBit.Word.swap_realizes (environment := environment) (QubitLayout.canonical _) .empty
      rawAccumulatorWord rawInPlaceAccumulatorWord
      rawAccumulator_inPlaceAccumulator_ne)

/-- Actual bitwise CNOT routing from the stored in-place source into the low
VBE active source.  The same self-inverse program is used for unload. -/
def sourceCopyGates : List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.xorIntoGates rawInPlaceMultiplicandWord
    rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne

/-- Circuit compiled from the literal source-copy list. -/
def sourceCopyCircuit : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty sourceCopyGates

/-- Folded raw action of the source copy/unload xor. -/
def rawSourceCopyStep : RawRegisters → RawRegisters :=
  EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
    rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne

/-- Named action of the source copy xor. -/
def sourceCopyStep : Registers → Registers :=
  fun x => registersEquiv.symm (rawSourceCopyStep (registersEquiv x))

set_option exponentiation.threshold 2048 in
/-- The physical CNOT word-xor realizes the displayed source-copy action. -/
lemma sourceCopy_realizes :
    UnitaryCircuit.Realizes encoding sourceCopyCircuit environment sourceCopyStep := by
  exact UnitaryCircuit.Realizes.relabel registersEquiv
    (EncodedBit.Word.xorInto_realizes (environment := environment) (QubitLayout.canonical _) .empty
      rawInPlaceMultiplicandWord
      rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne)

/-- Unloading uses the same self-inverse CNOT program after its corresponding
controlled modular-add stage has preserved the in-place source. -/
def sourceUnloadGates : List (EncodedBit.GateSpec rawEncoding) :=
  sourceCopyGates

/-- Circuit compiled from the literal source-unload list. -/
def sourceUnloadCircuit : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty sourceUnloadGates

/-- The source-unload step is the same xor action as the source-copy step. -/
def sourceUnloadStep : Registers → Registers :=
  sourceCopyStep

set_option exponentiation.threshold 2048 in
/-- The physical source-unload program realizes its displayed xor action. -/
lemma sourceUnload_realizes :
    UnitaryCircuit.Realizes encoding sourceUnloadCircuit environment sourceUnloadStep :=
  sourceCopy_realizes

/-! ## One selected controlled modular-add stage -/

/-- Lift the width-parameterized modular-add gate list into the existing VBE in-place
carrier, preserving its stored multiplicand word. -/
def inPlaceArithmeticGates : List (EncodedBit.GateSpec inPlaceEncoding) :=
  (MAU.Addition.VBECircuit.modularAddGates
    params.width params.modulus.val).map
    (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticGate params.width)

/-- Lift the existing arithmetic schedule through the common carrier without
allocating another arithmetic workspace. -/
def rawArithmeticGates : List (EncodedBit.GateSpec rawEncoding) :=
  ((inPlaceArithmeticGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodRight wordEncoding)).map
    (EncodedBit.GateSpec.prodRight wordEncoding)

/-- Every external multiplier bit is disjoint from the mechanically lifted
modular-arithmetic schedule. -/
lemma rawMultiplierDisjoint (bit : Fin params.width) :
    ∀ gate, gate ∈ rawArithmeticGates →
      EncodedBit.GateSpec.bitDisjoint (rawMultiplierBit bit) gate := by
  intro gate hgate
  rw [rawArithmeticGates] at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, _hinner, rfl⟩
  change EncodedBit.GateSpec.bitDisjoint
    (BinaryLabelEncoding.prodLeftBit wordEncoding accumulatorSuffixEncoding
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit))
    (EncodedBit.GateSpec.prodRight wordEncoding innerGate)
  exact EncodedBit.GateSpec.bitDisjoint_prodRight_leftBit wordEncoding
    accumulatorSuffixEncoding
    (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit) innerGate

/-- The shared control-work bit is disjoint from every lifted arithmetic gate. -/
lemma rawWorkDisjoint :
    ∀ gate, gate ∈ rawArithmeticGates →
      EncodedBit.GateSpec.bitDisjoint rawWorkBit gate := by
  intro gate hgate
  rw [rawArithmeticGates] at hgate
  rcases List.mem_map.mp hgate with ⟨suffixGate, hsuffix, rfl⟩
  rcases List.mem_map.mp hsuffix with ⟨inPlaceWorkGate, hinPlaceWork, rfl⟩
  rcases List.mem_map.mp hinPlaceWork with ⟨inPlaceGate, _hinPlace, rfl⟩
  have hinPlaceWork :=
    EncodedBit.GateSpec.bitDisjoint_prodLeft_rightBit inPlaceEncoding
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit inPlaceGate
  have hsuffixWork :=
    EncodedBit.GateSpec.bitDisjoint_prodRight_of_bitDisjoint wordEncoding
      (BinaryLabelEncoding.prodRightBit inPlaceEncoding BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit)
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool inPlaceGate)
      hinPlaceWork
  have hrawWork :=
    EncodedBit.GateSpec.bitDisjoint_prodRight_of_bitDisjoint wordEncoding
      (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
        (BinaryLabelEncoding.prodRightBit inPlaceEncoding BinaryLabelEncoding.bool
          BinaryLabelEncoding.boolBit))
      (EncodedBit.GateSpec.prodRight wordEncoding
        (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool inPlaceGate))
      hsuffixWork
  unfold rawWorkBit rawEncoding RawRegisters
  exact hrawWork

/-- Each selected multiplier control is a different physical wire from the
shared control-work bit. -/
lemma rawMultiplierWork_ne (bit : Fin params.width) :
    (rawMultiplierBit bit).wire ≠ rawWorkBit.wire := by
  change
    (BinaryLabelEncoding.prodLeftBit wordEncoding
      (BinaryLabelEncoding.prod wordEncoding inPlaceWithWorkEncoding)
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit)).wire ≠
      (BinaryLabelEncoding.prodRightBit wordEncoding
        (BinaryLabelEncoding.prod wordEncoding inPlaceWithWorkEncoding)
        (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
          (BinaryLabelEncoding.prodRightBit inPlaceEncoding
            BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))).wire
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    wordEncoding (BinaryLabelEncoding.prod wordEncoding inPlaceWithWorkEncoding)
    (BinaryLabelEncoding.prodRightBit wordEncoding inPlaceWithWorkEncoding
      (BinaryLabelEncoding.prodRightBit inPlaceEncoding BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))
    (PlainAdder.Schedule.PowerOfTwo.wordBit params.width bit)).symm

/-- Mechanically controlled X/CNOT/Toffoli schedule for one selected external
multiplier bit.  It acts on the reused VBE arithmetic layout only. -/
def rawStageGates (bit : Fin params.width) : List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (rawMultiplierBit bit) rawWorkBit rawArithmeticGates
    (rawMultiplierDisjoint bit) rawWorkDisjoint (rawMultiplierWork_ne bit)

/-- Actual primitive circuit for one selected variable modular-add stage. -/
def stageCircuit (bit : Fin params.width) : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (rawStageGates bit)

/-- Raw folded action of one selected controlled modular-add stage. -/
def rawStageStep (bit : Fin params.width) : RawRegisters → RawRegisters :=
  EncodedBit.GateSpec.controlledListWithWorkStep
    (rawMultiplierBit bit) rawWorkBit rawArithmeticGates
    (rawMultiplierDisjoint bit) rawWorkDisjoint (rawMultiplierWork_ne bit)

/-- Named folded action of one selected controlled modular-add stage. -/
def stageStep (bit : Fin params.width) : Registers → Registers :=
  fun x => registersEquiv.symm (rawStageStep bit (registersEquiv x))

set_option exponentiation.threshold 2048 in
/-- The actual controlled gate list realizes its named stage action. -/
lemma stage_realizes (bit : Fin params.width) :
    UnitaryCircuit.Realizes encoding (stageCircuit bit) environment (stageStep bit) := by
  exact UnitaryCircuit.Realizes.relabel registersEquiv
    (EncodedBit.GateSpec.controlledListWithWorkWitness (environment := environment)
      (QubitLayout.canonical _) .empty
      (rawMultiplierBit bit) rawWorkBit rawArithmeticGates
      (rawMultiplierDisjoint bit) rawWorkDisjoint (rawMultiplierWork_ne bit))

/-- The unconditional mechanically lifted arithmetic action used when a
selected multiplier bit is true and the shared work bit is clean. -/
def rawUncontrolledAddStep : RawRegisters → RawRegisters :=
  EncodedBit.GateSpec.stepList rawArithmeticGates

/-- The three product lifts around the unconditional stage retain exactly the
public VBE lifted modular-add action on the in-place carrier. -/
private lemma rawUncontrolledAddStep_eq_liftedModularAdd (x : RawRegisters) :
    rawUncontrolledAddStep x =
      (x.1, (x.2.1,
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
          params.width params.modulus.val x.2.2.1, x.2.2.2))) := by
  change EncodedBit.GateSpec.stepList
      (((inPlaceArithmeticGates.map
          (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)).map
        (EncodedBit.GateSpec.prodRight wordEncoding)) x = _
  calc
    EncodedBit.GateSpec.stepList
        (((inPlaceArithmeticGates.map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
          (EncodedBit.GateSpec.prodRight wordEncoding)).map
          (EncodedBit.GateSpec.prodRight wordEncoding)) x =
        (x.1,
          EncodedBit.GateSpec.stepList
            ((inPlaceArithmeticGates.map
                (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
              (EncodedBit.GateSpec.prodRight wordEncoding)) x.2) :=
      EncodedBit.GateSpec.stepList_prodRight wordEncoding
        ((inPlaceArithmeticGates.map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
          (EncodedBit.GateSpec.prodRight wordEncoding)) x
    _ = (x.1, (x.2.1,
        EncodedBit.GateSpec.stepList
          (inPlaceArithmeticGates.map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)) x.2.2)) :=
      congrArg (fun suffix => (x.1, suffix))
        (EncodedBit.GateSpec.stepList_prodRight wordEncoding
          (inPlaceArithmeticGates.map
            (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)) x.2)
    _ = (x.1, (x.2.1,
        (EncodedBit.GateSpec.stepList inPlaceArithmeticGates x.2.2.1,
          x.2.2.2))) :=
      congrArg (fun suffix => (x.1, (x.2.1, suffix)))
        (EncodedBit.GateSpec.stepList_prodLeft BinaryLabelEncoding.bool
          inPlaceArithmeticGates x.2.2)
    _ = _ :=
      congrArg (fun inPlace => (x.1, (x.2.1, (inPlace, x.2.2.2))))
        (by
          change EncodedBit.GateSpec.stepList
              (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates
                params.width params.modulus.val) x.2.2.1 =
              MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
                params.width params.modulus.val x.2.2.1
          exact
            MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep_eq_gateList
              params.width params.modulus.val x.2.2.1)

/-- Named form of the unconditional reused-arithmetic action. -/
def uncontrolledAddStep : Registers → Registers :=
  fun x => registersEquiv.symm (rawUncontrolledAddStep (registersEquiv x))

set_option exponentiation.threshold 2048 in
private def routingRawRegisters
    (multiplier source accumulator active target : Word) : RawRegisters :=
  (multiplier, (accumulator,
    (MAU.Multiplication.Accumulate.VBECircuit.workspaceState
      params.width source active
      (params.modulus.val : Word)
      (MAU.Addition.VBECircuit.widenWord params.width target) false, false)))

private def routingRegisters
    (multiplier source accumulator active target : Word) : Registers :=
  registersEquiv.symm
    (routingRawRegisters multiplier source accumulator active target)

private lemma cleanRegisters_eq_routing (x : Data) :
    cleanRegisters x =
      routingRegisters (x.multiplier.val : Word)
        (x.multiplicand.val : Word) (x.accumulator.val : Word) 0 0 :=
  rfl

/-- A canonical field representative retains its value in the physical
256-bit word. -/
private lemma canonicalWord_val
    (x : ZMod params.modulus.val) :
    ((x.val : Word)).val = x.val := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  apply ZMod.val_natCast_of_lt
  exact (ZMod.val_lt x).trans modulus_lt_capacity

/-- Fieldwise equality for the reusable in-place VBE register structure. -/
private lemma inPlaceRegisters_ext
    (x y : InPlaceRegisters)
    (hmultiplicand : x.multiplicand = y.multiplicand)
    (harithmetic : x.arithmetic = y.arithmetic) :
    x = y := by
  cases x
  cases y
  simp_all

set_option exponentiation.threshold 2048 in
/-- Fieldwise equality for the reusable VBE modular-addition workspace. -/
private lemma additionRegisters_ext
    (x y : MAU.Addition.VBECircuit.Registers params.width)
    (hactiveSource : x.activeSource = y.activeSource)
    (htarget : x.target = y.target)
    (hcarry : x.carry = y.carry)
    (hparkedSource : x.parkedSource = y.parkedSource)
    (hcarryWork : x.carryWork = y.carryWork)
    (hreductionFlag : x.reductionFlag = y.reductionFlag) :
    x = y := by
  cases x
  cases y
  simp_all

set_option exponentiation.threshold 2048 in
/-- The raw accumulator word swap exchanges only the external low word and the
low VBE target word, retaining the clean target overflow bit. -/
private lemma rawAccumulatorSwapStep_routing
    (multiplier source accumulator active target : Word) :
    rawAccumulatorSwapStep
        (routingRawRegisters multiplier source accumulator active target) =
      routingRawRegisters multiplier source target active accumulator := by
  let before : RawRegisters :=
    routingRawRegisters multiplier source accumulator active target
  let step := rawAccumulatorSwapStep
  have hstepRaw :
      step = EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne :=
    rfl
  have hbeforeTarget :
      before.2.2.1.arithmetic.target =
        MAU.Addition.VBECircuit.widenWord params.width target :=
    rfl
  have hbeforeAccumulator : before.2.1 = accumulator :=
    rfl
  have hbeforeParked :
      before.2.2.1.arithmetic.parkedSource =
        (params.modulus.val : Word) :=
    rfl
  have hbeforeActive :
      before.2.2.1.arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord params.width active :=
    rfl
  change step before =
    routingRawRegisters multiplier source target active accumulator
  have hmultiplier : (step before).1 = multiplier := by
    exact EncodedBit.Word.swapStep_preserves_projection
      rawAccumulatorWord rawInPlaceAccumulatorWord
      rawAccumulator_inPlaceAccumulator_ne (fun x => x.1)
      (fun _ _ => rfl) (fun _ _ => rfl) before
  have haccumulator : (step before).2.1 = target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :
        (rawAccumulatorWord.bit bit).get
            (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
              rawAccumulator_inPlaceAccumulator_ne before) =
          (rawInPlaceAccumulatorWord.bit bit).get before :=
      congrFun
      (EncodedBit.Word.swapStep_get_left_word
        rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne rawAccumulator_pairwise_ne
        rawInPlaceAccumulator_pairwise_ne
        rawAccumulator_inPlaceAccumulator_cross_ne before) bit
    have hleftRead (state : RawRegisters) :
        (rawAccumulatorWord.bit bit).get state =
          state.2.1.val.testBit bit.val :=
      rawAccumulatorBit_get bit state
    have hrightRead (state : RawRegisters) :
        (rawInPlaceAccumulatorWord.bit bit).get state =
          state.2.2.1.arithmetic.target.val.testBit bit.val :=
      rawInPlaceAccumulatorBit_get bit state
    have hwidenTarget :
        (MAU.Addition.VBECircuit.widenWord params.width target).val.testBit bit.val =
          target.val.testBit bit.val := by
      rw [MAU.Addition.VBECircuit.widenWord_val]
    calc
      (step before).2.1.val.testBit bit.val =
          (rawAccumulatorWord.bit bit).get (step before) :=
        (hleftRead (step before)).symm
      _ = (rawAccumulatorWord.bit bit).get
            (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
              rawAccumulator_inPlaceAccumulator_ne before) := by
        rw [hstepRaw]
      _ = (rawInPlaceAccumulatorWord.bit bit).get before := hread
      _ = before.2.2.1.arithmetic.target.val.testBit bit.val :=
        hrightRead before
      _ = (MAU.Addition.VBECircuit.widenWord params.width target).val.testBit
            bit.val := by
        rw [hbeforeTarget]
      _ = target.val.testBit bit.val := hwidenTarget
  have hmultiplicand : (step before).2.2.1.multiplicand = source := by
    simpa [step, rawAccumulatorSwapStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using
      EncodedBit.Word.swapStep_preserves_projection
        rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne
        (fun x => x.2.2.1.multiplicand) (fun _ _ => rfl) (fun _ _ => rfl)
        before
  have hactive : (step before).2.2.1.arithmetic.activeSource =
      MAU.Addition.VBECircuit.widenWord params.width active := by
    have hframe :
        (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
          rawAccumulator_inPlaceAccumulator_ne before).2.2.1.arithmetic.activeSource =
          before.2.2.1.arithmetic.activeSource :=
      EncodedBit.Word.swapStep_preserves_projection
      rawAccumulatorWord rawInPlaceAccumulatorWord
      rawAccumulator_inPlaceAccumulator_ne
      (fun x => x.2.2.1.arithmetic.activeSource)
      (fun _ _ => rfl) (fun _ _ => rfl) before
    calc
      (step before).2.2.1.arithmetic.activeSource =
          (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
            rawAccumulator_inPlaceAccumulator_ne before).2.2.1.arithmetic.activeSource := by
        rw [hstepRaw]
      _ = before.2.2.1.arithmetic.activeSource := hframe
      _ = MAU.Addition.VBECircuit.widenWord params.width active := hbeforeActive
  have htarget : (step before).2.2.1.arithmetic.target =
      MAU.Addition.VBECircuit.widenWord params.width accumulator := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    by_cases hlow : bit.val < params.width
    · let low : Fin params.width := ⟨bit.val, hlow⟩
      have hbit :
          bit = lowSourceIndex low := by
        apply Fin.ext
        rfl
      rw [hbit]
      have hread :
          (rawInPlaceAccumulatorWord.bit low).get
              (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
                rawAccumulator_inPlaceAccumulator_ne before) =
            (rawAccumulatorWord.bit low).get before :=
        congrFun
          (EncodedBit.Word.swapStep_get_right_word
            rawAccumulatorWord rawInPlaceAccumulatorWord
            rawAccumulator_inPlaceAccumulator_ne rawAccumulator_pairwise_ne
            rawInPlaceAccumulator_pairwise_ne
            rawAccumulator_inPlaceAccumulator_cross_ne before) low
      have hleftRead (state : RawRegisters) :
          (rawAccumulatorWord.bit low).get state =
            state.2.1.val.testBit low.val :=
        rawAccumulatorBit_get low state
      have hrightRead (state : RawRegisters) :
          (rawInPlaceAccumulatorWord.bit low).get state =
            state.2.2.1.arithmetic.target.val.testBit low.val :=
        rawInPlaceAccumulatorBit_get low state
      have hwidenAccumulator :
          (MAU.Addition.VBECircuit.widenWord params.width accumulator).val.testBit
              low.val = accumulator.val.testBit low.val := by
        rw [MAU.Addition.VBECircuit.widenWord_val]
      calc
        (step before).2.2.1.arithmetic.target.val.testBit low.val =
            (rawInPlaceAccumulatorWord.bit low).get (step before) :=
          (hrightRead (step before)).symm
        _ = (rawInPlaceAccumulatorWord.bit low).get
              (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
                rawAccumulator_inPlaceAccumulator_ne before) := by
          rw [hstepRaw]
        _ = (rawAccumulatorWord.bit low).get before := hread
        _ = before.2.1.val.testBit low.val := hleftRead before
        _ = accumulator.val.testBit low.val := by
          rw [hbeforeAccumulator]
        _ = (MAU.Addition.VBECircuit.widenWord params.width accumulator).val.testBit
              low.val := hwidenAccumulator.symm
    · have hlast :
          bit = (Fin.last params.width :
            Fin (MAU.Addition.VBECircuit.AdderWidth params.width)) := by
        apply Fin.ext
        have hbitLt := bit.isLt
        simp only [MAU.Addition.VBECircuit.AdderWidth, Fin.val_last] at hbitLt ⊢
        omega
      have hlastVal : (Fin.last params.width).val = params.width :=
        rfl
      rw [hlast, hlastVal]
      have hread :
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
              (Fin.last params.width))).get
              (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
                rawAccumulator_inPlaceAccumulator_ne before) =
            (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
                (Fin.last params.width))).get before :=
        EncodedBit.Word.swapStep_get_observed_of_swap_ne
          rawAccumulatorWord rawInPlaceAccumulatorWord
          rawAccumulator_inPlaceAccumulator_ne
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
              (Fin.last params.width)))
          (fun low =>
            rawAccumulator_inPlaceBit_ne low
              (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
                (Fin.last params.width)))
          rawInPlaceAccumulator_targetHigh_ne before
      have htargetHigh : target.val.testBit params.width = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt target)
      have haccumulatorHigh : accumulator.val.testBit params.width = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt accumulator)
      have hrightHigh :
          (MAU.Addition.VBECircuit.widenWord params.width accumulator).val.testBit
              params.width = false := by
        rw [MAU.Addition.VBECircuit.widenWord_val]
        exact haccumulatorHigh
      have hbeforeHigh :
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
              (Fin.last params.width))).get before = false := by
        calc
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
              (Fin.last params.width))).get before =
              before.2.2.1.arithmetic.target.val.testBit params.width :=
            rawInPlaceAccumulatorHighBit_get before
          _ = (MAU.Addition.VBECircuit.widenWord params.width target).val.testBit
                params.width := by
            rw [hbeforeTarget]
          _ = target.val.testBit params.width := by
            rw [MAU.Addition.VBECircuit.widenWord_val]
          _ = false := htargetHigh
      calc
        (step before).2.2.1.arithmetic.target.val.testBit params.width =
            (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
                (Fin.last params.width))).get (step before) :=
          (rawInPlaceAccumulatorHighBit_get (step before)).symm
        _ = (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
                (Fin.last params.width))).get
              (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
                rawAccumulator_inPlaceAccumulator_ne before) := by
          rw [hstepRaw]
        _ = (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width
                (Fin.last params.width))).get before := hread
        _ = false := hbeforeHigh
        _ = (MAU.Addition.VBECircuit.widenWord params.width accumulator).val.testBit
              params.width := hrightHigh.symm
  have hcarry : (step before).2.2.1.arithmetic.carry = false := by
    simpa [step, rawAccumulatorSwapStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.swapStep_preserves_projection
        rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne
        (fun x => x.2.2.1.arithmetic.carry)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hparked : (step before).2.2.1.arithmetic.parkedSource =
      (params.modulus.val : Word) := by
    have hframe :
        (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
          rawAccumulator_inPlaceAccumulator_ne before).2.2.1.arithmetic.parkedSource =
          before.2.2.1.arithmetic.parkedSource :=
      EncodedBit.Word.swapStep_preserves_projection
        rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne
        (fun x => x.2.2.1.arithmetic.parkedSource)
        (fun _ _ => rfl) (fun _ _ => rfl) before
    calc
      (step before).2.2.1.arithmetic.parkedSource =
          (EncodedBit.Word.swapStep rawAccumulatorWord rawInPlaceAccumulatorWord
            rawAccumulator_inPlaceAccumulator_ne before).2.2.1.arithmetic.parkedSource := by
        rw [hstepRaw]
      _ = before.2.2.1.arithmetic.parkedSource := hframe
      _ = (params.modulus.val : Word) := hbeforeParked
  have hcarryWork : (step before).2.2.1.arithmetic.carryWork =
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
        (MAU.Addition.VBECircuit.AdderWidth params.width) := by
    simpa [step, rawAccumulatorSwapStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.swapStep_preserves_projection
        rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne
        (fun x => x.2.2.1.arithmetic.carryWork)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hflag : (step before).2.2.1.arithmetic.reductionFlag = false := by
    simpa [step, rawAccumulatorSwapStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.swapStep_preserves_projection
        rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne
        (fun x => x.2.2.1.arithmetic.reductionFlag)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hwork : (step before).2.2.2 = false := by
    simpa [step, rawAccumulatorSwapStep, before, routingRawRegisters] using
      EncodedBit.Word.swapStep_preserves_projection
        rawAccumulatorWord rawInPlaceAccumulatorWord
        rawAccumulator_inPlaceAccumulator_ne (fun x => x.2.2.2)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  change step before =
    (multiplier, (target,
      (MAU.Multiplication.Accumulate.VBECircuit.workspaceState params.width
        source active (params.modulus.val : Word)
        (MAU.Addition.VBECircuit.widenWord params.width accumulator) false,
        false)))
  apply Prod.ext
  · exact hmultiplier
  · apply Prod.ext
    · exact haccumulator
    · apply Prod.ext
      · apply inPlaceRegisters_ext
        · exact hmultiplicand
        · apply additionRegisters_ext
          · exact hactive
          · exact htarget
          · exact hcarry
          · exact hparked
          · exact hcarryWork
          · exact hflag
      · exact hwork

/-- The named accumulator swap is the raw routing endpoint transported through
the field-layout equivalence. -/
private lemma accumulatorSwapStep_routing
    (multiplier source accumulator active target : Word) :
    accumulatorSwapStep
        (routingRegisters multiplier source accumulator active target) =
      routingRegisters multiplier source target active accumulator :=
  congrArg registersEquiv.symm
    (rawAccumulatorSwapStep_routing multiplier source accumulator active target)

set_option exponentiation.threshold 2048 in
/-- The source xor routing realizes any low-word xor relation while retaining
the clean high active-source bit and every other workspace field. -/
private lemma rawSourceCopyStep_routing
    (multiplier source accumulator active target result : Word)
    (hresult : ∀ bit : Fin params.width,
      result.val.testBit bit.val =
        (active.val.testBit bit.val ^^ source.val.testBit bit.val)) :
    rawSourceCopyStep
        (routingRawRegisters multiplier source accumulator active target) =
      routingRawRegisters multiplier source accumulator result target := by
  let before : RawRegisters :=
    routingRawRegisters multiplier source accumulator active target
  let step := rawSourceCopyStep
  have hstepRaw :
      step = EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
        rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne :=
    rfl
  have hbeforeAccumulator : before.2.1 = accumulator :=
    rfl
  have hbeforeMultiplicand : before.2.2.1.multiplicand = source :=
    rfl
  have hbeforeActiveSource :
      before.2.2.1.arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord params.width active :=
    rfl
  change step before =
    routingRawRegisters multiplier source accumulator result target
  have hmultiplier : (step before).1 = multiplier := by
    exact EncodedBit.Word.xorIntoStep_preserves_projection
      rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
      rawInPlaceMultiplicand_activeSource_ne (fun x => x.1)
      (fun _ _ => rfl) before
  have haccumulator : (step before).2.1 = accumulator := by
    have hframe :
        (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
          rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne
          before).2.1 = before.2.1 :=
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne (fun x => x.2.1)
        (fun _ _ => rfl) before
    calc
      (step before).2.1 =
          (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
            rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne
            before).2.1 := by
        rw [hstepRaw]
      _ = before.2.1 := hframe
      _ = accumulator := hbeforeAccumulator
  have hmultiplicand : (step before).2.2.1.multiplicand = source := by
    have hframe :
        (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
          rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne
          before).2.2.1.multiplicand = before.2.2.1.multiplicand :=
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne
        (fun x => x.2.2.1.multiplicand) (fun _ _ => rfl) before
    calc
      (step before).2.2.1.multiplicand =
          (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
            rawInPlaceActiveSourceWord rawInPlaceMultiplicand_activeSource_ne
            before).2.2.1.multiplicand := by
        rw [hstepRaw]
      _ = before.2.2.1.multiplicand := hframe
      _ = source := hbeforeMultiplicand
  have hactive : (step before).2.2.1.arithmetic.activeSource =
      MAU.Addition.VBECircuit.widenWord params.width result := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    by_cases hlow : bit.val < params.width
    · let low : Fin params.width := ⟨bit.val, hlow⟩
      have hbit :
          bit = lowSourceIndex low := by
        apply Fin.ext
        rfl
      rw [hbit]
      have hread :
          (rawInPlaceActiveSourceWord.bit low).get
              (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
                rawInPlaceActiveSourceWord
                rawInPlaceMultiplicand_activeSource_ne before) =
            ((rawInPlaceActiveSourceWord.bit low).get before ^^
              (rawInPlaceMultiplicandWord.bit low).get before) :=
        EncodedBit.Word.xorIntoStep_get_target
          rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
          rawInPlaceMultiplicand_activeSource_ne low
          (fun other hne =>
            rawInPlaceActiveSource_pairwise_ne other low hne)
          (fun other => Ne.symm
            (rawInPlaceMultiplicand_activeSource_cross_ne low other)) before
      have htargetRead (state : RawRegisters) :
          (rawInPlaceActiveSourceWord.bit low).get state =
            state.2.2.1.arithmetic.activeSource.val.testBit low.val :=
        rawInPlaceActiveSourceBit_get low state
      have hsourceRead (state : RawRegisters) :
          (rawInPlaceMultiplicandWord.bit low).get state =
            state.2.2.1.multiplicand.val.testBit low.val :=
        rawInPlaceMultiplicandBit_get low state
      have hinputTarget :
          (rawInPlaceActiveSourceWord.bit low).get before =
            active.val.testBit low.val := by
        calc
          (rawInPlaceActiveSourceWord.bit low).get before =
              before.2.2.1.arithmetic.activeSource.val.testBit low.val :=
            htargetRead before
          _ = (MAU.Addition.VBECircuit.widenWord params.width active).val.testBit
                low.val := by
            rw [hbeforeActiveSource]
          _ = active.val.testBit low.val := by
            rw [MAU.Addition.VBECircuit.widenWord_val]
      have hinputSource :
          (rawInPlaceMultiplicandWord.bit low).get before =
            source.val.testBit low.val := by
        calc
          (rawInPlaceMultiplicandWord.bit low).get before =
              before.2.2.1.multiplicand.val.testBit low.val :=
            hsourceRead before
          _ = source.val.testBit low.val := by
            rw [hbeforeMultiplicand]
      have hxor :
          ((rawInPlaceActiveSourceWord.bit low).get before ^^
            (rawInPlaceMultiplicandWord.bit low).get before) =
              (active.val.testBit low.val ^^ source.val.testBit low.val) :=
        congrArg₂ Bool.xor hinputTarget hinputSource
      have hwidenResult :
          (MAU.Addition.VBECircuit.widenWord params.width result).val.testBit
              low.val = result.val.testBit low.val := by
        rw [MAU.Addition.VBECircuit.widenWord_val]
      calc
        (step before).2.2.1.arithmetic.activeSource.val.testBit low.val =
            (rawInPlaceActiveSourceWord.bit low).get (step before) :=
          (htargetRead (step before)).symm
        _ = (rawInPlaceActiveSourceWord.bit low).get
              (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
                rawInPlaceActiveSourceWord
                rawInPlaceMultiplicand_activeSource_ne before) := by
          rw [hstepRaw]
        _ = ((rawInPlaceActiveSourceWord.bit low).get before ^^
              (rawInPlaceMultiplicandWord.bit low).get before) := hread
        _ = (active.val.testBit low.val ^^ source.val.testBit low.val) := hxor
        _ = result.val.testBit low.val := (hresult low).symm
        _ = (MAU.Addition.VBECircuit.widenWord params.width result).val.testBit
              low.val := hwidenResult.symm
    · have hlast :
          bit = (Fin.last params.width :
            Fin (MAU.Addition.VBECircuit.AdderWidth params.width)) := by
        apply Fin.ext
        have hbitLt := bit.isLt
        simp only [MAU.Addition.VBECircuit.AdderWidth, Fin.val_last] at hbitLt ⊢
        omega
      have hlastVal : (Fin.last params.width).val = params.width :=
        rfl
      rw [hlast, hlastVal]
      have hread :
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
              (Fin.last params.width))).get
              (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
                rawInPlaceActiveSourceWord
                rawInPlaceMultiplicand_activeSource_ne before) =
            (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
                (Fin.last params.width))).get before :=
        EncodedBit.Word.xorIntoStep_get_observed_of_target_ne
          rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
          rawInPlaceMultiplicand_activeSource_ne
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
              (Fin.last params.width)))
          rawInPlaceActiveSource_activeHigh_ne before
      have hactiveHigh : active.val.testBit params.width = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt active)
      have hresultHigh : result.val.testBit params.width = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt result)
      have hrightHigh :
          (MAU.Addition.VBECircuit.widenWord params.width result).val.testBit
              params.width = false := by
        rw [MAU.Addition.VBECircuit.widenWord_val]
        exact hresultHigh
      have hbeforeHigh :
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
              (Fin.last params.width))).get before = false := by
        calc
          (rawInPlaceBit
            (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
              (Fin.last params.width))).get before =
              before.2.2.1.arithmetic.activeSource.val.testBit params.width :=
            rawInPlaceActiveSourceHighBit_get before
          _ = (MAU.Addition.VBECircuit.widenWord params.width active).val.testBit
                params.width := by
            rw [hbeforeActiveSource]
          _ = active.val.testBit params.width := by
            rw [MAU.Addition.VBECircuit.widenWord_val]
          _ = false := hactiveHigh
      calc
        (step before).2.2.1.arithmetic.activeSource.val.testBit params.width =
            (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
                (Fin.last params.width))).get (step before) :=
          (rawInPlaceActiveSourceHighBit_get (step before)).symm
        _ = (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
                (Fin.last params.width))).get
              (EncodedBit.Word.xorIntoStep rawInPlaceMultiplicandWord
                rawInPlaceActiveSourceWord
                rawInPlaceMultiplicand_activeSource_ne before) := by
          rw [hstepRaw]
        _ = (rawInPlaceBit
              (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit params.width
                (Fin.last params.width))).get before := hread
        _ = false := hbeforeHigh
        _ = (MAU.Addition.VBECircuit.widenWord params.width result).val.testBit
              params.width := hrightHigh.symm
  have htarget : (step before).2.2.1.arithmetic.target =
      MAU.Addition.VBECircuit.widenWord params.width target := by
    simpa [step, rawSourceCopyStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne
        (fun x => x.2.2.1.arithmetic.target) (fun _ _ => rfl) before
  have hcarry : (step before).2.2.1.arithmetic.carry = false := by
    simpa [step, rawSourceCopyStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne
        (fun x => x.2.2.1.arithmetic.carry) (fun _ _ => rfl) before
  have hparked : (step before).2.2.1.arithmetic.parkedSource =
      (params.modulus.val : Word) := by
    simpa [step, rawSourceCopyStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne
        (fun x => x.2.2.1.arithmetic.parkedSource) (fun _ _ => rfl) before
  have hcarryWork : (step before).2.2.1.arithmetic.carryWork =
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
        (MAU.Addition.VBECircuit.AdderWidth params.width) := by
    simpa [step, rawSourceCopyStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne
        (fun x => x.2.2.1.arithmetic.carryWork) (fun _ _ => rfl) before
  have hflag : (step before).2.2.1.arithmetic.reductionFlag = false := by
    simpa [step, rawSourceCopyStep, before, routingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne
        (fun x => x.2.2.1.arithmetic.reductionFlag) (fun _ _ => rfl) before
  have hwork : (step before).2.2.2 = false := by
    simpa [step, rawSourceCopyStep, before, routingRawRegisters] using
      EncodedBit.Word.xorIntoStep_preserves_projection
        rawInPlaceMultiplicandWord rawInPlaceActiveSourceWord
        rawInPlaceMultiplicand_activeSource_ne (fun x => x.2.2.2)
        (fun _ _ => rfl) before
  change step before =
    (multiplier, (accumulator,
      (MAU.Multiplication.Accumulate.VBECircuit.workspaceState params.width
        source result (params.modulus.val : Word)
        (MAU.Addition.VBECircuit.widenWord params.width target) false,
        false)))
  apply Prod.ext
  · exact hmultiplier
  · apply Prod.ext
    · exact haccumulator
    · apply Prod.ext
      · apply
          (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
            params.width).injective
        change
          ((step before).2.2.1.multiplicand,
            (step before).2.2.1.arithmetic) =
            (source,
              MAU.Addition.VBECircuit.sourceSwapCleanState params.width result
                (params.modulus.val : Word)
                (MAU.Addition.VBECircuit.widenWord params.width target) false)
        apply Prod.ext
        · exact hmultiplicand
        · apply
            (MAU.Addition.VBECircuit.registersEquiv params.width).injective
          simp [MAU.Addition.VBECircuit.registersEquiv,
            MAU.Addition.VBECircuit.sourceSwapCleanState, hactive, htarget,
            hcarry, hparked, hcarryWork, hflag]
      · exact hwork

/-- The named source xor endpoint is the raw routing endpoint transported
through the field-layout equivalence. -/
private lemma sourceCopyStep_routing
    (multiplier source accumulator active target result : Word)
    (hresult : ∀ bit : Fin params.width,
      result.val.testBit bit.val =
        (active.val.testBit bit.val ^^ source.val.testBit bit.val)) :
    sourceCopyStep
        (routingRegisters multiplier source accumulator active target) =
      routingRegisters multiplier source accumulator result target :=
  congrArg registersEquiv.symm
    (rawSourceCopyStep_routing multiplier source accumulator active target result
      hresult)

/-- Loading a clean active source copies the stored multiplicand. -/
private lemma sourceCopyStep_routing_zero
    (multiplier source accumulator target : Word) :
    sourceCopyStep
        (routingRegisters multiplier source accumulator 0 target) =
      routingRegisters multiplier source accumulator source target := by
  apply sourceCopyStep_routing multiplier source accumulator 0 target source
  intro bit
  simp

/-- Unloading the copied active source restores its clean zero state. -/
private lemma sourceUnloadStep_routing_source
    (multiplier source accumulator target : Word) :
    sourceUnloadStep
        (routingRegisters multiplier source accumulator source target) =
      routingRegisters multiplier source accumulator 0 target := by
  change sourceCopyStep
      (routingRegisters multiplier source accumulator source target) =
    routingRegisters multiplier source accumulator 0 target
  apply sourceCopyStep_routing multiplier source accumulator source target 0
  intro bit
  simp

set_option exponentiation.threshold 2048 in
/-- The raw lifted unconditional VBE schedule adds the routed active source
into the routed target and restores every arithmetic auxiliary field. -/
private lemma rawUncontrolledAddStep_routing
    (multiplier source accumulator : Word)
    (hsource : source.val < params.modulus.val)
    (haccumulator : accumulator.val < params.modulus.val) :
    rawUncontrolledAddStep
        (routingRawRegisters multiplier source 0 source accumulator) =
      routingRawRegisters multiplier source 0 source
        ((source.val + accumulator.val) %
          params.modulus.val : Word) := by
  let result : Word :=
    ((source.val + accumulator.val) %
      params.modulus.val : Word)
  have hresultBound :
      (source.val + accumulator.val) % params.modulus.val <
        2 ^ params.width :=
    (Nat.mod_lt _ params.modulusPos).trans
      modulus_lt_capacity
  have hwidenResult :
      MAU.Addition.VBECircuit.widenWord params.width result =
        ((source.val + accumulator.val) %
          params.modulus.val :
            PlainAdder.Word
              (MAU.Addition.VBECircuit.AdderWidth params.width)) := by
    dsimp [result]
    exact MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
      params.width ((source.val + accumulator.val) %
        params.modulus.val) hresultBound
  have hbase :
      MAU.Addition.VBECircuit.modularAddStep params.width
          params.modulus.val
          (MAU.Addition.VBECircuit.sourceSwapCleanState params.width
            source (params.modulus.val : Word)
            (MAU.Addition.VBECircuit.widenWord params.width accumulator) false) =
        MAU.Addition.VBECircuit.sourceSwapCleanState params.width source
          (params.modulus.val : Word)
          (MAU.Addition.VBECircuit.widenWord params.width result) false := by
    rw [MAU.Addition.VBECircuit.modularAddStep_cleanEndpoint
      params.width params.modulus.val source accumulator
      params.modulusPos
      modulus_lt_capacity hsource haccumulator]
    simp only [hwidenResult]
  have hstep :
      MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
          params.width params.modulus.val
          (MAU.Multiplication.Accumulate.VBECircuit.workspaceState params.width
            source source (params.modulus.val : Word)
            (MAU.Addition.VBECircuit.widenWord params.width accumulator) false) =
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState params.width
          source source (params.modulus.val : Word)
          (MAU.Addition.VBECircuit.widenWord params.width result) false := by
    simpa [MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using
      congrArg
        (fun arithmetic =>
          ({ multiplicand := source, arithmetic := arithmetic } :
            MAU.Multiplication.Accumulate.VBECircuit.Registers params.width))
        hbase
  calc
    rawUncontrolledAddStep
        (routingRawRegisters multiplier source 0 source accumulator) =
      (multiplier, (0,
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
          params.width params.modulus.val
          (MAU.Multiplication.Accumulate.VBECircuit.workspaceState params.width
            source source (params.modulus.val : Word)
            (MAU.Addition.VBECircuit.widenWord params.width accumulator) false),
          false))) := by
      simpa only [routingRawRegisters] using
        rawUncontrolledAddStep_eq_liftedModularAdd
          (routingRawRegisters multiplier source 0 source accumulator)
    _ = routingRawRegisters multiplier source 0 source result := by
      exact congrArg (fun workspace => (multiplier, (0, (workspace, false)))) hstep

/-- The named unconditional add is the raw arithmetic endpoint transported
through the field-layout equivalence. -/
private lemma uncontrolledAddStep_routing
    (multiplier source accumulator : Word)
    (hsource : source.val < params.modulus.val)
    (haccumulator : accumulator.val < params.modulus.val) :
    uncontrolledAddStep
        (routingRegisters multiplier source 0 source accumulator) =
      routingRegisters multiplier source 0 source
        ((source.val + accumulator.val) %
          params.modulus.val : Word) :=
  congrArg registersEquiv.symm
    (rawUncontrolledAddStep_routing multiplier source accumulator
      hsource haccumulator)

/-- A false selected multiplier bit leaves the complete common carrier
unchanged, without any condition on the shared work bit. -/
lemma stageStep_eq_self_of_multiplier_false (bit : Fin params.width)
    (x : Registers) (hmultiplier : x.multiplier.val.testBit bit.val = false) :
    stageStep bit x = x := by
  have hcontrol : (rawMultiplierBit bit).get (registersEquiv x) = false := by
    rw [rawMultiplierBit_get]
    simpa [registersEquiv] using hmultiplier
  have hstep :=
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (rawMultiplierBit bit) rawWorkBit rawArithmeticGates
      (rawMultiplierDisjoint bit) rawWorkDisjoint (rawMultiplierWork_ne bit)
      (registersEquiv x) hcontrol
  change registersEquiv.symm (rawStageStep bit (registersEquiv x)) = x
  have hstep' : rawStageStep bit (registersEquiv x) = registersEquiv x := by
    exact hstep
  rw [hstep']
  exact registersEquiv.symm_apply_apply x

/-- With a true selected multiplier bit and a clean shared work bit, the
controlled stage agrees exactly with the unconditional reused VBE schedule. -/
lemma stageStep_eq_uncontrolledAddStep_of_multiplier_true_work_clean
    (bit : Fin params.width) (x : Registers)
    (hmultiplier : x.multiplier.val.testBit bit.val = true)
    (hwork : x.work = false) :
    stageStep bit x = uncontrolledAddStep x := by
  have hcontrol : (rawMultiplierBit bit).get (registersEquiv x) = true := by
    rw [rawMultiplierBit_get]
    simpa [registersEquiv] using hmultiplier
  have hworkRaw : rawWorkBit.get (registersEquiv x) = false := by
    rw [rawWorkBit_get]
    simpa [registersEquiv] using hwork
  have hstep :=
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (rawMultiplierBit bit) rawWorkBit rawArithmeticGates
      (rawMultiplierDisjoint bit) rawWorkDisjoint (rawMultiplierWork_ne bit)
      (registersEquiv x) hcontrol hworkRaw
  change registersEquiv.symm (rawStageStep bit (registersEquiv x)) =
    registersEquiv.symm (rawUncontrolledAddStep (registersEquiv x))
  apply congrArg registersEquiv.symm
  exact hstep

/-! ## In-place multiplication lift and one variable-multiplication round -/

/-- Lift an in-place primitive list through the complete common carrier while
preserving the clean work bit, external accumulator, and multiplier. -/
def liftInPlaceGates
    (gates : List (EncodedBit.GateSpec inPlaceEncoding)) :
    List (EncodedBit.GateSpec rawEncoding) :=
  let withWork : List (EncodedBit.GateSpec inPlaceWithWorkEncoding) :=
    gates.map (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let withAccumulator :
      List (EncodedBit.GateSpec accumulatorSuffixEncoding) :=
    withWork.map (EncodedBit.GateSpec.prodRight wordEncoding)
  withAccumulator.map (EncodedBit.GateSpec.prodRight wordEncoding)

/-- Lift an in-place semantic step while preserving multiplier, accumulator,
and control-work fields of the common physical carrier. -/
def liftInPlaceStep
    (step : InPlaceRegisters → InPlaceRegisters) :
    RawRegisters → RawRegisters :=
  fun x => (x.1, (x.2.1, (step x.2.2.1, x.2.2.2)))

/-- The lifted primitive list has exactly the corresponding product-carrier
semantic action. -/
lemma liftInPlaceGates_stepList
    (gates : List (EncodedBit.GateSpec inPlaceEncoding)) (x : RawRegisters) :
    EncodedBit.GateSpec.stepList (liftInPlaceGates gates) x =
      liftInPlaceStep (EncodedBit.GateSpec.stepList gates) x := by
  rcases x with ⟨multiplier, accumulator, inPlace, work⟩
  let withWork : List (EncodedBit.GateSpec inPlaceWithWorkEncoding) :=
    gates.map (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let withAccumulator :
      List (EncodedBit.GateSpec accumulatorSuffixEncoding) :=
    withWork.map (EncodedBit.GateSpec.prodRight wordEncoding)
  change EncodedBit.GateSpec.stepList
      (withAccumulator.map (EncodedBit.GateSpec.prodRight wordEncoding))
        (multiplier, (accumulator, (inPlace, work))) = _
  rw [EncodedBit.GateSpec.stepList_prodRight]
  change (multiplier,
    EncodedBit.GateSpec.stepList withAccumulator
      (accumulator, (inPlace, work))) = _
  rw [show EncodedBit.GateSpec.stepList withAccumulator
      (accumulator, (inPlace, work)) =
        (accumulator, EncodedBit.GateSpec.stepList withWork (inPlace, work)) from
      by
        simpa only [withAccumulator] using
          EncodedBit.GateSpec.stepList_prodRight wordEncoding withWork
            (accumulator, (inPlace, work))]
  rw [show EncodedBit.GateSpec.stepList withWork (inPlace, work) =
      (EncodedBit.GateSpec.stepList gates inPlace, work) from
    by
      simpa only [withWork] using
        EncodedBit.GateSpec.stepList_prodLeft BinaryLabelEncoding.bool gates
          (inPlace, work)]
  rfl

/-- The modulus is odd, so the static residue `2` is invertible. -/
lemma primeModulus_odd : Odd params.modulus.val :=
  params.modulusOdd

/-- Coprimality certificate used to construct the fixed doubling unit. -/
lemma two_coprime_primeModulus :
    Nat.Coprime 2 params.modulus.val :=
  primeModulus_odd.coprime_two_left

/-- Canonical in-place multiplication unit for one source-doubling step. -/
def twoUnit : (ZMod params.modulus.val)ˣ :=
  ZMod.unitOfCoprime 2 two_coprime_primeModulus

/-- The variable source widened by the already allocated clean control-work
bit.  The extra bit is the high position of the shift/reduce operand. -/
def rawDoublingSourceWord :
    EncodedBit.Word rawEncoding
      (MAU.Addition.VBECircuit.AdderWidth params.width) where
  bit := fun bit =>
    Fin.lastCases rawWorkBit
      (fun low => rawInPlaceMultiplicandBit low) bit

/-- Full VBE arithmetic target, including its overflow position, lifted into
the common variable-multiplication carrier. -/
def rawDoublingTargetWord :
    EncodedBit.Word rawEncoding
      (MAU.Addition.VBECircuit.AdderWidth params.width) where
  bit := fun bit => rawInPlaceBit
    (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width bit)

@[simp] private lemma rawDoublingSourceWord_bit_last :
    rawDoublingSourceWord.bit (Fin.last params.width) = rawWorkBit := by
  simp [rawDoublingSourceWord, MAU.Addition.VBECircuit.AdderWidth]

@[simp] private lemma rawDoublingSourceWord_bit_castSucc
    (bit : Fin params.width) :
    rawDoublingSourceWord.bit (Fin.castSucc bit) =
      rawInPlaceMultiplicandBit bit := by
  simp [rawDoublingSourceWord, MAU.Addition.VBECircuit.AdderWidth]

/-- The VBE reduction flag lifted into the common carrier. -/
def rawDoublingReductionFlagBit : EncodedBit rawEncoding :=
  rawInPlaceBit
    (MAU.Multiplication.Accumulate.VBECircuit.reductionFlagBit params.width)

@[simp] lemma rawDoublingReductionFlagBit_get (x : RawRegisters) :
    rawDoublingReductionFlagBit.get x =
      x.2.2.1.arithmetic.reductionFlag := by
  change
    (MAU.Multiplication.Accumulate.VBECircuit.reductionFlagBit
      params.width).get x.2.2.1 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.reductionFlagBit_get
    params.width x.2.2.1

/-- Least-significant index of every positive-width residue word. -/
def doublingLowBit : Fin params.width :=
  ⟨0, params.widthPos⟩

private lemma rawInPlaceBit_rawWork_ne
    (bit : EncodedBit inPlaceEncoding) :
    (rawInPlaceBit bit).wire ≠ rawWorkBit.wire := by
  have hinner :
      (BinaryLabelEncoding.prodLeftBit inPlaceEncoding
          BinaryLabelEncoding.bool bit).wire ≠
        (BinaryLabelEncoding.prodRightBit inPlaceEncoding
          BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit).wire :=
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      inPlaceEncoding BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit
      bit).symm
  have hsuffix := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hinner
  have hraw := EncodedBit.GateSpec.prodRightWire_ne wordEncoding hsuffix
  simpa only [rawInPlaceBit, rawWorkBit, rawEncoding,
    accumulatorSuffixEncoding, inPlaceWithWorkEncoding] using hraw

/-- Distinct bits of the widened source occupy distinct physical wires. -/
lemma rawDoublingSourceWord_pairwise_ne
    (left right : Fin (MAU.Addition.VBECircuit.AdderWidth params.width))
    (hne : left ≠ right) :
    (rawDoublingSourceWord.bit left).wire ≠
      (rawDoublingSourceWord.bit right).wire := by
  revert hne
  revert right
  refine Fin.lastCases ?_ ?_ left
  · intro right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · intro hsame _
      exact hsame rfl
    · intro low _
      simpa [rawDoublingSourceWord, rawInPlaceMultiplicandBit,
        MAU.Multiplication.VBECircuit.multiplicandWord,
        MAU.Multiplication.Accumulate.VBECircuit.multiplicandWord] using
        (rawInPlaceBit_rawWork_ne
          (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
            params.width low)).symm
  · intro low right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · intro _
      simpa [rawDoublingSourceWord, rawInPlaceMultiplicandBit] using
        rawInPlaceBit_rawWork_ne
          (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
            params.width low)
    · intro other hne
      have hlow : low ≠ other := by
        intro heq
        apply hne
        subst other
        rfl
      intro hwire
      apply inPlaceMultiplicandBit_pairwise_ne low other hlow
      apply Fin.ext
      simpa [rawDoublingSourceWord, rawInPlaceMultiplicandBit,
        inPlaceMultiplicandBit, EncodedBit.relabel] using
        congrArg Fin.val hwire

/-- Distinct bits of the full VBE target occupy distinct physical wires. -/
lemma rawDoublingTargetWord_pairwise_ne
    (left right : Fin (MAU.Addition.VBECircuit.AdderWidth params.width))
    (hne : left ≠ right) :
    (rawDoublingTargetWord.bit left).wire ≠
      (rawDoublingTargetWord.bit right).wire := by
  have hbase :
      (MAU.Addition.VBECircuit.targetBit params.width left).wire ≠
        (MAU.Addition.VBECircuit.targetBit params.width right).wire := by
    intro hwire
    apply hne
    apply Fin.ext
    have hval := congrArg Fin.val hwire
    have hleft := MAU.Addition.VBECircuit.targetBit_wire_val
      params.width left
    have hright := MAU.Addition.VBECircuit.targetBit_wire_val
      params.width right
    rw [hleft, hright] at hval
    simp only [MAU.Addition.VBECircuit.AdderWidth] at hval
    have hleftBound : left.val ≤ params.width := by
      have := left.isLt
      simpa only [MAU.Addition.VBECircuit.AdderWidth, Nat.lt_add_one_iff] using this
    have hrightBound : right.val ≤ params.width := by
      have := right.isLt
      simpa only [MAU.Addition.VBECircuit.AdderWidth, Nat.lt_add_one_iff] using this
    omega
  simpa [rawDoublingTargetWord,
    MAU.Multiplication.Accumulate.VBECircuit.targetBit] using
    rawInPlaceBit_wire_ne
      (MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit_ne
        params.width hbase)

/-- The widened source and full arithmetic target are physically disjoint. -/
lemma rawDoublingSource_target_cross_ne
    (source target :
      Fin (MAU.Addition.VBECircuit.AdderWidth params.width)) :
    (rawDoublingSourceWord.bit source).wire ≠
      (rawDoublingTargetWord.bit target).wire := by
  revert target
  refine Fin.lastCases ?_ ?_ source
  · intro target
    simpa [rawDoublingSourceWord, rawDoublingTargetWord] using
      (rawInPlaceBit_rawWork_ne
        (MAU.Multiplication.Accumulate.VBECircuit.targetBit
          params.width target)).symm
  · intro source target
    simpa [rawDoublingSourceWord, rawInPlaceMultiplicandBit,
      rawDoublingTargetWord,
      MAU.Multiplication.Accumulate.VBECircuit.targetBit] using
      rawInPlaceBit_wire_ne
        (MAU.Multiplication.VBECircuit.multiplicand_liftArithmetic_ne
          params.width source
          (MAU.Addition.VBECircuit.targetBit params.width target))

/-- The low source bit used to erase the reduction flag is a distinct wire. -/
lemma rawDoublingSourceZero_reductionFlag_ne :
    (rawInPlaceMultiplicandBit doublingLowBit).wire ≠
      rawDoublingReductionFlagBit.wire := by
  simpa [rawInPlaceMultiplicandBit, rawDoublingReductionFlagBit,
    MAU.Multiplication.Accumulate.VBECircuit.reductionFlagBit] using
    rawInPlaceBit_wire_ne
      (MAU.Multiplication.VBECircuit.multiplicand_liftArithmetic_ne
        params.width doublingLowBit
        (MAU.Addition.VBECircuit.reductionFlagBit params.width))

lemma rawDoublingSourceWord_get_castSucc
    (bit : Fin params.width) (x : RawRegisters) :
    (rawDoublingSourceWord.bit (Fin.castSucc bit)).get x =
      x.2.2.1.multiplicand.val.testBit bit.val := by
  simpa [rawDoublingSourceWord, rawInPlaceMultiplicandBit] using
    rawInPlaceMultiplicandBit_get bit x

lemma rawDoublingSourceWord_get_last (x : RawRegisters) :
    (rawDoublingSourceWord.bit (Fin.last params.width)).get x = x.2.2.2 := by
  simp [rawDoublingSourceWord]

@[simp] lemma rawDoublingTargetWord_get
    (bit : Fin (MAU.Addition.VBECircuit.AdderWidth params.width))
    (x : RawRegisters) :
    (rawDoublingTargetWord.bit bit).get x =
      x.2.2.1.arithmetic.target.val.testBit bit.val := by
  change
    (MAU.Multiplication.Accumulate.VBECircuit.targetBit params.width bit).get
      x.2.2.1 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.targetBit_get
    params.width bit x.2.2.1

/-- Two word swaps move the source into and back out of the VBE target. -/
def doublingSwapGates : List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.swapGates rawDoublingSourceWord rawDoublingTargetWord
    (fun bit => rawDoublingSource_target_cross_ne bit bit)

/-- A high-to-low adjacent-swap sweep implements the zero-filled left shift
because the widened target's low bit is zero after the initial word swap. -/
def doublingShiftGates : List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.adjacentShiftRightGates rawDoublingTargetWord
    rawDoublingTargetWord_pairwise_ne

/-- For odd modulus and an even unreduced input, the reduced result parity is
the retained reduction flag; this CNOT erases it after the final word swap. -/
def doublingCleanupGates : List (EncodedBit.GateSpec rawEncoding) :=
  [.cnot (rawInPlaceMultiplicandBit doublingLowBit)
    rawDoublingReductionFlagBit
    rawDoublingSourceZero_reductionFlag_ne]

/-- Primitive source list for shift, one exact modular reduction, and cleanup.
It reuses the existing `7f+5` carrier and contains no generic constant
multiplication block. -/
def doublingGates : List (EncodedBit.GateSpec rawEncoding) :=
  doublingSwapGates ++ doublingShiftGates ++ rawArithmeticGates ++
    doublingSwapGates ++ doublingCleanupGates

/-- Folded action of either full widened source/target word swap. -/
def rawDoublingSwapStep : RawRegisters → RawRegisters :=
  EncodedBit.Word.swapStep rawDoublingSourceWord rawDoublingTargetWord
    (fun bit => rawDoublingSource_target_cross_ne bit bit)

/-- Folded high-to-low adjacent-swap action on the full VBE target. -/
def rawDoublingShiftStep : RawRegisters → RawRegisters :=
  EncodedBit.Word.adjacentShiftRightStep rawDoublingTargetWord
    rawDoublingTargetWord_pairwise_ne

/-- Folded final parity-to-reduction-flag cleanup CNOT. -/
def rawDoublingCleanupStep : RawRegisters → RawRegisters :=
  EncodedBit.GateSpec.step
    (.cnot (rawInPlaceMultiplicandBit doublingLowBit)
      rawDoublingReductionFlagBit rawDoublingSourceZero_reductionFlag_ne)

private def doublingRoutingRawRegisters
    (multiplier accumulator source target : Word) (flag : Bool) :
    RawRegisters :=
  (multiplier, (accumulator,
    (MAU.Multiplication.Accumulate.VBECircuit.workspaceState
      params.width source 0 (params.modulus.val : Word)
      (MAU.Addition.VBECircuit.widenWord params.width target) flag,
      false)))

private def doublingWideRawRegisters
    (multiplier accumulator source : Word)
    (target : PlainAdder.Word
      (MAU.Addition.VBECircuit.AdderWidth params.width))
    (flag work : Bool) : RawRegisters :=
  (multiplier, (accumulator,
    (MAU.Multiplication.Accumulate.VBECircuit.workspaceState
      params.width source 0 (params.modulus.val : Word) target flag,
      work)))

private def doubledWideWord (target : Word) :
    PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth params.width) :=
  ((2 * target.val : Nat) :
    PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth params.width))

@[simp] private lemma doubledWideWord_val (target : Word) :
    (doubledWideWord target).val = 2 * target.val := by
  unfold doubledWideWord
  apply ZMod.val_natCast_of_lt
  have htarget := ZMod.val_lt target
  simp only [MAU.Addition.VBECircuit.AdderWidth, pow_succ]
  omega

private lemma rawDoublingSwapStep_routing
    (multiplier accumulator source target : Word) (flag : Bool) :
    rawDoublingSwapStep
        (doublingRoutingRawRegisters multiplier accumulator source target flag) =
      doublingRoutingRawRegisters multiplier accumulator target source flag := by
  let before :=
    doublingRoutingRawRegisters multiplier accumulator source target flag
  let step := rawDoublingSwapStep
  have hleft := EncodedBit.Word.swapStep_get_left_word
    rawDoublingSourceWord rawDoublingTargetWord
    (fun bit => rawDoublingSource_target_cross_ne bit bit)
    rawDoublingSourceWord_pairwise_ne rawDoublingTargetWord_pairwise_ne
    rawDoublingSource_target_cross_ne before
  have hright := EncodedBit.Word.swapStep_get_right_word
    rawDoublingSourceWord rawDoublingTargetWord
    (fun bit => rawDoublingSource_target_cross_ne bit bit)
    rawDoublingSourceWord_pairwise_ne rawDoublingTargetWord_pairwise_ne
    rawDoublingSource_target_cross_ne before
  have hpreserve {Projection : Type} (project : RawRegisters → Projection)
      (hsource : ∀ i x, project ((rawDoublingSourceWord.bit i).flip x) =
        project x)
      (htarget : ∀ i x, project ((rawDoublingTargetWord.bit i).flip x) =
        project x) :
      project (step before) = project before := by
    exact EncodedBit.Word.swapStep_preserves_projection
      rawDoublingSourceWord rawDoublingTargetWord
      (fun bit => rawDoublingSource_target_cross_ne bit bit)
      project hsource htarget before
  have hsourcePreserve {Projection : Type}
      (project : RawRegisters → Projection)
      (hwork : ∀ x, project (rawWorkBit.flip x) = project x)
      (hlow : ∀ low x,
        project ((rawInPlaceMultiplicandBit low).flip x) = project x) :
      ∀ i x, project ((rawDoublingSourceWord.bit i).flip x) = project x := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa only [rawDoublingSourceWord_bit_last] using hwork
    · intro low
      simpa only [rawDoublingSourceWord_bit_castSucc] using hlow low
  have hmultiplier : (step before).1 = multiplier := by
    simpa [before, doublingRoutingRawRegisters, step, rawDoublingSwapStep] using
      hpreserve (fun x => x.1)
        (hsourcePreserve (fun x => x.1) (fun _ => rfl) (fun _ _ => rfl))
        (fun _ _ => rfl)
  have haccumulator : (step before).2.1 = accumulator := by
    simpa [before, doublingRoutingRawRegisters, step, rawDoublingSwapStep] using
      hpreserve (fun x => x.2.1)
        (hsourcePreserve (fun x => x.2.1) (fun _ => rfl) (fun _ _ => rfl))
        (fun _ _ => rfl)
  have hmultiplicand : (step before).2.2.1.multiplicand = target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread := congrFun hleft (Fin.castSucc bit)
    simpa [step, rawDoublingSwapStep, before, doublingRoutingRawRegisters,
      rawInPlaceMultiplicandBit_get,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using hread
  have hwork : (step before).2.2.2 = false := by
    have hread := congrFun hleft (Fin.last params.width)
    have hhigh : target.val.testBit params.width = false :=
      Nat.testBit_lt_two_pow (ZMod.val_lt target)
    simpa [step, rawDoublingSwapStep, before, doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState,
      MAU.Addition.VBECircuit.widenWord_val, hhigh] using hread
  have htarget : (step before).2.2.1.arithmetic.target =
      MAU.Addition.VBECircuit.widenWord params.width source := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread := congrFun hright bit
    revert hread
    refine Fin.lastCases ?_ ?_ bit
    · intro hread
      have hhigh : source.val.testBit params.width = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt source)
      simpa [step, rawDoublingSwapStep, before, doublingRoutingRawRegisters,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        MAU.Addition.VBECircuit.widenWord_val, hhigh] using hread
    · intro low hread
      simpa [step, rawDoublingSwapStep, before, doublingRoutingRawRegisters,
        rawInPlaceMultiplicandBit_get,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        MAU.Addition.VBECircuit.widenWord_val] using hread
  have hactive : (step before).2.2.1.arithmetic.activeSource =
      MAU.Addition.VBECircuit.widenWord params.width (0 : Word) := by
    simpa [before, doublingRoutingRawRegisters, step, rawDoublingSwapStep,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.activeSource)
        (hsourcePreserve (fun x => x.2.2.1.arithmetic.activeSource)
          (fun _ => rfl) (fun _ _ => rfl))
        (fun _ _ => rfl)
  have hcarry : (step before).2.2.1.arithmetic.carry = false := by
    simpa [before, doublingRoutingRawRegisters, step, rawDoublingSwapStep,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.carry)
        (hsourcePreserve (fun x => x.2.2.1.arithmetic.carry)
          (fun _ => rfl) (fun _ _ => rfl))
        (fun _ _ => rfl)
  have hparked : (step before).2.2.1.arithmetic.parkedSource =
      (params.modulus.val : Word) := by
    simpa [before, doublingRoutingRawRegisters, step, rawDoublingSwapStep,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.parkedSource)
        (hsourcePreserve (fun x => x.2.2.1.arithmetic.parkedSource)
          (fun _ => rfl) (fun _ _ => rfl))
        (fun _ _ => rfl)
  have hcarryWork : (step before).2.2.1.arithmetic.carryWork =
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
        (MAU.Addition.VBECircuit.AdderWidth params.width) := by
    simpa [before, doublingRoutingRawRegisters, step, rawDoublingSwapStep,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.carryWork)
        (hsourcePreserve (fun x => x.2.2.1.arithmetic.carryWork)
          (fun _ => rfl) (fun _ _ => rfl))
        (fun _ _ => rfl)
  have hflag : (step before).2.2.1.arithmetic.reductionFlag = flag := by
    simpa [before, doublingRoutingRawRegisters, step, rawDoublingSwapStep,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.reductionFlag)
        (hsourcePreserve (fun x => x.2.2.1.arithmetic.reductionFlag)
          (fun _ => rfl) (fun _ _ => rfl))
        (fun _ _ => rfl)
  change step before = _
  apply Prod.ext
  · exact hmultiplier
  · apply Prod.ext
    · exact haccumulator
    · apply Prod.ext
      · apply inPlaceRegisters_ext
        · exact hmultiplicand
        · apply additionRegisters_ext
          · exact hactive
          · exact htarget
          · exact hcarry
          · exact hparked
          · exact hcarryWork
          · exact hflag
      · exact hwork

private lemma rawDoublingShiftStep_routing
    (multiplier accumulator source target : Word) (flag : Bool) :
    rawDoublingShiftStep
        (doublingRoutingRawRegisters multiplier accumulator source target flag) =
      doublingWideRawRegisters multiplier accumulator source
        (doubledWideWord target) flag false := by
  let before :=
    doublingRoutingRawRegisters multiplier accumulator source target flag
  let step := rawDoublingShiftStep
  have hpreserve {Projection : Type} (project : RawRegisters → Projection)
      (htarget : ∀ i x, project ((rawDoublingTargetWord.bit i).flip x) =
        project x) :
      project (step before) = project before := by
    unfold step rawDoublingShiftStep EncodedBit.Word.adjacentShiftRightStep
      EncodedBit.Word.adjacentShiftRightGates
    apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    intro gate hgate
    have hleft : gate ∈ EncodedBit.Word.adjacentShiftLeftGates
        rawDoublingTargetWord rawDoublingTargetWord_pairwise_ne := by
      simpa using List.mem_reverse.mp hgate
    rw [EncodedBit.Word.adjacentShiftLeftGates] at hleft
    rcases List.mem_flatMap.mp hleft with ⟨i, _hi, hleft⟩
    simp only [EncodedBit.Word.adjacentSwapGates, EncodedBit.swapGates,
      List.mem_cons, List.not_mem_nil, or_false] at hleft
    rcases hleft with hleft | hleft | hleft <;> subst gate
    · exact htarget _
    · exact htarget _
    · exact htarget _
  have htarget : (step before).2.2.1.arithmetic.target =
      doubledWideWord target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    simp only [MAU.Addition.VBECircuit.AdderWidth] at bit ⊢
    refine Fin.cases ?_ ?_ bit
    · have hread := EncodedBit.Word.adjacentShiftRightStep_get_zero
        rawDoublingTargetWord rawDoublingTargetWord_pairwise_ne before
      have hhigh : target.val.testBit params.width = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt target)
      have hdoubleZero : (2 * target.val).testBit 0 = false := by
        simp
      simp only [Fin.val_zero]
      rw [doubledWideWord_val, hdoubleZero]
      simpa [step, rawDoublingShiftStep, before,
        doublingRoutingRawRegisters,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        MAU.Addition.VBECircuit.widenWord_val, hhigh] using hread
    · intro low
      have hread := EncodedBit.Word.adjacentShiftRightStep_get_succ
        rawDoublingTargetWord rawDoublingTargetWord_pairwise_ne low before
      have hdoubleSucc :
          (2 * target.val).testBit low.succ.val =
            target.val.testBit low.val := by
        simpa [Nat.bit_false] using
          Nat.testBit_bit_succ low.val false target.val
      rw [doubledWideWord_val, hdoubleSucc]
      simpa [step, rawDoublingShiftStep, before,
        doublingRoutingRawRegisters,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        MAU.Addition.VBECircuit.widenWord_val] using hread
  have hmultiplier : (step before).1 = multiplier := by
    simpa [step, before, doublingRoutingRawRegisters] using
      hpreserve (fun x => x.1) (fun _ _ => by
        rfl)
  have haccumulator : (step before).2.1 = accumulator := by
    simpa [step, before, doublingRoutingRawRegisters] using
      hpreserve (fun x => x.2.1) (fun _ _ => by
        rfl)
  have hmultiplicand : (step before).2.2.1.multiplicand = source := by
    simpa [step, before, doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using
      hpreserve (fun x => x.2.2.1.multiplicand) (fun _ _ => by
        rfl)
  have hactive : (step before).2.2.1.arithmetic.activeSource =
      MAU.Addition.VBECircuit.widenWord params.width (0 : Word) := by
    simpa [step, before, doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.activeSource) (fun _ _ => by
        rfl)
  have hcarry : (step before).2.2.1.arithmetic.carry = false := by
    simpa [step, before, doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.carry) (fun _ _ => by
        rfl)
  have hparked : (step before).2.2.1.arithmetic.parkedSource =
      (params.modulus.val : Word) := by
    simpa [step, before, doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.parkedSource) (fun _ _ => by
        rfl)
  have hcarryWork : (step before).2.2.1.arithmetic.carryWork =
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
        (MAU.Addition.VBECircuit.AdderWidth params.width) := by
    simpa [step, before, doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.carryWork) (fun _ _ => by
        rfl)
  have hflag : (step before).2.2.1.arithmetic.reductionFlag = flag := by
    simpa [step, before, doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      hpreserve (fun x => x.2.2.1.arithmetic.reductionFlag) (fun _ _ => by
        rfl)
  have hwork : (step before).2.2.2 = false := by
    simpa [step, before, doublingRoutingRawRegisters] using
      hpreserve (fun x => x.2.2.2) (fun _ _ => by
        rfl)
  change step before = _
  apply Prod.ext
  · exact hmultiplier
  · apply Prod.ext
    · exact haccumulator
    · apply Prod.ext
      · apply inPlaceRegisters_ext
        · exact hmultiplicand
        · apply additionRegisters_ext
          · exact hactive
          · exact htarget
          · exact hcarry
          · exact hparked
          · exact hcarryWork
          · exact hflag
      · exact hwork

private lemma rawDoublingReductionStep_routing
    (multiplier accumulator source x : Word)
    (hx : x.val < params.modulus.val) :
    rawUncontrolledAddStep
        (doublingWideRawRegisters multiplier accumulator source
          (doubledWideWord x) false false) =
      doublingRoutingRawRegisters multiplier accumulator source
        (((2 * x.val) % params.modulus.val : Nat) : Word)
        (decide (params.modulus.val ≤ 2 * x.val)) := by
  let raw := doubledWideWord x
  let reduced : Nat := raw.val % params.modulus.val
  let reducedLow : Word := (reduced : Word)
  let flag := decide (params.modulus.val ≤ raw.val)
  have hraw : raw.val < 2 * params.modulus.val := by
    simp only [raw, doubledWideWord_val]
    omega
  have hreduced : reduced < 2 ^ params.width := by
    exact (Nat.mod_lt raw.val params.modulusPos).trans modulus_lt_capacity
  have hwiden :
      MAU.Addition.VBECircuit.widenWord params.width reducedLow =
        (reduced : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth params.width)) := by
    simpa only [reducedLow] using
      MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
        params.width reduced hreduced
  let beforeWork :=
    MAU.Multiplication.Accumulate.VBECircuit.workspaceState params.width
      source 0 (params.modulus.val : Word) raw false
  let afterWork :=
    MAU.Multiplication.Accumulate.VBECircuit.workspaceState params.width
      source 0 (params.modulus.val : Word)
      (MAU.Addition.VBECircuit.widenWord params.width reducedLow) flag
  have hstep :
      MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
          params.width params.modulus.val beforeWork = afterWork := by
    apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
      params.width).injective
    change
      (source,
          MAU.Addition.VBECircuit.modularAddStep params.width
            params.modulus.val
            (MAU.Addition.VBECircuit.sourceSwapCleanState params.width
              0 (params.modulus.val : Word) raw false)) =
        (source,
          MAU.Addition.VBECircuit.sourceSwapCleanState params.width
            0 (params.modulus.val : Word)
            (MAU.Addition.VBECircuit.widenWord params.width reducedLow) flag)
    rw [MAU.Addition.VBECircuit.modularAddStep_zeroSource_reduceOnceEndpoint
      params.width params.modulus.val raw params.modulusPos
      modulus_lt_capacity hraw]
    simp only [reduced, flag, hwiden]
  rw [rawUncontrolledAddStep_eq_liftedModularAdd]
  change
    (multiplier, (accumulator,
      (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
        params.width params.modulus.val beforeWork, false))) = _
  rw [hstep]
  simp [afterWork, doublingRoutingRawRegisters,
    reducedLow, reduced, raw, flag, doubledWideWord_val]

private lemma reducedDoubling_lowBit
    (x : Word) (hx : x.val < params.modulus.val) :
    ((((2 * x.val) % params.modulus.val : Nat) : Word).val).testBit 0 =
      decide (params.modulus.val ≤ 2 * x.val) := by
  have hraw : 2 * x.val < 2 * params.modulus.val := by omega
  have hreduced : (2 * x.val) % params.modulus.val < 2 ^ params.width :=
    (Nat.mod_lt _ params.modulusPos).trans modulus_lt_capacity
  rw [ZMod.val_natCast_of_lt hreduced]
  by_cases hreduce : params.modulus.val ≤ 2 * x.val
  · have hsub : 2 * x.val - params.modulus.val < params.modulus.val := by
      omega
    rw [Nat.mod_eq_sub_mod hreduce, Nat.mod_eq_of_lt hsub]
    rcases primeModulus_odd with ⟨k, hk⟩
    have hform :
        2 * x.val - params.modulus.val =
          2 * (x.val - k - 1) + 1 := by
      omega
    simp [hreduce, hform, Nat.testBit_zero]
  · have hlt : 2 * x.val < params.modulus.val := Nat.lt_of_not_ge hreduce
    rw [Nat.mod_eq_of_lt hlt]
    simp [hreduce, Nat.testBit_zero]

private lemma rawDoublingCleanupStep_routing
    (multiplier accumulator reduced : Word) (flag : Bool)
    (hbit : reduced.val.testBit 0 = flag) :
    rawDoublingCleanupStep
        (doublingRoutingRawRegisters multiplier accumulator reduced 0 flag) =
      doublingRoutingRawRegisters multiplier accumulator reduced 0 false := by
  have hcontrol :
      (rawInPlaceMultiplicandBit doublingLowBit).get
          (doublingRoutingRawRegisters multiplier accumulator reduced 0 flag) =
        flag := by
    rw [rawInPlaceMultiplicandBit_get]
    change reduced.val.testBit 0 = flag
    exact hbit
  change EncodedBit.cnotStep
      (rawInPlaceMultiplicandBit doublingLowBit)
      rawDoublingReductionFlagBit
      (doublingRoutingRawRegisters multiplier accumulator reduced 0 flag) = _
  unfold EncodedBit.cnotStep
  rw [hcontrol]
  cases flag
  · rfl
  · simp only [↓reduceIte]
    simp [rawDoublingReductionFlagBit, rawInPlaceBit,
      MAU.Multiplication.Accumulate.VBECircuit.reductionFlagBit,
      MAU.Multiplication.Accumulate.VBECircuit.liftArithmeticBit,
      MAU.Multiplication.Accumulate.VBECircuit.registersEquiv,
      MAU.Addition.VBECircuit.reductionFlagBit,
      MAU.Addition.VBECircuit.registersEquiv,
      EncodedBit.relabel, BinaryLabelEncoding.prodLeftBit,
      BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.boolBit,
      doublingRoutingRawRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState]

set_option exponentiation.threshold 2048 in
/-- Actual shift/reduce source-doubling circuit in the common carrier. -/
def doublingCircuit : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty doublingGates

/-- Raw action of the literal shift/reduce source-doubling circuit. -/
def rawDoublingStep : RawRegisters → RawRegisters :=
  fun x => rawDoublingCleanupStep
    (rawDoublingSwapStep
      (rawUncontrolledAddStep
        (rawDoublingShiftStep (rawDoublingSwapStep x))))

/-- The concrete swap/shift/reduce/swap/cleanup fold doubles one canonical
source residue while returning every arithmetic and shared work bit clean. -/
private lemma rawDoublingStep_routing
    (multiplier accumulator source : Word)
    (hsource : source.val < params.modulus.val) :
    rawDoublingStep
        (doublingRoutingRawRegisters multiplier accumulator source 0 false) =
      doublingRoutingRawRegisters multiplier accumulator
        ((((2 * source.val) % params.modulus.val : Nat) : Word)) 0 false := by
  unfold rawDoublingStep
  rw [rawDoublingSwapStep_routing multiplier accumulator source 0 false]
  rw [rawDoublingShiftStep_routing multiplier accumulator 0 source false]
  rw [rawDoublingReductionStep_routing multiplier accumulator 0 source hsource]
  rw [rawDoublingSwapStep_routing multiplier accumulator 0
    (((2 * source.val) % params.modulus.val : Nat) : Word)
    (decide (params.modulus.val ≤ 2 * source.val))]
  exact rawDoublingCleanupStep_routing multiplier accumulator
    (((2 * source.val) % params.modulus.val : Nat) : Word)
    (decide (params.modulus.val ≤ 2 * source.val))
    (reducedDoubling_lowBit source hsource)

/-- The concatenated shift/reduce source list has its displayed raw fold. -/
lemma doublingGates_stepList (x : RawRegisters) :
    EncodedBit.GateSpec.stepList doublingGates x = rawDoublingStep x := by
  simp only [doublingGates, EncodedBit.GateSpec.stepList_append]
  rfl

/-- Named action of the actual source-doubling circuit. -/
def doublingStep : Registers → Registers :=
  fun x => registersEquiv.symm (rawDoublingStep (registersEquiv x))

/-- On clean semantic data, the literal width-neutral circuit doubles the
stored source residue modulo the configured odd modulus. -/
lemma doublingStep_cleanEndpoint (x : Data) :
    doublingStep (cleanRegisters x) =
      cleanRegisters (Data.doubleMultiplicand x) := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  let source : Word := (x.multiplicand.val : Word)
  have hsourceVal : source.val = x.multiplicand.val := by
    simpa only [source] using canonicalWord_val x.multiplicand
  have hsource : source.val < params.modulus.val := by
    rw [hsourceVal]
    exact ZMod.val_lt x.multiplicand
  apply registersEquiv.injective
  change rawDoublingStep (registersEquiv (cleanRegisters x)) = _
  have hinput : registersEquiv (cleanRegisters x) =
      doublingRoutingRawRegisters
        (x.multiplier.val : Word) (x.accumulator.val : Word) source 0 false :=
    rfl
  rw [hinput, rawDoublingStep_routing _ _ source hsource]
  rw [hsourceVal]
  have hmultiplicandMod :
      x.multiplicand.val % params.modulus.val = x.multiplicand.val :=
    Nat.mod_eq_of_lt (ZMod.val_lt x.multiplicand)
  have hdoubleVal :
      (2 * x.multiplicand).val =
        (2 * x.multiplicand.val) % params.modulus.val := by
    calc
      (2 * x.multiplicand).val =
          ((2 % params.modulus.val) *
            (x.multiplicand.val % params.modulus.val)) %
              params.modulus.val := by
        rw [ZMod.val_mul,
          ZMod.val_two_eq_two_mod params.modulus.val, hmultiplicandMod]
      _ = (2 * x.multiplicand.val) % params.modulus.val :=
        (Nat.mul_mod 2 x.multiplicand.val params.modulus.val).symm
  simp [doublingRoutingRawRegisters, cleanRegisters,
    Data.doubleMultiplicand, registersEquiv,
    MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
    MAU.Addition.VBECircuit.sourceSwapCleanState, hdoubleVal]

set_option exponentiation.threshold 2048 in
/-- The literal shift/reduce circuit realizes its named action. -/
lemma doubling_realizes :
    UnitaryCircuit.Realizes encoding doublingCircuit environment doublingStep := by
  have raw : UnitaryCircuit.Realizes rawEncoding doublingCircuit environment rawDoublingStep := by
    unfold doublingCircuit
    exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
      (QubitLayout.canonical _) .empty
      doublingGates doublingGates_stepList
  exact UnitaryCircuit.Realizes.relabel registersEquiv raw

/-- Strict event pool derived from the actual lifted source-doubling circuit. -/
def doublingEventCost : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  doublingCircuit.eventCost

/-- Strict event critical path derived from the actual lifted source-doubling
circuit. -/
def doublingEventDepth :=
  doublingCircuit.eventDepth

/-- Linearizing the doubling event-depth tree recovers its actual event pool. -/
lemma doubling_resourcesFromEventDepth_eq_eventCost :
    doublingCircuit.resourcesFromEventDepth = doublingEventCost := by
  simpa only [doublingEventCost] using
    UnitaryCircuit.resourcesFromEventDepth_eq_eventCost doublingCircuit

/-- Actual selected modular-addition routing for one multiplier bit: exchange
the external accumulator, load the in-place source, run the selected VBE
stage, unload the source, then restore the external accumulator placement. -/
def selectedAddGates (bit : Fin params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  accumulatorSwapGates ++ sourceCopyGates ++ rawStageGates bit ++
    sourceUnloadGates ++ accumulatorSwapGates

/-- Raw folded action of the literal selected-add route. -/
def rawSelectedAddStep (bit : Fin params.width) : RawRegisters → RawRegisters :=
  fun x => rawAccumulatorSwapStep
    (rawSourceCopyStep
      (rawStageStep bit
        (rawSourceCopyStep
          (rawAccumulatorSwapStep x))))

/-- The concatenated selected-add source list has its displayed raw fold. -/
lemma selectedAddGates_stepList (bit : Fin params.width) (x : RawRegisters) :
    EncodedBit.GateSpec.stepList (selectedAddGates bit) x =
      rawSelectedAddStep bit x := by
  unfold selectedAddGates rawSelectedAddStep sourceUnloadGates
  simp only [EncodedBit.GateSpec.stepList_append]
  rfl

/-- Circuit compiled from the literal selected modular-addition route. -/
def selectedAddCircuit (bit : Fin params.width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (selectedAddGates bit)

/-- Full named action of the actual selected modular-addition routing. -/
def selectedAddStep (bit : Fin params.width) : Registers → Registers :=
  fun x => accumulatorSwapStep
    (sourceUnloadStep
      (stageStep bit
        (sourceCopyStep
          (accumulatorSwapStep x))))

/-- The raw selected-add fold is the packed form of the named action. -/
lemma rawSelectedAddStep_registersEquiv (bit : Fin params.width)
    (x : Registers) :
    rawSelectedAddStep bit (registersEquiv x) =
      registersEquiv (selectedAddStep bit x) := by
  unfold selectedAddStep accumulatorSwapStep sourceUnloadStep sourceCopyStep
    stageStep rawSelectedAddStep
  simp only [Equiv.apply_symm_apply]

set_option exponentiation.threshold 2048 in
/-- The composed accumulator-routing and selected-add circuit realizes its
full named action. -/
lemma selectedAdd_realizes (bit : Fin params.width) :
    UnitaryCircuit.Realizes encoding (selectedAddCircuit bit) environment (selectedAddStep bit) :=
      by
  have raw : UnitaryCircuit.Realizes rawEncoding (selectedAddCircuit bit) environment
      (rawSelectedAddStep bit) := by
    unfold selectedAddCircuit
    exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
      (QubitLayout.canonical _) .empty
      (selectedAddGates bit) (selectedAddGates_stepList bit)
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.relabel registersEquiv raw)
  intro x
  unfold selectedAddStep accumulatorSwapStep sourceUnloadStep sourceCopyStep
    stageStep rawSelectedAddStep
  simp only [Equiv.apply_symm_apply]

/-- The selected-add routing preserves the canonical clean workspace and adds
the stored multiplicand exactly when the selected multiplier bit is set. -/
lemma selectedAddStep_cleanEndpoint (bit : Fin params.width) (x : Data) :
    selectedAddStep bit (cleanRegisters x) =
      cleanRegisters (Data.addSelected bit x) := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  let multiplier : Word := (x.multiplier.val : Word)
  let source : Word := (x.multiplicand.val : Word)
  let accumulator : Word := (x.accumulator.val : Word)
  have hmultiplierVal : multiplier.val = x.multiplier.val := by
    simpa only [multiplier] using canonicalWord_val x.multiplier
  have hsourceVal : source.val = x.multiplicand.val := by
    simpa only [source] using canonicalWord_val x.multiplicand
  have haccumulatorVal : accumulator.val = x.accumulator.val := by
    simpa only [accumulator] using canonicalWord_val x.accumulator
  have hsource : source.val < params.modulus.val := by
    rw [hsourceVal]
    exact ZMod.val_lt x.multiplicand
  have haccumulator : accumulator.val < params.modulus.val := by
    rw [haccumulatorVal]
    exact ZMod.val_lt x.accumulator
  have hinput : cleanRegisters x =
      routingRegisters multiplier source accumulator 0 0 := by
    simpa only [multiplier, source, accumulator] using cleanRegisters_eq_routing x
  have hswapInitial :
      accumulatorSwapStep
          (routingRegisters multiplier source accumulator 0 0) =
        routingRegisters multiplier source 0 0 accumulator :=
    accumulatorSwapStep_routing multiplier source accumulator 0 0
  have hcopyInitial :
      sourceCopyStep (routingRegisters multiplier source 0 0 accumulator) =
        routingRegisters multiplier source 0 source accumulator :=
    sourceCopyStep_routing_zero multiplier source 0 accumulator
  cases hselected : multiplier.val.testBit bit.val with
  | false =>
      have hselectedData : x.multiplier.val.testBit bit.val = false := by
        simpa [hmultiplierVal] using hselected
      have hstage :
          stageStep bit
              (routingRegisters multiplier source 0 source accumulator) =
            routingRegisters multiplier source 0 source accumulator := by
        apply stageStep_eq_self_of_multiplier_false bit
        simpa [routingRegisters, routingRawRegisters, registersEquiv] using hselected
      have hunload :
          sourceUnloadStep
              (routingRegisters multiplier source 0 source accumulator) =
            routingRegisters multiplier source 0 0 accumulator :=
        sourceUnloadStep_routing_source multiplier source 0 accumulator
      have hswapFinal :
          accumulatorSwapStep
              (routingRegisters multiplier source 0 0 accumulator) =
            routingRegisters multiplier source accumulator 0 0 :=
        accumulatorSwapStep_routing multiplier source 0 0 accumulator
      have houtput : cleanRegisters (Data.addSelected bit x) =
          routingRegisters multiplier source accumulator 0 0 := by
        simpa [Data.addSelected, hselectedData, multiplier, source, accumulator] using
          cleanRegisters_eq_routing (Data.addSelected bit x)
      calc
        selectedAddStep bit (cleanRegisters x) =
            selectedAddStep bit
              (routingRegisters multiplier source accumulator 0 0) := by
          rw [hinput]
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (stageStep bit
                (sourceCopyStep
                  (accumulatorSwapStep
                    (routingRegisters multiplier source accumulator 0 0))))) := rfl
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (stageStep bit
                (sourceCopyStep
                  (routingRegisters multiplier source 0 0 accumulator)))) := by
          rw [hswapInitial]
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (stageStep bit
                (routingRegisters multiplier source 0 source accumulator))) := by
          rw [hcopyInitial]
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (routingRegisters multiplier source 0 source accumulator)) := by
          rw [hstage]
        _ = accumulatorSwapStep
            (routingRegisters multiplier source 0 0 accumulator) := by
          rw [hunload]
        _ = routingRegisters multiplier source accumulator 0 0 := by
          rw [hswapFinal]
        _ = cleanRegisters (Data.addSelected bit x) := houtput.symm
  | true =>
      let sum : ZMod params.modulus.val :=
        x.accumulator + x.multiplicand
      let result : Word :=
        ((source.val + accumulator.val) %
          params.modulus.val : Word)
      have hresultBound :
          (source.val + accumulator.val) % params.modulus.val <
            2 ^ params.width :=
        (Nat.mod_lt _ params.modulusPos).trans
          modulus_lt_capacity
      have hresultSum : result = (sum.val : Word) := by
        apply ZMod.val_injective
        calc
          result.val =
              (source.val + accumulator.val) %
                params.modulus.val := by
            dsimp [result]
            exact ZMod.val_natCast_of_lt hresultBound
          _ = (x.multiplicand.val + x.accumulator.val) %
                params.modulus.val := by
            rw [hsourceVal, haccumulatorVal]
          _ = sum.val := by
            simpa [sum, Nat.add_comm] using
              (ZMod.val_add x.accumulator x.multiplicand).symm
          _ = (sum.val : Word).val :=
            (canonicalWord_val sum).symm
      have hselectedData : x.multiplier.val.testBit bit.val = true := by
        simpa [hmultiplierVal] using hselected
      have hstage :
          stageStep bit
              (routingRegisters multiplier source 0 source accumulator) =
            uncontrolledAddStep
              (routingRegisters multiplier source 0 source accumulator) := by
        apply stageStep_eq_uncontrolledAddStep_of_multiplier_true_work_clean bit
        · simpa [routingRegisters, routingRawRegisters, registersEquiv] using hselected
        · simp [routingRegisters, routingRawRegisters, registersEquiv]
      have hadd :
          uncontrolledAddStep
              (routingRegisters multiplier source 0 source accumulator) =
            routingRegisters multiplier source 0 source result := by
        simpa only [result] using
          uncontrolledAddStep_routing multiplier source accumulator
            hsource haccumulator
      have haddSum :
          uncontrolledAddStep
              (routingRegisters multiplier source 0 source accumulator) =
            routingRegisters multiplier source 0 source (sum.val : Word) := by
        calc
          uncontrolledAddStep
              (routingRegisters multiplier source 0 source accumulator) =
            routingRegisters multiplier source 0 source result := hadd
          _ = routingRegisters multiplier source 0 source (sum.val : Word) := by
            rw [hresultSum]
      have hunloadSum :
          sourceUnloadStep
              (routingRegisters multiplier source 0 source (sum.val : Word)) =
            routingRegisters multiplier source 0 0 (sum.val : Word) :=
        sourceUnloadStep_routing_source multiplier source 0 (sum.val : Word)
      have hswapFinalSum :
          accumulatorSwapStep
              (routingRegisters multiplier source 0 0 (sum.val : Word)) =
            routingRegisters multiplier source (sum.val : Word) 0 0 :=
        accumulatorSwapStep_routing multiplier source 0 0 (sum.val : Word)
      have houtput : cleanRegisters (Data.addSelected bit x) =
          routingRegisters multiplier source (sum.val : Word) 0 0 := by
        simpa [Data.addSelected, hselectedData, multiplier, source, sum] using
          cleanRegisters_eq_routing (Data.addSelected bit x)
      calc
        selectedAddStep bit (cleanRegisters x) =
            selectedAddStep bit
              (routingRegisters multiplier source accumulator 0 0) := by
          rw [hinput]
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (stageStep bit
                (sourceCopyStep
                  (accumulatorSwapStep
                    (routingRegisters multiplier source accumulator 0 0))))) := rfl
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (stageStep bit
                (sourceCopyStep
                  (routingRegisters multiplier source 0 0 accumulator)))) := by
          rw [hswapInitial]
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (stageStep bit
                (routingRegisters multiplier source 0 source accumulator))) := by
          rw [hcopyInitial]
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (uncontrolledAddStep
                (routingRegisters multiplier source 0 source accumulator))) := by
          rw [hstage]
        _ = accumulatorSwapStep
            (sourceUnloadStep
              (routingRegisters multiplier source 0 source (sum.val : Word))) := by
          rw [haddSum]
        _ = accumulatorSwapStep
            (routingRegisters multiplier source 0 0 (sum.val : Word)) := by
          rw [hunloadSum]
        _ = routingRegisters multiplier source (sum.val : Word) 0 0 := by
          rw [hswapFinalSum]
        _ = cleanRegisters (Data.addSelected bit x) := houtput.symm

/-- Strict event pool derived from one actual selected-add routing circuit. -/
def selectedAddEventCost (bit : Fin params.width) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (selectedAddCircuit bit).eventCost

/-- Strict event critical path derived from one actual selected-add routing
circuit. -/
def selectedAddEventDepth (bit : Fin params.width) :=
  (selectedAddCircuit bit).eventDepth

/-- Linearizing the selected-add event-depth tree recovers its actual event
pool. -/
lemma selectedAdd_resourcesFromEventDepth_eq_eventCost (bit : Fin params.width) :
    (selectedAddCircuit bit).resourcesFromEventDepth = selectedAddEventCost bit := by
  simpa only [selectedAddEventCost] using
    UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (selectedAddCircuit bit)

/-- One actual variable-multiplication round: selected modular addition then
the actual in-place doubling circuit. The width-indexed fold is assembled by
the subsequent schedule layer. -/
def roundGates (bit : Fin params.width) :
    List (EncodedBit.GateSpec rawEncoding) :=
  selectedAddGates bit ++ doublingGates

/-- Raw folded action of one literal selected-add/doubling round. -/
def rawRoundStep (bit : Fin params.width) : RawRegisters → RawRegisters :=
  fun x => rawDoublingStep (rawSelectedAddStep bit x)

/-- The concatenated round source list has its displayed raw fold. -/
lemma roundGates_stepList (bit : Fin params.width) (x : RawRegisters) :
    EncodedBit.GateSpec.stepList (roundGates bit) x = rawRoundStep bit x := by
  rw [roundGates, EncodedBit.GateSpec.stepList_append,
    selectedAddGates_stepList, doublingGates_stepList]
  rfl

/-- Circuit compiled from the literal selected-add/doubling round. -/
def roundCircuit (bit : Fin params.width) : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (roundGates bit)

/-- Named action of one actual variable-multiplication round. -/
def roundStep (bit : Fin params.width) : Registers → Registers :=
  fun x => doublingStep (selectedAddStep bit x)

/-- The raw round fold is the packed form of the named action. -/
lemma rawRoundStep_registersEquiv (bit : Fin params.width) (x : Registers) :
    rawRoundStep bit (registersEquiv x) = registersEquiv (roundStep bit x) := by
  unfold roundStep doublingStep rawRoundStep
  rw [rawSelectedAddStep_registersEquiv]
  simp only [Equiv.apply_symm_apply]

set_option exponentiation.threshold 2048 in
/-- One actual selected-add/doubling round realizes its named action. -/
lemma roundCircuit_realizes (bit : Fin params.width) :
    UnitaryCircuit.Realizes encoding (roundCircuit bit) environment (roundStep bit) := by
  have raw : UnitaryCircuit.Realizes rawEncoding (roundCircuit bit) environment (rawRoundStep bit)
    := by
    unfold roundCircuit
    exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
      (QubitLayout.canonical _) .empty
      (roundGates bit) (roundGates_stepList bit)
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.relabel registersEquiv raw)
  intro x
  unfold roundStep doublingStep selectedAddStep accumulatorSwapStep
    sourceUnloadStep sourceCopyStep stageStep rawRoundStep rawSelectedAddStep
  simp only [Equiv.apply_symm_apply]

/-- Strict event pool derived from one actual selected-add/doubling round. -/
def roundEventCost (bit : Fin params.width) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (roundCircuit bit).eventCost

/-- Strict event critical path derived from one actual selected-add/doubling
round. -/
def roundEventDepth (bit : Fin params.width) :=
  (roundCircuit bit).eventDepth

/-- Linearizing the round event-depth tree recovers its actual event pool. -/
lemma round_resourcesFromEventDepth_eq_eventCost (bit : Fin params.width) :
    (roundCircuit bit).resourcesFromEventDepth = roundEventCost bit := by
  simpa only [roundEventCost] using
    UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (roundCircuit bit)

end

end VariableModularMul
end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
