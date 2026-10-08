/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.Modular.Division
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Resource

/-!
# Physical workspace for width-parameterized affine point addition

The division product carrier and every later multiplication/addition stage use
one `VariableModularMul.Registers` value. Four thin words retain only values
that must outlive a reset of that carrier. There is no temporal epoch, logical
block bank, wrapper flag, or compatibility addressing layer.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ParameterizedPointAddition
namespace Workspace

open Nat.FixedWidth

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

/-- The one physical variable modular multiply-accumulate carrier. -/
abbrev ProductRegisters := Arithmetic.VariableModularMul.Registers

/-- The four field-width values retained while the product carrier is reset. -/
abbrev ThinRegisters :=
  Word params.width ×
    (Word params.width × (Word params.width × Word params.width))

/-- Public output words together with the control and known-clean padding bit. -/
abbrev OutputRegisters :=
  Word params.width × (Word params.width × (Bool × Bool))

/-- Physical shared point-addition workspace: Kaliski inversion, the one
division/product/addition carrier, four thin saved words, and output suffix. -/
abbrev RawRegisters :=
  Arithmetic.ModularInversion.RawRegisters ×
    (ProductRegisters × (ThinRegisters × OutputRegisters))

/-- The named encoding of the actual shared product carrier. -/
abbrev productEncoding : BinaryLabelEncoding ProductRegisters :=
  Arithmetic.VariableModularMul.encoding

/-- Canonical little-endian encoding of one field-width word. -/
def wordEncoding : BinaryLabelEncoding (Word params.width) :=
  MAU.Inversion.MK.wordEncoding params.width

/-- Exact physical encoding of the four thin retained words. -/
def thinEncoding : BinaryLabelEncoding ThinRegisters :=
  BinaryLabelEncoding.prod wordEncoding
    (BinaryLabelEncoding.prod wordEncoding
      (BinaryLabelEncoding.prod wordEncoding wordEncoding))

/-- Encoding of the retained public-output suffix. -/
def outputEncoding : BinaryLabelEncoding OutputRegisters :=
  BinaryLabelEncoding.prod wordEncoding
    (BinaryLabelEncoding.prod wordEncoding
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool))

/-- Encoding of values retained beside the shared product carrier. -/
def tailEncoding : BinaryLabelEncoding (ThinRegisters × OutputRegisters) :=
  BinaryLabelEncoding.prod thinEncoding outputEncoding

/-- Encoding of the shared product carrier and retained tail. -/
def productTailEncoding :
    BinaryLabelEncoding (ProductRegisters × (ThinRegisters × OutputRegisters)) :=
  BinaryLabelEncoding.prod productEncoding tailEncoding

/-- Complete physical encoding. -/
def rawEncoding : BinaryLabelEncoding RawRegisters :=
  BinaryLabelEncoding.prod Arithmetic.ModularInversion.rawEncoding productTailEncoding

/-- The clean direct product carrier, with all three public field values zero. -/
def blankProductRegisters : ProductRegisters :=
  Arithmetic.VariableModularMul.cleanRegisters
    ({ multiplier := 0, multiplicand := 0, accumulator := 0 } :
      Arithmetic.VariableModularMul.Data)

/-- The four retained field words start clean. -/
def blankThinRegisters : ThinRegisters :=
  (0, (0, (0, 0)))

/-- The retained suffix starts with clean public words and control bits. -/
def blankOutputRegisters : OutputRegisters :=
  (0, (0, (false, false)))

/-- Input-independent clean state of the complete shared workspace. -/
def blankRegisters : RawRegisters :=
  (Arithmetic.ModularInversion.blankRegisters,
    (blankProductRegisters, (blankThinRegisters, blankOutputRegisters)))

/-- Canonical little-endian lens over a fixed-width retained word. -/
def fixedWord : EncodedBit.Word wordEncoding params.width where
  bit := fun bit => BinaryLabelEncoding.finIdentityBit params.width
    (WireAddress.littleEndianWire bit)

@[simp] theorem fixedWord_get (bit : Fin params.width)
    (word : Word params.width) :
    (fixedWord.bit bit).get word = word.val.testBit bit.val := by
  simp [fixedWord, wordEncoding, MAU.Inversion.MK.wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]

theorem fixedWord_pairwise_ne (left right : Fin params.width)
    (hne : left ≠ right) :
    (fixedWord.bit left).wire ≠ (fixedWord.bit right).wire := by
  intro hwire
  apply hne
  exact WireAddress.bitIndex_injective hwire

/-- Read-write port for a standalone retained field-width word. -/
def fixedWordPort : Arithmetic.BlockBank.WordPort wordEncoding params.width where
  word := fixedWord
  read := id
  set := fun _ value => value
  set_read := by intro state; rfl
  read_set := by intro state value; rfl
  set_set := by intro state first second; rfl
  get_bit := fixedWord_get
  pairwise_ne := fixedWord_pairwise_ne
  clear_flip := by intro bit state; rfl

/-- The numerator retained after division is reversed. -/
def numeratorScratchThinPort :
    Arithmetic.BlockBank.WordPort thinEncoding params.width :=
  fixedWordPort.prodLeft
    (BinaryLabelEncoding.prod wordEncoding
      (BinaryLabelEncoding.prod wordEncoding wordEncoding))

/-- The quotient/slope retained before the division workspace is reversed. -/
def slopeThinPort : Arithmetic.BlockBank.WordPort thinEncoding params.width :=
  Arithmetic.BlockBank.WordPort.prodRight wordEncoding
    (fixedWordPort.prodLeft (BinaryLabelEncoding.prod wordEncoding wordEncoding))

/-- The retained affine x-coordinate scratch. -/
def xThinPort : Arithmetic.BlockBank.WordPort thinEncoding params.width :=
  Arithmetic.BlockBank.WordPort.prodRight wordEncoding
    (Arithmetic.BlockBank.WordPort.prodRight wordEncoding
      (fixedWordPort.prodLeft wordEncoding))

/-- The retained affine y-coordinate scratch. -/
def yThinPort : Arithmetic.BlockBank.WordPort thinEncoding params.width :=
  Arithmetic.BlockBank.WordPort.prodRight wordEncoding
    (Arithmetic.BlockBank.WordPort.prodRight wordEncoding
      (Arithmetic.BlockBank.WordPort.prodRight wordEncoding fixedWordPort))

/-- Public output x-coordinate in the retained suffix. -/
def outputXPort : Arithmetic.BlockBank.WordPort outputEncoding params.width :=
  fixedWordPort.prodLeft
    (BinaryLabelEncoding.prod wordEncoding
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool))

/-- Public output y-coordinate in the retained suffix. -/
def outputYPort : Arithmetic.BlockBank.WordPort outputEncoding params.width :=
  Arithmetic.BlockBank.WordPort.prodRight wordEncoding
    (fixedWordPort.prodLeft
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool))

/-- Public control bit retained outside every arithmetic carrier. -/
def outputControlBit : EncodedBit outputEncoding :=
  BinaryLabelEncoding.prodRightBit wordEncoding
    (BinaryLabelEncoding.prod wordEncoding
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit wordEncoding
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- Known-clean high bit used when a field word is widened for Kaliski input. -/
def outputFlagBit : EncodedBit outputEncoding :=
  BinaryLabelEncoding.prodRightBit wordEncoding
    (BinaryLabelEncoding.prod wordEncoding
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit wordEncoding
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- Lift a product-carrier word to the complete physical workspace. -/
def productWord {wordWidth : Nat}
    (word : EncodedBit.Word productEncoding wordWidth) :
    EncodedBit.Word rawEncoding wordWidth where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding
      (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
        (word.bit bit))

/-- Lift a thin retained word to the complete physical workspace. -/
def thinWord
    (word : EncodedBit.Word thinEncoding params.width) :
    EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding
      (BinaryLabelEncoding.prodRightBit productEncoding tailEncoding
        (BinaryLabelEncoding.prodLeftBit thinEncoding outputEncoding
          (word.bit bit)))

/-- Lift an output-suffix word to the complete physical workspace. -/
def outputWord
    (word : EncodedBit.Word outputEncoding params.width) :
    EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding
      (BinaryLabelEncoding.prodRightBit productEncoding tailEncoding
        (BinaryLabelEncoding.prodRightBit thinEncoding outputEncoding
          (word.bit bit)))

/-- Lift an inversion-owned word to the complete physical workspace. -/
def inversionWord {wordWidth : Nat}
    (word : EncodedBit.Word Arithmetic.ModularInversion.rawEncoding wordWidth) :
    EncodedBit.Word rawEncoding wordWidth where
  bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding (word.bit bit)

/-- Lift an inversion-owned word port to the complete shared workspace. -/
def inversionPort {wordWidth : Nat}
    (port : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding wordWidth) :
    Arithmetic.BlockBank.WordPort rawEncoding wordWidth :=
  port.prodLeft productTailEncoding

/-- The preserved Kaliski denominator copy on the complete workspace. -/
def denominatorPreservedPort :
    Arithmetic.BlockBank.WordPort rawEncoding
      Arithmetic.ModularInversion.arithmeticWidth :=
  inversionPort Arithmetic.ModularInversion.preservedInputPort

/-- The Kaliski working denominator copy on the complete workspace. -/
def denominatorWorkingPort :
    Arithmetic.BlockBank.WordPort rawEncoding
      Arithmetic.ModularInversion.arithmeticWidth :=
  inversionPort Arithmetic.ModularInversion.workingInputPort

/-- Lift one direct product-carrier bit to the complete workspace. -/
def productBit (bit : EncodedBit productEncoding) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
    productTailEncoding
    (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding bit)

/-- Lift one retained-output bit to the complete workspace. -/
def outputBit (bit : EncodedBit outputEncoding) : EncodedBit rawEncoding :=
  BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
    productTailEncoding
    (BinaryLabelEncoding.prodRightBit productEncoding tailEncoding
      (BinaryLabelEncoding.prodRightBit thinEncoding outputEncoding bit))

/-- The actual multiplier word in the shared product carrier. -/
def productMultiplierWord : EncodedBit.Word productEncoding params.width where
  bit := Arithmetic.VariableModularMul.multiplierBit

/-- The actual in-place multiplicand word in the shared product carrier. -/
def productMultiplicandWord : EncodedBit.Word productEncoding params.width where
  bit := Arithmetic.VariableModularMul.inPlaceMultiplicandBit

/-- The actual external accumulator word in the shared product carrier. -/
def productAccumulatorWord : EncodedBit.Word productEncoding params.width where
  bit := Arithmetic.VariableModularMul.accumulatorBit

/-- Structural multiplier port on the direct shared product carrier. -/
def productMultiplierPort :
    Arithmetic.BlockBank.WordPort productEncoding params.width :=
  Arithmetic.ModularDivision.productNumeratorPort

/-- Read the direct shared product multiplicand. -/
def readProductMultiplicand (state : ProductRegisters) : Word params.width :=
  ⟨state.inPlace.multiplicand.val,
    ZMod.val_lt state.inPlace.multiplicand⟩

/-- Replace only the direct shared product multiplicand. -/
def setProductMultiplicand (state : ProductRegisters) (value : Word params.width) :
    ProductRegisters :=
  { state with inPlace :=
      { state.inPlace with
        multiplicand := (value.val : Arithmetic.VariableModularMul.Word) } }

/-- Structural multiplicand port on the direct shared product carrier. -/
def productMultiplicandPort :
    Arithmetic.BlockBank.WordPort productEncoding params.width where
  word := productMultiplicandWord
  read := readProductMultiplicand
  set := setProductMultiplicand
  set_read := by
    intro state
    rcases state with ⟨multiplier, accumulator, inPlace, work⟩
    rcases inPlace with ⟨multiplicand, arithmetic⟩
    simp [setProductMultiplicand, readProductMultiplicand]
  read_set := by
    intro state value
    cases state
    apply Fin.ext
    simp [setProductMultiplicand, readProductMultiplicand,
      Nat.mod_eq_of_lt value.isLt]
  set_set := by
    intro state first second
    cases state
    rfl
  get_bit := by
    intro bit state
    exact Arithmetic.VariableModularMul.inPlaceMultiplicandBit_get bit state
  pairwise_ne := Arithmetic.VariableModularMul.inPlaceMultiplicandBit_pairwise_ne
  clear_flip := by
    intro bit state
    rcases state with ⟨multiplier, accumulator, inPlace, work⟩
    rcases inPlace with ⟨multiplicand, arithmetic⟩
    rfl

/-- Read the direct shared product accumulator. -/
def readProductAccumulator (state : ProductRegisters) : Word params.width :=
  ⟨state.accumulator.val, ZMod.val_lt state.accumulator⟩

/-- Replace only the direct shared product accumulator. -/
def setProductAccumulator (state : ProductRegisters) (value : Word params.width) :
    ProductRegisters :=
  { state with accumulator := (value.val : Arithmetic.VariableModularMul.Word) }

theorem productAccumulatorBit_pairwise_ne
    (left right : Fin params.width) (hne : left ≠ right) :
    (Arithmetic.VariableModularMul.accumulatorBit left).wire ≠
      (Arithmetic.VariableModularMul.accumulatorBit right).wire := by
  intro hwire
  apply Arithmetic.VariableModularMul.rawAccumulator_pairwise_ne left right hne
  apply Fin.ext
  simpa only [Arithmetic.VariableModularMul.accumulatorBit,
    EncodedBit.relabel] using congrArg Fin.val hwire

/-- Structural accumulator port on the direct shared product carrier. -/
def productAccumulatorPort :
    Arithmetic.BlockBank.WordPort productEncoding params.width where
  word := productAccumulatorWord
  read := readProductAccumulator
  set := setProductAccumulator
  set_read := by
    intro state
    rcases state with ⟨multiplier, accumulator, inPlace, work⟩
    simp [setProductAccumulator, readProductAccumulator]
  read_set := by
    intro state value
    cases state
    apply Fin.ext
    simp [setProductAccumulator, readProductAccumulator,
      Nat.mod_eq_of_lt value.isLt]
  set_set := by
    intro state first second
    cases state
    rfl
  get_bit := by
    intro bit state
    change (Arithmetic.VariableModularMul.accumulatorBit bit).get state =
      state.accumulator.val.testBit bit.val
    change (Arithmetic.VariableModularMul.rawAccumulatorBit bit).get
        (Arithmetic.VariableModularMul.registersEquiv state) = _
    exact Arithmetic.VariableModularMul.rawAccumulatorBit_get bit
      (Arithmetic.VariableModularMul.registersEquiv state)
  pairwise_ne := productAccumulatorBit_pairwise_ne
  clear_flip := by
    intro bit state
    rcases state with ⟨multiplier, accumulator, inPlace, work⟩
    rfl

/-- Lift a product-carrier port to the complete shared workspace. -/
def productPort
    (port : Arithmetic.BlockBank.WordPort productEncoding params.width) :
    Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  Arithmetic.BlockBank.WordPort.prodRight Arithmetic.ModularInversion.rawEncoding
    (port.prodLeft tailEncoding)

/-- Lift a thin saved-word port to the complete shared workspace. -/
def thinPort
    (port : Arithmetic.BlockBank.WordPort thinEncoding params.width) :
    Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  Arithmetic.BlockBank.WordPort.prodRight Arithmetic.ModularInversion.rawEncoding
    (Arithmetic.BlockBank.WordPort.prodRight productEncoding
      (port.prodLeft outputEncoding))

/-- Full-workspace port of the retained division numerator. -/
def numeratorScratchPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  thinPort numeratorScratchThinPort

/-- Full-workspace port of the retained affine slope. -/
def slopePort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  thinPort slopeThinPort

/-- Full-workspace port of the retained affine x-coordinate. -/
def xPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  thinPort xThinPort

/-- Full-workspace port of the retained affine y-coordinate. -/
def yPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  thinPort yThinPort

/-- Lift an output-suffix port to the complete shared workspace. -/
def outputPort
    (port : Arithmetic.BlockBank.WordPort outputEncoding params.width) :
    Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  Arithmetic.BlockBank.WordPort.prodRight Arithmetic.ModularInversion.rawEncoding
    (Arithmetic.BlockBank.WordPort.prodRight productEncoding
      (Arithmetic.BlockBank.WordPort.prodRight thinEncoding port))

/-- Lift the retained output x-coordinate port to the complete workspace. -/
def retainedOutputXPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  outputPort outputXPort

/-- Lift the retained output y-coordinate port to the complete workspace. -/
def retainedOutputYPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  outputPort outputYPort

/-- The retained output control on the complete workspace. -/
def retainedOutputControlBit : EncodedBit rawEncoding :=
  outputBit outputControlBit

/-- The retained high padding flag on the complete workspace. -/
def retainedOutputFlagBit : EncodedBit rawEncoding :=
  outputBit outputFlagBit

/-- The division numerator is the shared product multiplier. -/
def divisionNumeratorWord : EncodedBit.Word rawEncoding params.width :=
  productWord productMultiplierWord

/-- The division inverse is loaded into this same shared multiplicand word. -/
def divisionProductTargetWord : EncodedBit.Word rawEncoding params.width :=
  productWord productMultiplicandWord

/-- The division quotient is the shared product accumulator. -/
def divisionQuotientWord : EncodedBit.Word rawEncoding params.width :=
  productWord productAccumulatorWord

/-- The division numerator is the shared product multiplier port. -/
def divisionNumeratorPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  productPort productMultiplierPort

/-- The division product target is the shared product multiplicand port. -/
def divisionProductTargetPort :
    Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  productPort productMultiplicandPort

/-- The division quotient is the shared product accumulator port. -/
def divisionQuotientPort : Arithmetic.BlockBank.WordPort rawEncoding params.width :=
  productPort productAccumulatorPort

/-- Full-carrier views for values that survive a product-carrier reset. -/
def numeratorScratchWord : EncodedBit.Word rawEncoding params.width :=
  thinWord numeratorScratchThinPort.word

def slopeWord : EncodedBit.Word rawEncoding params.width :=
  thinWord slopeThinPort.word

def xWord : EncodedBit.Word rawEncoding params.width :=
  thinWord xThinPort.word

def yWord : EncodedBit.Word rawEncoding params.width :=
  thinWord yThinPort.word

/-- The product multiplier and division numerator are literally the same
physical word, not two logical blocks joined by an epoch API. -/
theorem divisionNumeratorWord_eq_productMultiplierWord :
    divisionNumeratorWord = productWord productMultiplierWord :=
  rfl

/-- The product accumulator and division quotient are literally the same
physical word. -/
theorem divisionQuotientWord_eq_productAccumulatorWord :
    divisionQuotientWord = productWord productAccumulatorWord :=
  rfl

/-- The public division numerator has no second carrier: it is the product
multiplier port on this one physical workspace. -/
theorem divisionNumeratorPort_eq_productMultiplierPort :
    divisionNumeratorPort = productPort productMultiplierPort :=
  rfl

/-- The public division quotient has no second carrier: it is the product
accumulator port on this one physical workspace. -/
theorem divisionQuotientPort_eq_productAccumulatorPort :
    divisionQuotientPort = productPort productAccumulatorPort :=
  rfl

/-- Value-preserving transport from a field word to the tail-successor Kaliski
input width. -/
def zeroExtendWord (value : Word params.width) :
    Word Arithmetic.ModularInversion.arithmeticWidth :=
  ⟨value.val, by
    rw [Arithmetic.ModularInversion.arithmeticWidth_eq]
    exact value.isLt⟩

@[simp] theorem zeroExtendWord_val (value : Word params.width) :
    (zeroExtendWord value).val = value.val :=
  rfl

/-- Any product-carrier wire is physically disjoint from any thin saved word. -/
theorem product_thin_cross_ne
    (productBit : EncodedBit productEncoding)
    (thinBit : EncodedBit thinEncoding) :
    (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding
      (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding productBit)).wire ≠
      (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
        productTailEncoding
        (BinaryLabelEncoding.prodRightBit productEncoding tailEncoding
          (BinaryLabelEncoding.prodLeftBit thinEncoding outputEncoding thinBit))).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne
    Arithmetic.ModularInversion.rawEncoding
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    productEncoding tailEncoding
    (BinaryLabelEncoding.prodLeftBit thinEncoding outputEncoding thinBit)
    productBit).symm

/-- Any full-workspace product port is physically disjoint from any retained
thin-word port. -/
theorem productPort_thinPort_cross_ne
    (product : Arithmetic.BlockBank.WordPort productEncoding params.width)
    (thin : Arithmetic.BlockBank.WordPort thinEncoding params.width)
    (productBit thinBit : Fin params.width) :
    ((productPort product).word.bit productBit).wire ≠
      ((thinPort thin).word.bit thinBit).wire := by
  exact product_thin_cross_ne (product.word.bit productBit) (thin.word.bit thinBit)

/-- The direct multiplier and in-place multiplicand are different physical
words of the one shared product carrier. -/
theorem productMultiplier_productMultiplicand_cross_ne
    (left right : Fin params.width) :
    ((productPort productMultiplierPort).word.bit left).wire ≠
      ((productPort productMultiplicandPort).word.bit right).wire := by
  change
    (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding
      (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
        (Arithmetic.VariableModularMul.multiplierBit left))).wire ≠
      (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
        productTailEncoding
        (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
          (Arithmetic.VariableModularMul.inPlaceMultiplicandBit right))).wire
  apply EncodedBit.GateSpec.prodRightWire_ne
    Arithmetic.ModularInversion.rawEncoding
  apply EncodedBit.GateSpec.prodLeftWire_ne tailEncoding
  exact Arithmetic.VariableModularMul.multiplierBit_inPlaceMultiplicandBit_ne
    left right

/-- The direct multiplier and external accumulator are different physical
words of the one shared product carrier. -/
theorem productMultiplier_productAccumulator_cross_ne
    (left right : Fin params.width) :
    ((productPort productMultiplierPort).word.bit left).wire ≠
      ((productPort productAccumulatorPort).word.bit right).wire := by
  change
    (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding
      (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
        (Arithmetic.VariableModularMul.multiplierBit left))).wire ≠
      (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
        productTailEncoding
        (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
          (Arithmetic.VariableModularMul.accumulatorBit right))).wire
  apply EncodedBit.GateSpec.prodRightWire_ne
    Arithmetic.ModularInversion.rawEncoding
  apply EncodedBit.GateSpec.prodLeftWire_ne tailEncoding
  intro hwire
  have hraw :
      (Arithmetic.VariableModularMul.rawMultiplierBit left).wire ≠
        (Arithmetic.VariableModularMul.rawAccumulatorBit right).wire := by
    exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      Arithmetic.VariableModularMul.wordEncoding
      Arithmetic.VariableModularMul.accumulatorSuffixEncoding
      (BinaryLabelEncoding.prodLeftBit Arithmetic.VariableModularMul.wordEncoding
        Arithmetic.VariableModularMul.inPlaceWithWorkEncoding
        (PlainAdder.Schedule.PowerOfTwo.wordBit params.width right))
      (PlainAdder.Schedule.PowerOfTwo.wordBit params.width left)).symm
  apply hraw
  apply Fin.ext
  simpa only [Arithmetic.VariableModularMul.multiplierBit,
    Arithmetic.VariableModularMul.accumulatorBit, EncodedBit.relabel] using
    congrArg Fin.val hwire

/-- The in-place multiplicand and external accumulator are different physical
words of the one shared product carrier. -/
theorem productMultiplicand_productAccumulator_cross_ne
    (left right : Fin params.width) :
    ((productPort productMultiplicandPort).word.bit left).wire ≠
      ((productPort productAccumulatorPort).word.bit right).wire := by
  change
    (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding
      (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
        (Arithmetic.VariableModularMul.inPlaceMultiplicandBit left))).wire ≠
      (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
        productTailEncoding
        (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
          (Arithmetic.VariableModularMul.accumulatorBit right))).wire
  apply EncodedBit.GateSpec.prodRightWire_ne
    Arithmetic.ModularInversion.rawEncoding
  apply EncodedBit.GateSpec.prodLeftWire_ne tailEncoding
  intro hwire
  have hraw :
      (Arithmetic.VariableModularMul.rawAccumulatorBit right).wire ≠
        (Arithmetic.VariableModularMul.rawInPlaceMultiplicandBit left).wire := by
    have hinner :
        (BinaryLabelEncoding.prodLeftBit Arithmetic.VariableModularMul.wordEncoding
          Arithmetic.VariableModularMul.inPlaceWithWorkEncoding
          (PlainAdder.Schedule.PowerOfTwo.wordBit params.width right)).wire ≠
          (BinaryLabelEncoding.prodRightBit Arithmetic.VariableModularMul.wordEncoding
            Arithmetic.VariableModularMul.inPlaceWithWorkEncoding
            (BinaryLabelEncoding.prodLeftBit
              Arithmetic.VariableModularMul.inPlaceEncoding BinaryLabelEncoding.bool
              (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
                params.width left))).wire :=
      (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
        Arithmetic.VariableModularMul.wordEncoding
        Arithmetic.VariableModularMul.inPlaceWithWorkEncoding
        (BinaryLabelEncoding.prodLeftBit
          Arithmetic.VariableModularMul.inPlaceEncoding BinaryLabelEncoding.bool
          (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
            params.width left))
        (PlainAdder.Schedule.PowerOfTwo.wordBit params.width right)).symm
    exact EncodedBit.GateSpec.prodRightWire_ne
      Arithmetic.VariableModularMul.wordEncoding hinner
  apply hraw
  apply Fin.ext
  simpa only [Arithmetic.VariableModularMul.inPlaceMultiplicandBit,
    Arithmetic.VariableModularMul.accumulatorBit,
    Arithmetic.VariableModularMul.rawInPlaceMultiplicandBit,
    Arithmetic.VariableModularMul.rawInPlaceBit,
    Arithmetic.VariableModularMul.accumulatorSuffixEncoding,
    Arithmetic.VariableModularMul.inPlaceWithWorkEncoding,
    Arithmetic.VariableModularMul.inPlaceEncoding, EncodedBit.relabel] using
    (congrArg Fin.val hwire).symm

/-- Inversion-owned division wires are disjoint from the shared product
carrier. This deliberately does not claim that division's product wires are
disjoint: those wires are the carrier. -/
theorem division_block_cross_ne
    (divisionOwned : EncodedBit Arithmetic.ModularInversion.rawEncoding)
    (productOwned : EncodedBit productEncoding) :
    (BinaryLabelEncoding.prodLeftBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding divisionOwned).wire ≠
      (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
        productTailEncoding
        (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding
          productOwned)).wire := by
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    Arithmetic.ModularInversion.rawEncoding productTailEncoding
    (BinaryLabelEncoding.prodLeftBit productEncoding tailEncoding productOwned)
    divisionOwned).symm

/-- Any full-workspace inversion port is physically disjoint from the direct
product carrier. -/
theorem inversionPort_productPort_cross_ne
    {inversionWidth : Nat}
    (inversion : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding inversionWidth)
    (product : Arithmetic.BlockBank.WordPort productEncoding params.width)
    (inversionBit : Fin inversionWidth) (productBit : Fin params.width) :
    ((inversionPort inversion).word.bit inversionBit).wire ≠
      ((productPort product).word.bit productBit).wire := by
  exact division_block_cross_ne (inversion.word.bit inversionBit)
    (product.word.bit productBit)

/-- Any inversion port is physically disjoint from the retained high padding
flag. -/
theorem inversionPort_retainedOutputFlagBit_cross_ne
    {inversionWidth : Nat}
    (inversion : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding inversionWidth)
    (inversionBit : Fin inversionWidth) :
    ((inversionPort inversion).word.bit inversionBit).wire ≠
      retainedOutputFlagBit.wire := by
  change
    (BinaryLabelEncoding.prodLeftBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding (inversion.word.bit inversionBit)).wire ≠
      (BinaryLabelEncoding.prodRightBit Arithmetic.ModularInversion.rawEncoding
        productTailEncoding
        (BinaryLabelEncoding.prodRightBit productEncoding tailEncoding
          (BinaryLabelEncoding.prodRightBit thinEncoding outputEncoding
            outputFlagBit))).wire
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    Arithmetic.ModularInversion.rawEncoding productTailEncoding
    (BinaryLabelEncoding.prodRightBit productEncoding tailEncoding
      (BinaryLabelEncoding.prodRightBit thinEncoding outputEncoding outputFlagBit))
    (inversion.word.bit inversionBit)).symm

/-- The product accumulator transported to the equal-width Kaliski input. -/
def productAccumulatorZeroExtendedWord :
    EncodedBit.Word rawEncoding Arithmetic.ModularInversion.arithmeticWidth where
  bit := fun bit =>
    (productPort productAccumulatorPort).word.bit
      (Fin.cast Arithmetic.ModularInversion.arithmeticWidth_eq bit)

/-- The physical accumulator transport reads as the value-level transport. -/
theorem productAccumulatorZeroExtendedWord_get
    (state : RawRegisters)
    (bit : Fin Arithmetic.ModularInversion.arithmeticWidth) :
    (productAccumulatorZeroExtendedWord.bit bit).get state =
      (zeroExtendWord ((productPort productAccumulatorPort).read state)).val.testBit
        bit.val := by
  simpa only [productAccumulatorZeroExtendedWord, zeroExtendWord,
    Fin.val_cast] using
    (productPort productAccumulatorPort).get_bit
      (Fin.cast Arithmetic.ModularInversion.arithmeticWidth_eq bit) state

/-- The widened accumulator source is disjoint from every bit of an
inversion-owned Kaliski input port. -/
theorem productAccumulatorZeroExtendedWord_inversionPort_cross_ne
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth)
    (sourceBit targetBit : Fin Arithmetic.ModularInversion.arithmeticWidth) :
    (productAccumulatorZeroExtendedWord.bit sourceBit).wire ≠
      ((inversionPort target).word.bit targetBit).wire := by
  simp only [productAccumulatorZeroExtendedWord]
  exact (inversionPort_productPort_cross_ne target productAccumulatorPort targetBit
    (Fin.cast Arithmetic.ModularInversion.arithmeticWidth_eq sourceBit)).symm

/-- Literal CNOT loader from the zero-extended direct accumulator into an
arithmetic-width inversion input port. -/
def productAccumulatorToInversionGates
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth) :
    List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.xorIntoGates productAccumulatorZeroExtendedWord
    (inversionPort target).word
    (fun bit =>
      productAccumulatorZeroExtendedWord_inversionPort_cross_ne target bit bit)

/-- Circuit compiled from the literal accumulator-to-inversion loader. -/
def productAccumulatorToInversionProgram
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (productAccumulatorToInversionGates target)

/-- Basis-state action of the literal accumulator-to-inversion loader. -/
def productAccumulatorToInversionStep
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth) :
    RawRegisters → RawRegisters :=
  EncodedBit.Word.xorIntoStep productAccumulatorZeroExtendedWord
    (inversionPort target).word
    (fun bit =>
      productAccumulatorZeroExtendedWord_inversionPort_cross_ne target bit bit)

theorem productAccumulatorToInversionGates_stepList
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth)
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (productAccumulatorToInversionGates target) state =
      productAccumulatorToInversionStep target state :=
  rfl

theorem productAccumulatorToInversion_realizes
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth) :
    UnitaryCircuit.Realizes rawEncoding (productAccumulatorToInversionProgram target)
      (productAccumulatorToInversionStep target) :=
  EncodedBit.Word.xorInto_realizes (QubitLayout.canonical _) .empty _ _ _

/-- The widened accumulator loader has one CNOT for every Kaliski input bit. -/
theorem productAccumulatorToInversionGates_length
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth) :
    (productAccumulatorToInversionGates target).length =
      Arithmetic.ModularInversion.arithmeticWidth := by
  exact EncodedBit.Word.xorIntoGates_length _ _ _

/-- The widened accumulator loader's exact CNOT ledger. -/
theorem productAccumulatorToInversionGates_cnotMultiplicity_sum
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth) :
    ((productAccumulatorToInversionGates target).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      Arithmetic.ModularInversion.arithmeticWidth := by
  exact EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum _ _ _

/-- The widened accumulator loader has no Toffoli leaves. -/
theorem productAccumulatorToInversionGates_toffoliMultiplicity_sum
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth) :
    ((productAccumulatorToInversionGates target).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  exact EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum _ _ _

/-- Loading a clean inversion input copies the accumulator's zero extension
without disturbing the rest of the workspace. -/
theorem productAccumulatorToInversionStep_eq_set_of_clean
    (target : Arithmetic.BlockBank.WordPort
      Arithmetic.ModularInversion.rawEncoding
        Arithmetic.ModularInversion.arithmeticWidth)
    (state : RawRegisters) (value : Word params.width)
    (hsource : (productPort productAccumulatorPort).read state = value)
    (htarget : (inversionPort target).read state = 0) :
    productAccumulatorToInversionStep target state =
      (inversionPort target).set state (zeroExtendWord value) := by
  have hcopy := EncodedBit.Word.xorIntoStep_eq_set_of_clean
    productAccumulatorZeroExtendedWord (inversionPort target).word
    (fun bit =>
      productAccumulatorZeroExtendedWord_inversionPort_cross_ne target bit bit)
    (inversionPort target).read
    (fun current => (inversionPort target).set current 0)
    (inversionPort target).set
    (fun current => by
      rw [(inversionPort target).set_set, (inversionPort target).set_read])
    (inversionPort target).get_bit
    (inversionPort target).pairwise_ne
    (fun sourceBit targetBit =>
      (productAccumulatorZeroExtendedWord_inversionPort_cross_ne
        target sourceBit targetBit).symm)
    (inversionPort target).clear_flip
    state (zeroExtendWord value) htarget
    (fun bit => by
      rw [productAccumulatorZeroExtendedWord_get state bit, hsource])
  rw [(inversionPort target).set_set] at hcopy
  exact hcopy

/-- Concrete loader for the preserved Kaliski denominator copy. -/
def productAccumulatorToDenominatorPreservedGates :
    List (EncodedBit.GateSpec rawEncoding) :=
  productAccumulatorToInversionGates Arithmetic.ModularInversion.preservedInputPort

/-- Concrete loader for the working Kaliski denominator copy. -/
def productAccumulatorToDenominatorWorkingGates :
    List (EncodedBit.GateSpec rawEncoding) :=
  productAccumulatorToInversionGates Arithmetic.ModularInversion.workingInputPort

/-- Basis-state action of loading the preserved Kaliski denominator copy. -/
def productAccumulatorToDenominatorPreservedStep : RawRegisters → RawRegisters :=
  productAccumulatorToInversionStep Arithmetic.ModularInversion.preservedInputPort

/-- Basis-state action of loading the working Kaliski denominator copy. -/
def productAccumulatorToDenominatorWorkingStep : RawRegisters → RawRegisters :=
  productAccumulatorToInversionStep Arithmetic.ModularInversion.workingInputPort

/-- Clean preserved-denominator loading is the canonical zero extension of
the direct accumulator. -/
theorem productAccumulatorToDenominatorPreservedStep_eq_set_of_clean
    (state : RawRegisters) (value : Word params.width)
    (hsource : (productPort productAccumulatorPort).read state = value)
    (htarget : denominatorPreservedPort.read state = 0) :
    productAccumulatorToDenominatorPreservedStep state =
      denominatorPreservedPort.set state (zeroExtendWord value) := by
  exact productAccumulatorToInversionStep_eq_set_of_clean
    Arithmetic.ModularInversion.preservedInputPort state value hsource htarget

/-- Clean working-denominator loading is the canonical zero extension of the
direct accumulator. -/
theorem productAccumulatorToDenominatorWorkingStep_eq_set_of_clean
    (state : RawRegisters) (value : Word params.width)
    (hsource : (productPort productAccumulatorPort).read state = value)
    (htarget : denominatorWorkingPort.read state = 0) :
    productAccumulatorToDenominatorWorkingStep state =
      denominatorWorkingPort.set state (zeroExtendWord value) := by
  exact productAccumulatorToInversionStep_eq_set_of_clean
    Arithmetic.ModularInversion.workingInputPort state value hsource htarget

/-- Low field-width view of the preserved Kaliski denominator copy. -/
def denominatorPreservedLowWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    denominatorPreservedPort.word.bit (Arithmetic.ModularInversion.lowInputIndex bit)

/-- A preserved denominator stored as a zero extension has the expected low
field bits. -/
theorem denominatorPreservedLowWord_get_of_zeroExtend
    (state : RawRegisters) (value : Word params.width)
    (hpreserved : denominatorPreservedPort.read state = zeroExtendWord value)
    (bit : Fin params.width) :
    (denominatorPreservedLowWord.bit bit).get state = value.val.testBit bit.val := by
  change
    (denominatorPreservedPort.word.bit
      (Arithmetic.ModularInversion.lowInputIndex bit)).get state = _
  rw [denominatorPreservedPort.get_bit, hpreserved]
  rfl

/-- Every preserved low denominator bit is physically disjoint from every
direct product-accumulator bit. -/
theorem denominatorPreservedLowWord_productAccumulator_cross_ne
    (sourceBit targetBit : Fin params.width) :
    (denominatorPreservedLowWord.bit sourceBit).wire ≠
      ((productPort productAccumulatorPort).word.bit targetBit).wire := by
  change
    ((inversionPort Arithmetic.ModularInversion.preservedInputPort).word.bit
      (Arithmetic.ModularInversion.lowInputIndex sourceBit)).wire ≠
      ((productPort productAccumulatorPort).word.bit targetBit).wire
  exact inversionPort_productPort_cross_ne
    Arithmetic.ModularInversion.preservedInputPort productAccumulatorPort
    (Arithmetic.ModularInversion.lowInputIndex sourceBit) targetBit

/-- Literal CNOT route from the preserved denominator's low word into the
shared direct accumulator.  On equal values it clears the accumulator. -/
def denominatorPreservedToProductAccumulatorGates :
    List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.xorIntoGates denominatorPreservedLowWord
    (productPort productAccumulatorPort).word
    (fun bit =>
      denominatorPreservedLowWord_productAccumulator_cross_ne bit bit)

/-- Basis-state action of the preserved-denominator accumulator route. -/
def denominatorPreservedToProductAccumulatorStep : RawRegisters → RawRegisters :=
  EncodedBit.Word.xorIntoStep denominatorPreservedLowWord
    (productPort productAccumulatorPort).word
    (fun bit =>
      denominatorPreservedLowWord_productAccumulator_cross_ne bit bit)

theorem denominatorPreservedToProductAccumulatorGates_stepList
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList denominatorPreservedToProductAccumulatorGates state =
      denominatorPreservedToProductAccumulatorStep state :=
  rfl

/-- The preserved-denominator accumulator route has one CNOT per field bit. -/
theorem denominatorPreservedToProductAccumulatorGates_length :
    denominatorPreservedToProductAccumulatorGates.length = params.width := by
  exact EncodedBit.Word.xorIntoGates_length _ _ _

/-- Exact CNOT ledger of the preserved-denominator accumulator route. -/
theorem denominatorPreservedToProductAccumulatorGates_cnotMultiplicity_sum :
    (denominatorPreservedToProductAccumulatorGates.map
      EncodedBit.GateSpec.cnotMultiplicity).sum = params.width := by
  exact EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum _ _ _

/-- The preserved-denominator accumulator route has no Toffoli leaves. -/
theorem denominatorPreservedToProductAccumulatorGates_toffoliMultiplicity_sum :
    (denominatorPreservedToProductAccumulatorGates.map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  exact EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum _ _ _

/-- Loading a clean accumulator copies the low preserved denominator word. -/
theorem denominatorPreservedToProductAccumulatorStep_eq_set_of_clean
    (state : RawRegisters) (value : Word params.width)
    (hpreserved : denominatorPreservedPort.read state = zeroExtendWord value)
    (htarget : (productPort productAccumulatorPort).read state = 0) :
    denominatorPreservedToProductAccumulatorStep state =
      (productPort productAccumulatorPort).set state value := by
  have hcopy := EncodedBit.Word.xorIntoStep_eq_set_of_clean
    denominatorPreservedLowWord (productPort productAccumulatorPort).word
    (fun bit =>
      denominatorPreservedLowWord_productAccumulator_cross_ne bit bit)
    (productPort productAccumulatorPort).read
    (fun current => (productPort productAccumulatorPort).set current 0)
    (productPort productAccumulatorPort).set
    (fun current => by
      rw [(productPort productAccumulatorPort).set_set,
        (productPort productAccumulatorPort).set_read])
    (productPort productAccumulatorPort).get_bit
    (productPort productAccumulatorPort).pairwise_ne
    (fun sourceBit targetBit =>
      (denominatorPreservedLowWord_productAccumulator_cross_ne
        sourceBit targetBit).symm)
    (productPort productAccumulatorPort).clear_flip
    state value htarget
    (fun bit => denominatorPreservedLowWord_get_of_zeroExtend
      state value hpreserved bit)
  rw [(productPort productAccumulatorPort).set_set] at hcopy
  exact hcopy

/-- When the direct accumulator already equals the preserved denominator's
low word, the same literal CNOT route clears it. -/
theorem denominatorPreservedToProductAccumulatorStep_eq_set_zero_of_equal
    (state : RawRegisters)
    (hequal : denominatorPreservedPort.read state =
      zeroExtendWord ((productPort productAccumulatorPort).read state)) :
    denominatorPreservedToProductAccumulatorStep state =
      (productPort productAccumulatorPort).set state 0 := by
  let result := denominatorPreservedToProductAccumulatorStep state
  have hresultFrame :
      (productPort productAccumulatorPort).set result 0 =
        (productPort productAccumulatorPort).set state 0 := by
    exact EncodedBit.Word.xorIntoStep_preserves_projection
      denominatorPreservedLowWord (productPort productAccumulatorPort).word
      (fun bit =>
        denominatorPreservedLowWord_productAccumulator_cross_ne bit bit)
      (fun current => (productPort productAccumulatorPort).set current 0)
      (productPort productAccumulatorPort).clear_flip state
  have hresultWord : (productPort productAccumulatorPort).read result = 0 := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← (productPort productAccumulatorPort).get_bit]
    unfold result denominatorPreservedToProductAccumulatorStep
    rw [EncodedBit.Word.xorIntoStep_get_target denominatorPreservedLowWord
      (productPort productAccumulatorPort).word
      (fun index =>
        denominatorPreservedLowWord_productAccumulator_cross_ne index index)
      bit
      (fun other hne =>
        (productPort productAccumulatorPort).pairwise_ne other bit hne)
      (fun targetBit =>
        (denominatorPreservedLowWord_productAccumulator_cross_ne
          bit targetBit).symm)]
    rw [(productPort productAccumulatorPort).get_bit,
      denominatorPreservedLowWord_get_of_zeroExtend state
        ((productPort productAccumulatorPort).read state) hequal bit]
    simp
  calc
    result = (productPort productAccumulatorPort).set
        ((productPort productAccumulatorPort).set result 0)
        ((productPort productAccumulatorPort).read result) := by
      rw [(productPort productAccumulatorPort).set_set,
        (productPort productAccumulatorPort).set_read]
    _ = (productPort productAccumulatorPort).set
        ((productPort productAccumulatorPort).set state 0) 0 :=
      congrArg₂ (productPort productAccumulatorPort).set hresultFrame hresultWord
    _ = (productPort productAccumulatorPort).set state 0 := by
      rw [(productPort productAccumulatorPort).set_set]

/-- The division numerator and its thin saved copy are distinct physical words. -/
theorem divisionNumerator_numeratorScratch_cross_ne
    (left right : Fin params.width) :
    (divisionNumeratorWord.bit left).wire ≠ (numeratorScratchWord.bit right).wire :=
  product_thin_cross_ne (Arithmetic.VariableModularMul.multiplierBit left)
    (numeratorScratchThinPort.word.bit right)

/-- Literal physical SWAP after reversing division. It releases the product
carrier for tail arithmetic while preserving the numerator for final cleanup. -/
def productMultiplier_numeratorScratch_swapGates :
    List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.swapGates divisionNumeratorWord numeratorScratchWord
    (fun bit => divisionNumerator_numeratorScratch_cross_ne bit bit)

/-- The direct variable-product schedule, relabeled only from raw field order
to named product registers. -/
def multiplicationGates : List (EncodedBit.GateSpec productEncoding) :=
  Arithmetic.VariableModularMulSchedule.gates.map
    (EncodedBit.GateSpec.relabel Arithmetic.VariableModularMul.registersEquiv)

/-- A direct selected-add schedule on the same product carrier. It replaces
the old wrapper-based modular-addition block. -/
def selectedAdditionGates (bit : Fin params.width) :
    List (EncodedBit.GateSpec productEncoding) :=
  (Arithmetic.VariableModularMul.selectedAddGates bit).map
    (EncodedBit.GateSpec.relabel Arithmetic.VariableModularMul.registersEquiv)

/-- The low multiplier bit used as the selected-add control. -/
def selectedAdditionBit : Fin params.width :=
  ⟨0, params.widthPos⟩

/-- Toggle the one selected-add control bit.  A multiplication carrier with
this bit set and every other multiplier bit clear is an addition carrier. -/
def selectedAdditionToggleGates : List (EncodedBit.GateSpec rawEncoding) :=
  [.x (productBit
    (Arithmetic.VariableModularMul.multiplierBit selectedAdditionBit))]

/-- Lift a product-carrier schedule across the untouched thin/output tail and
inversion workspace. -/
def sharedProductGates
    (gates : List (EncodedBit.GateSpec productEncoding)) :
    List (EncodedBit.GateSpec rawEncoding) :=
  (gates.map (EncodedBit.GateSpec.prodLeft tailEncoding)).map
    (EncodedBit.GateSpec.prodRight Arithmetic.ModularInversion.rawEncoding)

/-- Relabeling the direct multiplication schedule preserves its primitive
event ledger. -/
theorem multiplicationGates_map_event :
    multiplicationGates.map (EncodedBit.GateSpec.event .empty) =
      Arithmetic.VariableModularMulSchedule.gates.map
        (EncodedBit.GateSpec.event .empty) := by
  exact EncodedBit.GateSpec.map_event_relabel
    .empty Arithmetic.VariableModularMul.registersEquiv _

/-- Relabeling the direct multiplication schedule preserves its literal
primitive-list length. -/
theorem multiplicationGates_length :
    multiplicationGates.length =
      Arithmetic.VariableModularMulSchedule.gates.length := by
  simp only [multiplicationGates, List.length_map]

/-- Relabeling preserves the direct multiplication CNOT coordinate. -/
theorem multiplicationGates_cnotMultiplicity_sum :
    (multiplicationGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      (Arithmetic.VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum :=
  EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    multiplicationGates_map_event

/-- Relabeling preserves the direct multiplication Toffoli coordinate. -/
theorem multiplicationGates_toffoliMultiplicity_sum :
    (multiplicationGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (Arithmetic.VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum :=
  EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    multiplicationGates_map_event

/-- Width-only event bound for the direct shared product schedule. -/
def multiplicationGateLengthBound : Nat :=
  Arithmetic.VariableModularMulSchedule.eventCountBoundFor params.width

/-- Width-only CNOT bound for the direct shared product schedule. -/
def multiplicationCnotBound : Nat :=
  Arithmetic.VariableModularMulSchedule.cnotBoundFor params.width

/-- Width-only Toffoli bound for the direct shared product schedule. -/
def multiplicationToffoliBound : Nat :=
  Arithmetic.VariableModularMulSchedule.toffoliBoundFor params.width

/-- The direct shared product gate list obeys its source event ledger. -/
theorem multiplicationGates_length_le :
    multiplicationGates.length ≤ multiplicationGateLengthBound := by
  rw [multiplicationGates_length]
  simpa only [multiplicationGateLengthBound,
    Arithmetic.VariableModularMulSchedule.eventCountBound] using
    Arithmetic.VariableModularMulSchedule.gates_length_le

/-- The direct shared product gate list obeys its source CNOT ledger. -/
theorem multiplicationGates_cnotMultiplicity_sum_le :
    (multiplicationGates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      multiplicationCnotBound := by
  rw [multiplicationGates_cnotMultiplicity_sum]
  simpa only [multiplicationCnotBound,
    Arithmetic.VariableModularMulSchedule.cnotBound] using
    Arithmetic.VariableModularMulSchedule.gates_cnotMultiplicity_sum_le

/-- The direct shared product gate list obeys its source Toffoli ledger. -/
theorem multiplicationGates_toffoliMultiplicity_sum_le :
    (multiplicationGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      multiplicationToffoliBound := by
  rw [multiplicationGates_toffoliMultiplicity_sum]
  simpa only [multiplicationToffoliBound,
    Arithmetic.VariableModularMulSchedule.toffoliBound] using
    Arithmetic.VariableModularMulSchedule.gates_toffoliMultiplicity_sum_le

/-- The direct relabeled multiplication schedule keeps its named endpoint. -/
theorem multiplicationGates_stepList (state : ProductRegisters) :
    EncodedBit.GateSpec.stepList multiplicationGates state =
      Arithmetic.VariableModularMulSchedule.step state := by
  rw [multiplicationGates, EncodedBit.GateSpec.stepList_relabel]
  rw [Arithmetic.VariableModularMulSchedule.gates_stepList,
    Arithmetic.VariableModularMulSchedule.rawStep_registersEquiv]
  simp only [Equiv.symm_apply_apply]

/-- The direct relabeled selected-add schedule keeps its named endpoint. -/
theorem selectedAdditionGates_stepList (bit : Fin params.width)
    (state : ProductRegisters) :
    EncodedBit.GateSpec.stepList (selectedAdditionGates bit) state =
      Arithmetic.VariableModularMul.selectedAddStep bit state := by
  rw [selectedAdditionGates, EncodedBit.GateSpec.stepList_relabel]
  rw [Arithmetic.VariableModularMul.selectedAddGates_stepList,
    Arithmetic.VariableModularMul.rawSelectedAddStep_registersEquiv]
  simp only [Equiv.symm_apply_apply]

/-- Relabeling the selected-add schedule preserves its primitive events. -/
theorem selectedAdditionGates_map_event (bit : Fin params.width) :
    (selectedAdditionGates bit).map (EncodedBit.GateSpec.event .empty) =
      (Arithmetic.VariableModularMul.selectedAddGates bit).map
        (EncodedBit.GateSpec.event .empty) := by
  exact EncodedBit.GateSpec.map_event_relabel
    .empty Arithmetic.VariableModularMul.registersEquiv _

/-- Relabeling preserves the selected-add primitive-list length. -/
theorem selectedAdditionGates_length (bit : Fin params.width) :
    (selectedAdditionGates bit).length =
      (Arithmetic.VariableModularMul.selectedAddGates bit).length := by
  simp only [selectedAdditionGates, List.length_map]

/-- One selected-add route retains the exact direct CNOT coordinate. -/
theorem selectedAdditionGates_cnotMultiplicity_sum (bit : Fin params.width) :
    ((selectedAdditionGates bit).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      8 * params.width + 1 := by
  rw [EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (selectedAdditionGates_map_event bit)]
  exact Arithmetic.VariableModularMul.selectedAddGates_cnotMultiplicity_sum bit

/-- The direct selected-add list obeys the source event ledger. -/
theorem selectedAdditionGates_length_le (bit : Fin params.width) :
    (selectedAdditionGates bit).length ≤ 116 * params.width + 15 := by
  rw [selectedAdditionGates_length]
  simpa only [Arithmetic.VariableModularMul.selectedAddCircuit,
    EncodedBit.GateSpec.programList_eventCost_card] using
    Arithmetic.VariableModularMul.selectedAddCircuit_eventCount_le bit

/-- The direct selected-add list obeys the source Toffoli ledger. -/
theorem selectedAdditionGates_toffoliMultiplicity_sum_le
    (bit : Fin params.width) :
    ((selectedAdditionGates bit).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      108 * params.width + 14 := by
  rw [EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (selectedAdditionGates_map_event bit)]
  simpa only [Arithmetic.VariableModularMul.selectedAddCircuit,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum] using
    Arithmetic.VariableModularMul.selectedAddCircuit_toffoli_count_le bit

/-- Lifting a product schedule changes only its physical wire addresses. -/
theorem sharedProductGates_map_event
    (gates : List (EncodedBit.GateSpec productEncoding)) :
    (sharedProductGates gates).map (EncodedBit.GateSpec.event .empty) =
      gates.map (EncodedBit.GateSpec.event .empty) := by
  unfold sharedProductGates
  exact (EncodedBit.GateSpec.map_event_prodRight
    Arithmetic.ModularInversion.rawEncoding _).trans
      (EncodedBit.GateSpec.map_event_prodLeft tailEncoding _)

/-- The shared-carrier lift preserves the literal schedule length. -/
theorem sharedProductGates_length
    (gates : List (EncodedBit.GateSpec productEncoding)) :
    (sharedProductGates gates).length = gates.length := by
  simpa only [List.length_map] using
    congrArg List.length (sharedProductGates_map_event gates)

/-- Lifting a direct product schedule changes only untouched outer fields. -/
theorem sharedProductGates_stepList
    (gates : List (EncodedBit.GateSpec productEncoding))
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList (sharedProductGates gates) state =
      (state.1,
        (EncodedBit.GateSpec.stepList gates state.2.1, state.2.2)) := by
  unfold sharedProductGates
  calc
    EncodedBit.GateSpec.stepList
          ((gates.map (EncodedBit.GateSpec.prodLeft tailEncoding)).map
            (EncodedBit.GateSpec.prodRight
              Arithmetic.ModularInversion.rawEncoding)) state =
        (state.1,
          EncodedBit.GateSpec.stepList
            (gates.map (EncodedBit.GateSpec.prodLeft tailEncoding)) state.2) :=
      EncodedBit.GateSpec.stepList_prodRight
        Arithmetic.ModularInversion.rawEncoding _ state
    _ = (state.1,
          (EncodedBit.GateSpec.stepList gates state.2.1, state.2.2)) := by
      rw [EncodedBit.GateSpec.stepList_prodLeft]

/-! ### Clean product-carrier microkernels -/

/-- A canonical clean product carrier framed by an arbitrary inversion prefix
and arbitrary retained point-addition tail.  The frame is semantic data, not a
second arithmetic workspace. -/
def productRegistersWithFrame
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) : RawRegisters :=
  (inversion, (Arithmetic.VariableModularMul.cleanRegisters x, tail))

@[simp] theorem productMultiplierPort_read_productRegistersWithFrame
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) :
    divisionNumeratorPort.read (productRegistersWithFrame inversion x tail) =
      Arithmetic.ModularDivision.residueWord x.multiplier := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  apply Fin.ext
  simp [divisionNumeratorPort, productPort, productMultiplierPort,
    Arithmetic.BlockBank.WordPort.prodRight,
    Arithmetic.BlockBank.WordPort.prodLeft,
    productRegistersWithFrame,
    Arithmetic.VariableModularMul.cleanRegisters,
    Arithmetic.ModularDivision.productNumeratorPort,
    Arithmetic.ModularDivision.residueWord]

@[simp] theorem productMultiplicandPort_read_productRegistersWithFrame
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) :
    divisionProductTargetPort.read (productRegistersWithFrame inversion x tail) =
      Arithmetic.ModularDivision.residueWord x.multiplicand := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  apply Fin.ext
  simp [divisionProductTargetPort, productPort, productMultiplicandPort,
    Arithmetic.BlockBank.WordPort.prodRight,
    Arithmetic.BlockBank.WordPort.prodLeft,
    readProductMultiplicand, productRegistersWithFrame,
    Arithmetic.VariableModularMul.cleanRegisters,
    MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
    Arithmetic.ModularDivision.residueWord]

@[simp] theorem productAccumulatorPort_read_productRegistersWithFrame
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) :
    divisionQuotientPort.read (productRegistersWithFrame inversion x tail) =
      Arithmetic.ModularDivision.residueWord x.accumulator := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  apply Fin.ext
  simp [divisionQuotientPort, productPort, productAccumulatorPort,
    Arithmetic.BlockBank.WordPort.prodRight,
    Arithmetic.BlockBank.WordPort.prodLeft,
    readProductAccumulator, productRegistersWithFrame,
    Arithmetic.VariableModularMul.cleanRegisters,
    Arithmetic.ModularDivision.residueWord]

theorem productMultiplierPort_set_productRegistersWithFrame
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters)
    (value : ZMod params.modulus.val) :
    divisionNumeratorPort.set (productRegistersWithFrame inversion x tail)
        (Arithmetic.ModularDivision.residueWord value) =
      productRegistersWithFrame inversion { x with multiplier := value } tail := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  simp [divisionNumeratorPort, productPort, productMultiplierPort,
    Arithmetic.BlockBank.WordPort.prodRight,
    Arithmetic.BlockBank.WordPort.prodLeft,
    productRegistersWithFrame, Arithmetic.VariableModularMul.cleanRegisters,
    Arithmetic.ModularDivision.productNumeratorPort,
    Arithmetic.ModularDivision.residueWord]

theorem productMultiplicandPort_set_productRegistersWithFrame
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters)
    (value : ZMod params.modulus.val) :
    divisionProductTargetPort.set (productRegistersWithFrame inversion x tail)
        (Arithmetic.ModularDivision.residueWord value) =
      productRegistersWithFrame inversion { x with multiplicand := value } tail := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  simp [divisionProductTargetPort, productPort, productMultiplicandPort,
    Arithmetic.BlockBank.WordPort.prodRight,
    Arithmetic.BlockBank.WordPort.prodLeft,
    setProductMultiplicand, productRegistersWithFrame,
    Arithmetic.VariableModularMul.cleanRegisters,
    MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
    Arithmetic.ModularDivision.residueWord]

theorem productAccumulatorPort_set_productRegistersWithFrame
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters)
    (value : ZMod params.modulus.val) :
    divisionQuotientPort.set (productRegistersWithFrame inversion x tail)
        (Arithmetic.ModularDivision.residueWord value) =
      productRegistersWithFrame inversion { x with accumulator := value } tail := by
  let _ : NeZero params.modulus.val :=
    ⟨Nat.ne_of_gt params.modulusPos⟩
  simp [divisionQuotientPort, productPort, productAccumulatorPort,
    Arithmetic.BlockBank.WordPort.prodRight,
    Arithmetic.BlockBank.WordPort.prodLeft,
    setProductAccumulator, productRegistersWithFrame,
    Arithmetic.VariableModularMul.cleanRegisters,
    Arithmetic.ModularDivision.residueWord]

/-- Semantic predecessor for running the complete product schedule backward. -/
def subtractProduct
    (x : Arithmetic.VariableModularMul.Data) :
    Arithmetic.VariableModularMul.Data where
  multiplier := x.multiplier
  multiplicand := x.multiplicand
  accumulator := x.accumulator - x.multiplier * x.multiplicand

/-- Semantic predecessor for running one selected-add schedule backward. -/
def subtractSelected (bit : Fin params.width)
    (x : Arithmetic.VariableModularMul.Data) :
    Arithmetic.VariableModularMul.Data where
  multiplier := x.multiplier
  multiplicand := x.multiplicand
  accumulator := x.accumulator -
    if x.multiplier.val.testBit bit.val then x.multiplicand else 0

/-- The real shared multiplication list maps a clean framed carrier to the
clean product-accumulated carrier and preserves both arbitrary frame parts. -/
theorem sharedMultiplicationGates_clean
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList
        (sharedProductGates multiplicationGates)
        (productRegistersWithFrame inversion x tail) =
      productRegistersWithFrame inversion
        (Arithmetic.VariableModularMul.Data.addProduct x) tail := by
  rw [sharedProductGates_stepList, multiplicationGates_stepList,
    productRegistersWithFrame,
    Arithmetic.VariableModularMulSchedule.step_cleanEndpoint]
  rfl

/-- Reversing the same literal multiplication list subtracts the variable
product and restores a clean framed carrier. -/
theorem sharedMultiplicationGates_reverse_clean
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList
        (sharedProductGates multiplicationGates).reverse
        (productRegistersWithFrame inversion x tail) =
      productRegistersWithFrame inversion (subtractProduct x) tail := by
  have hdata :
      Arithmetic.VariableModularMul.Data.addProduct (subtractProduct x) = x := by
    cases x
    simp [Arithmetic.VariableModularMul.Data.addProduct, subtractProduct]
  have hforward := sharedMultiplicationGates_clean inversion
    (subtractProduct x) tail
  rw [hdata] at hforward
  rw [← hforward]
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (sharedProductGates multiplicationGates) _

/-- One real selected-add list preserves a clean framed carrier and adds the
multiplicand exactly when the selected multiplier bit is set. -/
theorem sharedSelectedAdditionGates_clean
    (bit : Fin params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList
        (sharedProductGates (selectedAdditionGates bit))
        (productRegistersWithFrame inversion x tail) =
      productRegistersWithFrame inversion
        (Arithmetic.VariableModularMul.Data.addSelected bit x) tail := by
  rw [sharedProductGates_stepList, selectedAdditionGates_stepList,
    productRegistersWithFrame,
    Arithmetic.VariableModularMul.selectedAddStep_cleanEndpoint]
  rfl

/-- Reversing the same literal selected-add list subtracts its selected
multiplicand contribution and restores the clean carrier. -/
theorem sharedSelectedAdditionGates_reverse_clean
    (bit : Fin params.width)
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList
        (sharedProductGates (selectedAdditionGates bit)).reverse
        (productRegistersWithFrame inversion x tail) =
      productRegistersWithFrame inversion (subtractSelected bit x) tail := by
  have hdata : Arithmetic.VariableModularMul.Data.addSelected bit
      (subtractSelected bit x) = x := by
    cases x
    simp [Arithmetic.VariableModularMul.Data.addSelected, subtractSelected]
  have hforward := sharedSelectedAdditionGates_clean bit inversion
    (subtractSelected bit x) tail
  rw [hdata] at hforward
  rw [← hforward]
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (sharedProductGates (selectedAdditionGates bit)) _

/-- The literal one-gate selected-add toggle has exactly the semantic bit-flip
action of the low multiplier wire. -/
theorem selectedAdditionToggleGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList selectedAdditionToggleGates state =
      (productBit
        (Arithmetic.VariableModularMul.multiplierBit
          selectedAdditionBit)).flip state := by
  rfl

/-- On a clean carrier whose semantic multiplier is zero, the literal toggle
sets the selected-add control bit. -/
theorem selectedAdditionToggleGates_sets_selectedBit
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters)
    (hmultiplier : x.multiplier = 0) :
    (productBit
      (Arithmetic.VariableModularMul.multiplierBit selectedAdditionBit)).get
        (EncodedBit.GateSpec.stepList selectedAdditionToggleGates
          (productRegistersWithFrame inversion x tail)) = true := by
  rw [selectedAdditionToggleGates_stepList, EncodedBit.get_flip_self]
  have hzero :
      (productBit
        (Arithmetic.VariableModularMul.multiplierBit selectedAdditionBit)).get
          (productRegistersWithFrame inversion x tail) = false := by
    change (divisionNumeratorPort.word.bit selectedAdditionBit).get
        (productRegistersWithFrame inversion x tail) = false
    rw [divisionNumeratorPort.get_bit]
    simp [divisionNumeratorPort, productPort, productMultiplierPort,
      Arithmetic.BlockBank.WordPort.prodRight,
      Arithmetic.BlockBank.WordPort.prodLeft,
      Arithmetic.ModularDivision.productNumeratorPort,
      productRegistersWithFrame,
      Arithmetic.VariableModularMul.cleanRegisters, hmultiplier]
  rw [hzero]
  rfl

/-- Canonical low-bit-only word used to turn the selected-add route into an
unconditional modular addition. -/
def selectedAdditionOneWord : Word params.width :=
  ⟨1, Nat.one_lt_two_pow (Nat.ne_of_gt params.widthPos)⟩

/-- Semantic clean datum obtained by enabling the low multiplier bit. -/
def enableSelectedAddition
    (x : Arithmetic.VariableModularMul.Data) :
    Arithmetic.VariableModularMul.Data where
  multiplier := 1
  multiplicand := x.multiplicand
  accumulator := x.accumulator

/-- For a nontrivial field modulus, toggling the low multiplier bit converts a
clean zero-multiplier carrier into the canonical clean one-multiplier carrier.
This is the bridge that lets the real selected-add schedule serve as an
unconditional modular-add microkernel. -/
theorem selectedAdditionToggleGates_enable_clean
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters)
    (hmodulus : 1 < params.modulus.val)
    (hmultiplier : x.multiplier = 0) :
    EncodedBit.GateSpec.stepList selectedAdditionToggleGates
        (productRegistersWithFrame inversion x tail) =
      productRegistersWithFrame inversion (enableSelectedAddition x) tail := by
  let _ : Fact (1 < params.modulus.val) := ⟨hmodulus⟩
  let state := productRegistersWithFrame inversion x tail
  let target := divisionNumeratorPort.word.bit selectedAdditionBit
  have htarget :
      target = productBit
        (Arithmetic.VariableModularMul.multiplierBit selectedAdditionBit) := rfl
  have hreadZero : divisionNumeratorPort.read state = 0 := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    simp [state, divisionNumeratorPort, productPort, productMultiplierPort,
      Arithmetic.BlockBank.WordPort.prodRight,
      Arithmetic.BlockBank.WordPort.prodLeft,
      Arithmetic.ModularDivision.productNumeratorPort,
      productRegistersWithFrame,
      Arithmetic.VariableModularMul.cleanRegisters, hmultiplier]
  have hreadToggle :
      divisionNumeratorPort.read (target.flip state) =
        selectedAdditionOneWord := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← divisionNumeratorPort.get_bit]
    by_cases hbit : bit = selectedAdditionBit
    · subst bit
      rw [EncodedBit.get_flip_self, divisionNumeratorPort.get_bit, hreadZero]
      simp [selectedAdditionOneWord, selectedAdditionBit]
    · rw [EncodedBit.get_flip_of_wire_ne target
          (divisionNumeratorPort.word.bit bit)
          (divisionNumeratorPort.pairwise_ne selectedAdditionBit bit
            (Ne.symm hbit)),
        divisionNumeratorPort.get_bit, hreadZero]
      have hval : bit.val ≠ 0 := by
        intro hzero
        apply hbit
        apply Fin.ext
        simpa [selectedAdditionBit] using hzero
      rw [show (0 : Word params.width).val = 0 by rfl,
        show selectedAdditionOneWord.val = 1 by rfl]
      calc
        Nat.testBit 0 bit.val = false :=
          Nat.testBit_lt_two_pow (pow_pos (by decide) bit.val)
        _ = Nat.testBit 1 bit.val :=
          (Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hval)).symm
  have htoggleSet :
      target.flip state =
        divisionNumeratorPort.set state selectedAdditionOneWord := by
    calc
      target.flip state = divisionNumeratorPort.set (target.flip state)
          (divisionNumeratorPort.read (target.flip state)) :=
        (divisionNumeratorPort.set_read _).symm
      _ = divisionNumeratorPort.set (target.flip state)
          selectedAdditionOneWord := by rw [hreadToggle]
      _ = divisionNumeratorPort.set
          (divisionNumeratorPort.set (target.flip state) 0)
          selectedAdditionOneWord := by
        rw [divisionNumeratorPort.set_set]
      _ = divisionNumeratorPort.set
          (divisionNumeratorPort.set state 0) selectedAdditionOneWord := by
        rw [divisionNumeratorPort.clear_flip]
      _ = divisionNumeratorPort.set state selectedAdditionOneWord := by
        rw [divisionNumeratorPort.set_set]
  rw [selectedAdditionToggleGates_stepList, ← htarget, htoggleSet]
  simp [state, divisionNumeratorPort, productPort, productMultiplierPort,
    Arithmetic.BlockBank.WordPort.prodRight,
    Arithmetic.BlockBank.WordPort.prodLeft,
    Arithmetic.ModularDivision.productNumeratorPort,
    productRegistersWithFrame, enableSelectedAddition,
    selectedAdditionOneWord,
    Arithmetic.VariableModularMul.cleanRegisters, hmultiplier, ZMod.val_one]

/-- Executing the same literal selected-add toggle a second time restores the
entire framed carrier, hence in particular returns the selected bit to its
clean-zero value. -/
theorem selectedAdditionToggleGates_twice
    (state : RawRegisters) :
    EncodedBit.GateSpec.stepList selectedAdditionToggleGates
        (EncodedBit.GateSpec.stepList selectedAdditionToggleGates state) =
      state := by
  simpa only [selectedAdditionToggleGates, List.reverse_singleton] using
    EncodedBit.GateSpec.stepList_reverse_stepList
      selectedAdditionToggleGates state

/-- After the clean enable bridge, executing the same actual X gate restores
the original zero-multiplier carrier without disturbing either frame part. -/
theorem selectedAdditionToggleGates_disable_clean
    (inversion : Arithmetic.ModularInversion.RawRegisters)
    (x : Arithmetic.VariableModularMul.Data)
    (tail : ThinRegisters × OutputRegisters)
    (hmodulus : 1 < params.modulus.val)
    (hmultiplier : x.multiplier = 0) :
    EncodedBit.GateSpec.stepList selectedAdditionToggleGates
        (productRegistersWithFrame inversion (enableSelectedAddition x) tail) =
      productRegistersWithFrame inversion x tail := by
  rw [← selectedAdditionToggleGates_enable_clean inversion x tail
    hmodulus hmultiplier]
  exact selectedAdditionToggleGates_twice _

/-- Lift the real inversion schedule over the one product carrier and tail. -/
def inversionGates : List (EncodedBit.GateSpec rawEncoding) :=
  Arithmetic.ModularInversion.gates.map
    (EncodedBit.GateSpec.prodLeft productTailEncoding)

/-- Lifting inversion over the actual shared carrier preserves its list
length. -/
theorem inversionGates_length :
    inversionGates.length = Arithmetic.ModularInversion.gates.length := by
  exact EncodedBit.GateSpec.length_prodLeft productTailEncoding _

/-- Lifting inversion changes only its wire addresses. -/
theorem inversionGates_map_event :
    inversionGates.map (EncodedBit.GateSpec.event .empty) =
      Arithmetic.ModularInversion.gates.map (EncodedBit.GateSpec.event .empty) := by
  exact EncodedBit.GateSpec.map_event_prodLeft productTailEncoding _

/-- Low inverse-result word inside the physical inversion prefix. -/
def inverseSourceWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit Arithmetic.ModularInversion.rawEncoding
      productTailEncoding (Arithmetic.ModularDivision.inverseTargetLowBit bit)

/-- The inverse source and shared product multiplicand live in separate
physical product components. -/
theorem inverseSource_productTarget_ne (bit : Fin params.width) :
    (inverseSourceWord.bit bit).wire ≠ (divisionProductTargetWord.bit bit).wire := by
  exact division_block_cross_ne
    (Arithmetic.ModularDivision.inverseTargetLowBit bit)
    (Arithmetic.VariableModularMul.inPlaceMultiplicandBit bit)

/-- Literal CNOT route from inversion output to the shared product
multiplicand. -/
def divisionLoadGates : List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.xorIntoGates inverseSourceWord divisionProductTargetWord
    inverseSource_productTarget_ne

/-- The inverse loader is one CNOT per field bit. -/
theorem divisionLoadGates_length : divisionLoadGates.length = params.width := by
  exact EncodedBit.Word.xorIntoGates_length
    inverseSourceWord divisionProductTargetWord inverseSource_productTarget_ne

/-- The inverse loader has the same CNOT count as its word width. -/
theorem divisionLoadGates_cnotMultiplicity_sum :
    (divisionLoadGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      params.width := by
  exact EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    inverseSourceWord divisionProductTargetWord inverseSource_productTarget_ne

/-- The inverse loader has no Toffoli leaves. -/
theorem divisionLoadGates_toffoliMultiplicity_sum :
    (divisionLoadGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  exact EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum
    inverseSourceWord divisionProductTargetWord inverseSource_productTarget_ne

/-- Actual division schedule over the shared product carrier. This is the
same inversion/load/product/unload/uncompute order as modular division, with
the product stage physically reused rather than copied into a block bank. -/
def divisionGates : List (EncodedBit.GateSpec rawEncoding) :=
  inversionGates ++ divisionLoadGates ++
    sharedProductGates multiplicationGates ++
    divisionLoadGates.reverse ++ inversionGates.reverse

/-- Exact primitive-length decomposition of the real shared division route. -/
theorem divisionGates_length :
    divisionGates.length =
      2 * Arithmetic.ModularInversion.gates.length + 2 * params.width +
        Arithmetic.VariableModularMulSchedule.gates.length := by
  simp only [divisionGates, List.length_append, List.length_reverse,
    inversionGates_length, divisionLoadGates_length,
    sharedProductGates_length, multiplicationGates_length]
  omega

/-- Exact CNOT decomposition of the real shared division route. -/
theorem divisionGates_cnotMultiplicity_sum :
    (divisionGates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * (Arithmetic.ModularInversion.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum + 2 * params.width +
        (Arithmetic.VariableModularMulSchedule.gates.map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  have hinversion := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    inversionGates_map_event
  have hproduct := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (sharedProductGates_map_event multiplicationGates)
  simp only [divisionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse]
  rw [hinversion, hproduct, divisionLoadGates_cnotMultiplicity_sum,
    multiplicationGates_cnotMultiplicity_sum]
  omega

/-- Exact Toffoli decomposition of the real shared division route. -/
theorem divisionGates_toffoliMultiplicity_sum :
    (divisionGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * (Arithmetic.ModularInversion.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum +
        (Arithmetic.VariableModularMulSchedule.gates.map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  have hinversion := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    inversionGates_map_event
  have hproduct := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (sharedProductGates_map_event multiplicationGates)
  simp only [divisionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse]
  rw [hinversion, hproduct, divisionLoadGates_toffoliMultiplicity_sum,
    multiplicationGates_toffoliMultiplicity_sum]
  omega

/-! ### Direct division semantics -/

/-- Reassociate a canonical division carrier with the retained point-addition
tail.  This is only a carrier association; it allocates no second arithmetic
workspace. -/
def divisionCoreWithTail
    (core : Arithmetic.ModularDivision.RawRegisters)
    (tail : ThinRegisters × OutputRegisters) : RawRegisters :=
  (core.1, (core.2, tail))

/-- Clean direct workspace for one public division datum and an arbitrary
retained point-addition tail. -/
def divisionRegistersWithTail
    (x : MAU.Division.Data params.modulus.val)
    (tail : ThinRegisters × OutputRegisters) : RawRegisters :=
  divisionCoreWithTail (Arithmetic.ModularDivision.cleanRegisters x) tail

/-- Direct workspace after the Kaliski inversion prefix. -/
def divisionInverseReadyWithTail
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val)
    (tail : ThinRegisters × OutputRegisters) : RawRegisters :=
  divisionCoreWithTail
    (Arithmetic.ModularDivision.inverseReadyRegisters x accumulator) tail

/-- Direct workspace after the inverse has been routed into the shared
product multiplicand. -/
def divisionProductReadyWithTail
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val)
    (tail : ThinRegisters × OutputRegisters) : RawRegisters :=
  divisionCoreWithTail
    (Arithmetic.ModularDivision.productReadyRegisters x accumulator) tail

/-- The lifted inversion list acts only on the inversion prefix. -/
theorem inversionGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList inversionGates state =
      (Arithmetic.ModularInversion.rawStep state.1, state.2) := by
  calc
    EncodedBit.GateSpec.stepList inversionGates state =
        (EncodedBit.GateSpec.stepList Arithmetic.ModularInversion.gates state.1,
          state.2) := by
      simpa only [inversionGates, rawEncoding] using
        (EncodedBit.GateSpec.stepList_prodLeft productTailEncoding
          Arithmetic.ModularInversion.gates state)
    _ = (Arithmetic.ModularInversion.rawStep state.1, state.2) := by
      rw [Arithmetic.ModularInversion.gates_stepList]

/-- The direct product target and inversion-produced inverse word are
physically disjoint in both directions. -/
theorem divisionProductTarget_inverseSource_cross_ne
    (sourceBit targetBit : Fin params.width) :
    (divisionProductTargetWord.bit targetBit).wire ≠
      (inverseSourceWord.bit sourceBit).wire := by
  exact (division_block_cross_ne
    (Arithmetic.ModularDivision.inverseTargetLowBit sourceBit)
    (Arithmetic.VariableModularMul.inPlaceMultiplicandBit targetBit)).symm

/-- On an inverse-ready direct workspace, the lifted source word reads the
same inverse residue as the canonical division core. -/
theorem inverseSourceWord_get_inverseReadyWithTail
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val)
    (tail : ThinRegisters × OutputRegisters)
    (bit : Fin params.width) :
    (inverseSourceWord.bit bit).get
        (divisionInverseReadyWithTail x accumulator tail) =
      (Arithmetic.ModularDivision.residueWord
        (MAU.Inversion.inverseResidue x.denominator)).val.testBit bit.val := by
  change (Arithmetic.ModularDivision.inverseSourceWord.bit bit).get
      (Arithmetic.ModularDivision.inverseReadyRegisters x accumulator) = _
  exact Arithmetic.ModularDivision.inverseSourceWord_get_inverseReady
    x accumulator bit

/-- Computing the inverse on a clean direct workspace establishes the same
inverse-ready core while preserving the complete retained tail. -/
theorem inversionGates_clean
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList inversionGates
        (divisionCoreWithTail
          (Arithmetic.ModularDivision.cleanRegistersWithAccumulator
            x accumulator) tail) =
      divisionInverseReadyWithTail x accumulator tail := by
  rw [inversionGates_stepList]
  have hcore := Arithmetic.ModularDivision.inverseProgramGates_clean
    x accumulator
  rw [Arithmetic.ModularDivision.inverseProgramGates_stepList] at hcore
  simpa [divisionInverseReadyWithTail, divisionCoreWithTail] using
    congrArg (fun core : Arithmetic.ModularDivision.RawRegisters =>
      divisionCoreWithTail core tail) hcore

/-- The literal direct CNOT loader installs the inverse in the one shared
product multiplicand and leaves the retained tail unchanged. -/
theorem divisionLoadGates_inverseReady
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList divisionLoadGates
        (divisionInverseReadyWithTail x accumulator tail) =
      divisionProductReadyWithTail x accumulator tail := by
  let state := divisionInverseReadyWithTail x accumulator tail
  let value : Nat.FixedWidth.Word params.width :=
    Arithmetic.ModularDivision.residueWord
      (MAU.Inversion.inverseResidue x.denominator)
  have hcopy := EncodedBit.Word.xorIntoStep_eq_set_of_clean
    inverseSourceWord divisionProductTargetWord
    inverseSource_productTarget_ne divisionProductTargetPort.read
    (fun current => divisionProductTargetPort.set current 0)
    divisionProductTargetPort.set
    (fun current => by
      rw [divisionProductTargetPort.set_set,
        divisionProductTargetPort.set_read])
    divisionProductTargetPort.get_bit
    divisionProductTargetPort.pairwise_ne
    divisionProductTarget_inverseSource_cross_ne
    divisionProductTargetPort.clear_flip state value
    (by
      change readProductMultiplicand
          (Arithmetic.VariableModularMul.cleanRegisters
            (Arithmetic.ModularDivision.productData x 0 accumulator)) = 0
      apply Fin.ext
      simp [readProductMultiplicand,
        Arithmetic.ModularDivision.productData,
        Arithmetic.VariableModularMul.cleanRegisters,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState])
    (fun bit => by
      exact inverseSourceWord_get_inverseReadyWithTail
        x accumulator tail bit)
  rw [divisionProductTargetPort.set_set] at hcopy
  have hset :
      divisionProductTargetPort.set state value =
        divisionProductReadyWithTail x accumulator tail := by
    change
      (Arithmetic.ModularInversion.cleanRegisters
          (Arithmetic.ModularDivision.inversionData x).addInverseIntoTarget,
        (setProductMultiplicand
          (Arithmetic.VariableModularMul.cleanRegisters
            (Arithmetic.ModularDivision.productData x 0 accumulator)) value,
          tail)) =
      (Arithmetic.ModularInversion.cleanRegisters
          (Arithmetic.ModularDivision.inversionData x).addInverseIntoTarget,
        (Arithmetic.VariableModularMul.cleanRegisters
          (Arithmetic.ModularDivision.productData x
            (MAU.Inversion.inverseResidue x.denominator) accumulator), tail))
    apply congrArg (fun product : ProductRegisters =>
      (Arithmetic.ModularInversion.cleanRegisters
          (Arithmetic.ModularDivision.inversionData x).addInverseIntoTarget,
        (product, tail)))
    simp only [value, setProductMultiplicand,
      Arithmetic.ModularDivision.residueWord,
      Arithmetic.ModularDivision.productData,
      Arithmetic.VariableModularMul.cleanRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState]
  rw [hset] at hcopy
  simpa only [divisionLoadGates, EncodedBit.Word.xorIntoStep, state] using hcopy

/-- The literal shared product stage adds the quotient to the selected
accumulator while preserving the inversion prefix and retained tail. -/
theorem sharedProductGates_productReady
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList
        (sharedProductGates multiplicationGates)
        (divisionProductReadyWithTail x accumulator tail) =
      divisionProductReadyWithTail x
        (accumulator + MAU.Division.quotientResidue
          x.denominator x.numerator) tail := by
  rw [sharedProductGates_stepList, multiplicationGates_stepList]
  have hcore := Arithmetic.ModularDivision.productProgramGates_productReady
    x accumulator
  rw [Arithmetic.ModularDivision.productProgramGates_stepList] at hcore
  simpa [divisionProductReadyWithTail, divisionCoreWithTail] using
    congrArg (fun core : Arithmetic.ModularDivision.RawRegisters =>
      divisionCoreWithTail core tail) hcore

/-- Circuit compiled from the one literal direct division ledger. -/
def divisionProgram : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty divisionGates

/-- Total basis action of the literal direct division ledger. -/
def divisionStep : RawRegisters → RawRegisters :=
  EncodedBit.GateSpec.stepList divisionGates

/-- The named total action is definitionally the fold of the source gate
ledger. -/
theorem divisionGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList divisionGates state = divisionStep state :=
  rfl

/-- The compiled direct division circuit realizes the same folded source
ledger used for resources. -/
theorem divisionProgram_realizes :
    UnitaryCircuit.Realizes rawEncoding divisionProgram divisionStep :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty divisionGates

/-- The complete literal direct division schedule maps a clean core to the
quotient-updated clean core while preserving every retained point-addition
word and control bit. -/
theorem divisionGates_cleanEndpoint
    (x : MAU.Division.Data params.modulus.val)
    (tail : ThinRegisters × OutputRegisters) :
    EncodedBit.GateSpec.stepList divisionGates
        (divisionRegistersWithTail x tail) =
      divisionRegistersWithTail x.addQuotientIntoTarget tail := by
  let result := x.target +
    MAU.Division.quotientResidue x.denominator x.numerator
  have hinversionStart := inversionGates_clean x x.target tail
  have hloadStart := divisionLoadGates_inverseReady x x.target tail
  have hproduct :
      EncodedBit.GateSpec.stepList
          (sharedProductGates multiplicationGates)
          (divisionProductReadyWithTail x x.target tail) =
        divisionProductReadyWithTail x result tail := by
    simpa only [result] using sharedProductGates_productReady x x.target tail
  have hloadResult := divisionLoadGates_inverseReady x result tail
  have hunload :
      EncodedBit.GateSpec.stepList divisionLoadGates.reverse
          (divisionProductReadyWithTail x result tail) =
        divisionInverseReadyWithTail x result tail := by
    rw [← hloadResult]
    exact EncodedBit.GateSpec.stepList_reverse_stepList divisionLoadGates _
  have hinversionResult := inversionGates_clean x result tail
  have huncompute :
      EncodedBit.GateSpec.stepList inversionGates.reverse
          (divisionInverseReadyWithTail x result tail) =
        divisionCoreWithTail
          (Arithmetic.ModularDivision.cleanRegistersWithAccumulator x result)
          tail := by
    rw [← hinversionResult]
    exact EncodedBit.GateSpec.stepList_reverse_stepList inversionGates _
  change EncodedBit.GateSpec.stepList divisionGates
      (divisionCoreWithTail
        (Arithmetic.ModularDivision.cleanRegistersWithAccumulator x x.target)
        tail) = _
  simp only [divisionGates, EncodedBit.GateSpec.stepList_append]
  rw [hinversionStart, hloadStart, hproduct, hunload, huncompute]
  simp [divisionRegistersWithTail, divisionCoreWithTail, result,
    Arithmetic.ModularDivision.cleanRegisters,
    Arithmetic.ModularDivision.cleanRegistersWithAccumulator,
    MAU.Division.Data.addQuotientIntoTarget,
    Arithmetic.ModularDivision.inversionData,
    Arithmetic.ModularDivision.productData]

/-- Width-only event bound for the actual shared division route. -/
def divisionGateLengthBound : Nat :=
  2 * Arithmetic.ModularInversion.gateLengthBound + 2 * params.width +
    multiplicationGateLengthBound

/-- Width-only CNOT bound for the actual shared division route. -/
def divisionCnotBound : Nat :=
  2 * Arithmetic.ModularInversion.cnotBound + 2 * params.width +
    multiplicationCnotBound

/-- Width-only Toffoli bound for the actual shared division route. -/
def divisionToffoliBound : Nat :=
  2 * Arithmetic.ModularInversion.toffoliBound + multiplicationToffoliBound

/-- The actual shared division gate list obeys its literal event ledger. -/
theorem divisionGates_length_le :
    divisionGates.length ≤ divisionGateLengthBound := by
  rw [divisionGates_length]
  have hinversion : Arithmetic.ModularInversion.gates.length ≤
      Arithmetic.ModularInversion.gateLengthBound :=
    Arithmetic.ModularInversion.gates_length_le
  have hproduct := multiplicationGates_length_le
  rw [multiplicationGates_length] at hproduct
  unfold divisionGateLengthBound
  omega

/-- The actual shared division gate list obeys its literal CNOT ledger. -/
theorem divisionGates_cnotMultiplicity_sum_le :
    (divisionGates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      divisionCnotBound := by
  rw [divisionGates_cnotMultiplicity_sum]
  have hinversion :
      (Arithmetic.ModularInversion.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
        Arithmetic.ModularInversion.cnotBound :=
    Arithmetic.ModularInversion.gates_cnotMultiplicity_sum_le
  have hproduct := multiplicationGates_cnotMultiplicity_sum_le
  rw [multiplicationGates_cnotMultiplicity_sum] at hproduct
  unfold divisionCnotBound
  omega

/-- The actual shared division gate list obeys its literal Toffoli ledger. -/
theorem divisionGates_toffoliMultiplicity_sum_le :
    (divisionGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      divisionToffoliBound := by
  rw [divisionGates_toffoliMultiplicity_sum]
  have hinversion :
      (Arithmetic.ModularInversion.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
        Arithmetic.ModularInversion.toffoliBound :=
    Arithmetic.ModularInversion.gates_toffoliMultiplicity_sum_le
  have hproduct := multiplicationGates_toffoliMultiplicity_sum_le
  rw [multiplicationGates_toffoliMultiplicity_sum] at hproduct
  unfold divisionToffoliBound
  omega

/-- The physical carrier has one inversion workspace, one direct variable
product carrier, four thin field words, two output words, and two suffix bits. -/
theorem rawEncoding_width_exact :
    rawEncoding.width =
      Arithmetic.ModularInversion.physicalWidthFor params.width +
        13 * params.width + 7 := by
  rw [rawEncoding, BinaryLabelEncoding.prod_width, productTailEncoding,
    BinaryLabelEncoding.prod_width, tailEncoding,
    BinaryLabelEncoding.prod_width, thinEncoding,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.prod_width,
    BinaryLabelEncoding.prod_width, outputEncoding,
    BinaryLabelEncoding.prod_width, BinaryLabelEncoding.prod_width,
    BinaryLabelEncoding.prod_width]
  have hinversion : Arithmetic.ModularInversion.rawEncoding.width =
      Arithmetic.ModularInversion.physicalWidthFor params.width :=
    Arithmetic.ModularInversion.encoding_width_exact
  rw [hinversion]
  rw [show productEncoding.width = 7 * params.width + 5 by
    exact Arithmetic.VariableModularMul.encoding_width_exact]
  simp [wordEncoding, MAU.Inversion.MK.wordEncoding]
  omega

end

end Workspace
end ParameterizedPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
