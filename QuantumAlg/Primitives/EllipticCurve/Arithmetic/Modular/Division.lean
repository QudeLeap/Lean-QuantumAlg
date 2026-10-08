/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.Modular.Inversion
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.BlockBank
import all QuantumAlg.Primitives.MAU.Division.StructuredCircuit

/-!
# Width-parameterized odd-modulus division

This module composes the actual fixed-round Kaliski inversion circuit with the
actual variable modular multiply-accumulate circuit.  The only inter-carrier
routing is an explicit low-word CNOT copy of the inverse into the multiplier's
clean multiplicand register; the copy is uncomputed before inversion itself is
uncomputed.
-/

section

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic
namespace ModularDivision

open Nat.FixedWidth

noncomputable section

variable [params : VariableModularMul.Parameters]

local instance modulusNeZero : NeZero params.modulus.val :=
  ⟨Nat.ne_of_gt params.modulusPos⟩

/-- Raw register carrier of the fixed-round inversion stage. -/
abbrev InversionRaw := ModularInversion.RawRegisters

/-- Raw register carrier of the variable modular-product stage. -/
abbrev ProductRegisters := VariableModularMul.Registers

/-- Physical division carrier: Kaliski inversion workspace followed by one
variable modular multiply-accumulate workspace. -/
abbrev RawRegisters := InversionRaw × ProductRegisters

/-- Product encoding of the two actual arithmetic carriers. -/
@[implicit_reducible]
def rawEncoding : BinaryLabelEncoding RawRegisters :=
  BinaryLabelEncoding.prod ModularInversion.rawEncoding
    VariableModularMul.encoding

/-! ## Input-independent loading boundary -/

/-- Complete arithmetic-width denominator copy preserved by Kaliski
inversion, lifted into the division carrier. -/
def denominatorPreservedPort :
    BlockBank.WordPort rawEncoding ModularInversion.arithmeticWidth :=
  ModularInversion.preservedInputPort.prodLeft VariableModularMul.encoding

/-- Complete arithmetic-width denominator copy consumed by the Kaliski
working register, lifted into the division carrier. -/
def denominatorWorkingPort :
    BlockBank.WordPort rawEncoding ModularInversion.arithmeticWidth :=
  ModularInversion.workingInputPort.prodLeft VariableModularMul.encoding

/-- Structural numerator port over the variable-multiplication product
carrier before it is lifted into the complete division workspace. -/
def productNumeratorPort :
    BlockBank.WordPort VariableModularMul.encoding params.width where
  word := { bit := VariableModularMul.multiplierBit }
  read := fun state => ⟨state.multiplier.val, ZMod.val_lt state.multiplier⟩
  set := fun state value =>
    { state with multiplier := (value.val : VariableModularMul.Word) }
  set_read := by
    intro state
    cases state
    simp
  read_set := by
    intro state value
    apply Fin.ext
    simp [Nat.mod_eq_of_lt value.isLt]
  set_set := by intro state first second; cases state; rfl
  get_bit := by
    intro bit state
    change (VariableModularMul.rawMultiplierBit bit).get
        (VariableModularMul.registersEquiv state) =
      state.multiplier.val.testBit bit.val
    rw [VariableModularMul.rawMultiplierBit_get]
    rfl
  pairwise_ne := VariableModularMul.multiplierBit_pairwise_ne
  clear_flip := by intro bit state; cases state; rfl

/-- Preserved numerator word in the product half of the division carrier. -/
def numeratorPort : BlockBank.WordPort rawEncoding params.width :=
  BlockBank.WordPort.prodRight ModularInversion.rawEncoding
    productNumeratorPort

/-- Preserved low denominator copy lifted into the complete division carrier. -/
def denominatorPreservedWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit ModularInversion.rawEncoding
      VariableModularMul.encoding
      (ModularInversion.preservedInputLowWord.bit bit)

/-- Working low denominator copy lifted into the complete division carrier. -/
def denominatorWorkingWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit ModularInversion.rawEncoding
      VariableModularMul.encoding
      (ModularInversion.workingInputLowWord.bit bit)

/-- Preserved numerator word in the product half of the division carrier. -/
def numeratorWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit ModularInversion.rawEncoding
      VariableModularMul.encoding
      (VariableModularMul.multiplierBit bit)

/-- Canonical input-independent division workspace.  All data-dependent words
start zero while the modulus-dependent Kaliski and multiplication work fields
retain their fixed clean seeds. -/
def blankRegisters : RawRegisters :=
  (ModularInversion.blankRegisters,
    VariableModularMul.cleanRegisters
      ({ multiplier := 0, multiplicand := 0, accumulator := 0 } :
        VariableModularMul.Data))

@[simp] theorem numeratorPort_read_blankRegisters :
  numeratorPort.read blankRegisters = 0 := by
  apply Fin.ext
  simp [numeratorPort, BlockBank.WordPort.prodRight,
    productNumeratorPort, blankRegisters, VariableModularMul.cleanRegisters]

/-- Public inversion datum used inside division. -/
def inversionData (x : MAU.Division.Data params.modulus.val) :
    MAU.Inversion.Data params.modulus.val where
  input := x.denominator
  target := 0
  flag := x.flag

/-- Public product datum with a caller-selected multiplicand and target. -/
def productData (x : MAU.Division.Data params.modulus.val)
    (multiplicand accumulator : ZMod params.modulus.val) :
    VariableModularMul.Data where
  multiplier := x.numerator
  multiplicand := multiplicand
  accumulator := accumulator

/-- Canonical low-width fixed word for one field residue. -/
def residueWord (value : ZMod params.modulus.val) :
    Nat.FixedWidth.Word params.width :=
  ⟨value.val, (ZMod.val_lt value).trans
    VariableModularMul.modulus_lt_capacity⟩

/-- Clean physical state with a caller-selected product accumulator. -/
def cleanRegistersWithAccumulator
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val) : RawRegisters :=
  (ModularInversion.cleanRegisters (inversionData x),
    VariableModularMul.cleanRegisters (productData x 0 accumulator))

/-- Clean physical division input. -/
def cleanRegisters (x : MAU.Division.Data params.modulus.val) : RawRegisters :=
  cleanRegistersWithAccumulator x x.target

/-- Loading the two Kaliski input copies and the product numerator into the
input-independent division seed produces exactly the canonical clean division
state. -/
theorem loadBlankRegisters_eq_cleanRegisters
    (denominator : (ZMod params.modulus.val)ˣ)
    (numerator : ZMod params.modulus.val) :
    numeratorPort.set
        (denominatorWorkingPort.set
          (denominatorPreservedPort.set blankRegisters
            (ModularInversion.inputWord denominator))
          (ModularInversion.inputWord denominator))
        (residueWord numerator) =
      cleanRegisters
        ({ denominator := denominator
           numerator := numerator
           target := 0
           flag := false } : MAU.Division.Data params.modulus.val) := by
  rfl

/-- State after inversion has been computed but before its low word is routed
into the product workspace. -/
def inverseReadyRegisters (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val) : RawRegisters :=
  (ModularInversion.cleanRegisters
      (inversionData x).addInverseIntoTarget,
    VariableModularMul.cleanRegisters (productData x 0 accumulator))

/-- State with the inverse routed into the product multiplicand register. -/
def productReadyRegisters (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val) : RawRegisters :=
  (ModularInversion.cleanRegisters
      (inversionData x).addInverseIntoTarget,
    VariableModularMul.cleanRegisters
      (productData x (MAU.Inversion.inverseResidue x.denominator) accumulator))

/-- Public field-bit index in the tail-successor Kaliski target word. -/
def lowInverseIndex (bit : Fin params.width) :
    Fin ModularInversion.arithmeticWidth :=
  ModularInversion.lowInputIndex bit

/-- One low inverse-target bit in the raw inversion adapter. -/
def inverseTargetLowBit (bit : Fin params.width) :
    EncodedBit ModularInversion.rawEncoding :=
  BinaryLabelEncoding.prodRightBit
    (MAU.Inversion.MK.wordEncoding ModularInversion.arithmeticWidth)
    (BinaryLabelEncoding.prod
      (MAU.Inversion.MK.Correction.encoding ModularInversion.tailWidth
        ModularInversion.counterWidth)
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit
      (MAU.Inversion.MK.Correction.encoding ModularInversion.tailWidth
        ModularInversion.counterWidth)
      BinaryLabelEncoding.bool
      ((MAU.Inversion.MK.Correction.publicTargetWord ModularInversion.tailWidth
        ModularInversion.counterWidth).bit (lowInverseIndex bit)))

/-- Low inverse word lifted into the left side of the complete carrier. -/
def inverseSourceWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit ModularInversion.rawEncoding
      VariableModularMul.encoding (inverseTargetLowBit bit)

/-- Product multiplicand word lifted into the right side of the carrier. -/
def productTargetWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit ModularInversion.rawEncoding
      VariableModularMul.encoding
      (VariableModularMul.inPlaceMultiplicandBit bit)

/-- Public quotient accumulator in the product half of the division carrier. -/
def quotientWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit ModularInversion.rawEncoding
      VariableModularMul.encoding (VariableModularMul.accumulatorBit bit)

@[simp] theorem quotientWord_get (bit : Fin params.width)
    (state : RawRegisters) :
    (quotientWord.bit bit).get state =
      state.2.accumulator.val.testBit bit.val := by
  change (VariableModularMul.accumulatorBit bit).get state.2 = _
  change (VariableModularMul.rawAccumulatorBit bit).get
    (VariableModularMul.registersEquiv state.2) = _
  exact VariableModularMul.rawAccumulatorBit_get bit
    (VariableModularMul.registersEquiv state.2)

theorem quotientWord_pairwise_ne (left right : Fin params.width)
    (hne : left ≠ right) :
    (quotientWord.bit left).wire ≠ (quotientWord.bit right).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne ModularInversion.rawEncoding
  intro hwire
  apply VariableModularMul.rawAccumulator_pairwise_ne left right hne
  apply Fin.ext
  simpa only [VariableModularMul.accumulatorBit, EncodedBit.relabel] using
    congrArg Fin.val hwire

/-- Read the public quotient accumulator as an exact-width word. -/
def readQuotient (state : RawRegisters) : Nat.FixedWidth.Word params.width :=
  ⟨state.2.accumulator.val, ZMod.val_lt state.2.accumulator⟩

/-- Replace the public quotient accumulator in the product carrier. -/
def setQuotient (state : RawRegisters) (value : Nat.FixedWidth.Word params.width) :
    RawRegisters :=
  (state.1, { state.2 with accumulator := (value.val : VariableModularMul.Word) })

/-- Structural word port for the quotient accumulator. -/
def quotientPort : BlockBank.WordPort rawEncoding params.width where
  word := quotientWord
  read := readQuotient
  set := setQuotient
  set_read := by
    intro state
    rcases state with ⟨inversion, product⟩
    rcases product with ⟨multiplier, accumulator, inPlace, work⟩
    simp [setQuotient, readQuotient]
  read_set := by
    intro state value
    cases state
    apply Fin.ext
    simp [setQuotient, readQuotient, Nat.mod_eq_of_lt value.isLt]
  set_set := by intro state first second; cases state; rfl
  get_bit := by
    intro bit state
    simp [readQuotient]
  pairwise_ne := quotientWord_pairwise_ne
  clear_flip := by
    intro bit state
    rcases state with ⟨inversion, product⟩
    rcases product with ⟨multiplier, accumulator, inPlace, work⟩
    rfl

/-- The routed inverse word and product multiplicand occupy disjoint product
slices. -/
theorem inverseSource_productTarget_ne :
    ∀ bit, (inverseSourceWord.bit bit).wire ≠
      (productTargetWord.bit bit).wire := by
  intro bit
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    ModularInversion.rawEncoding VariableModularMul.encoding
    (VariableModularMul.inPlaceMultiplicandBit bit)
    (inverseTargetLowBit bit)).symm

/-- Literal low-word CNOT routing gates. -/
def loadGates : List (EncodedBit.GateSpec rawEncoding) :=
  EncodedBit.Word.xorIntoGates inverseSourceWord productTargetWord
    inverseSource_productTarget_ne

/-- Total folded action of the low-word routing gate list. -/
def loadStep : RawRegisters → RawRegisters :=
  EncodedBit.GateSpec.stepList loadGates

/-- Frame of the product carrier after erasing only its multiplicand word. -/
structure ProductFrame where
  /-- Preserved public numerator multiplier. -/
  multiplier : VariableModularMul.Word
  /-- Public quotient accumulator. -/
  accumulator : VariableModularMul.Word
  /-- Arithmetic workspace retained around the routed multiplicand. -/
  arithmetic : MAU.Addition.VBECircuit.Registers params.width
  /-- One-bit product cleanup workspace. -/
  work : Bool

/-- Complete division frame after erasing only the routed multiplicand word. -/
abbrev LoadFrame := InversionRaw × ProductFrame

/-- Read the routed product multiplicand as an exact-width word. -/
def readProductMultiplicand (state : RawRegisters) :
    Nat.FixedWidth.Word params.width :=
  ⟨state.2.inPlace.multiplicand.val,
    ZMod.val_lt state.2.inPlace.multiplicand⟩

/-- Erase only the product multiplicand while retaining the surrounding frame. -/
def loadFrame (state : RawRegisters) : LoadFrame :=
  (state.1,
    { multiplier := state.2.multiplier
      accumulator := state.2.accumulator
      arithmetic := state.2.inPlace.arithmetic
      work := state.2.work })

/-- Reinstall a product multiplicand into its retained division frame. -/
def setProductMultiplicand (frame : LoadFrame)
    (value : Nat.FixedWidth.Word params.width) : RawRegisters :=
  (frame.1,
    { multiplier := frame.2.multiplier
      accumulator := frame.2.accumulator
      inPlace :=
        { multiplicand := (value.val : VariableModularMul.Word)
          arithmetic := frame.2.arithmetic }
      work := frame.2.work })

theorem setProductMultiplicand_decompose (state : RawRegisters) :
    setProductMultiplicand (loadFrame state)
      (readProductMultiplicand state) = state := by
  rcases state with ⟨left, right⟩
  rcases right with ⟨multiplier, accumulator, inPlace, work⟩
  rcases inPlace with ⟨multiplicand, arithmetic⟩
  simp [setProductMultiplicand, loadFrame, readProductMultiplicand]

theorem productTargetWord_get (bit : Fin params.width)
    (state : RawRegisters) :
    (productTargetWord.bit bit).get state =
      (readProductMultiplicand state).val.testBit bit.val := by
  change
    (VariableModularMul.inPlaceMultiplicandBit bit).get state.2 = _
  exact VariableModularMul.inPlaceMultiplicandBit_get bit state.2

theorem productTargetWord_pairwise_ne :
    ∀ left right, left ≠ right →
      (productTargetWord.bit left).wire ≠
        (productTargetWord.bit right).wire := by
  intro left right hne
  exact EncodedBit.GateSpec.prodRightWire_ne ModularInversion.rawEncoding
    (VariableModularMul.inPlaceMultiplicandBit_pairwise_ne left right hne)

theorem productTarget_inverseSource_cross_ne :
    ∀ sourceBit targetBit,
      (productTargetWord.bit targetBit).wire ≠
        (inverseSourceWord.bit sourceBit).wire := by
  intro sourceBit targetBit
  exact EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    ModularInversion.rawEncoding VariableModularMul.encoding
    (VariableModularMul.inPlaceMultiplicandBit targetBit)
    (inverseTargetLowBit sourceBit)

theorem loadFrame_flip (bit : Fin params.width) (state : RawRegisters) :
    loadFrame ((productTargetWord.bit bit).flip state) = loadFrame state := by
  rfl

@[simp] theorem inverseSourceWord_get_inverseReady
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val) (bit : Fin params.width) :
    (inverseSourceWord.bit bit).get (inverseReadyRegisters x accumulator) =
      (residueWord (MAU.Inversion.inverseResidue x.denominator)).val.testBit
        bit.val := by
  change
    ((MAU.Inversion.MK.Correction.publicTargetWord ModularInversion.tailWidth
      ModularInversion.counterWidth).bit (lowInverseIndex bit)).get
        (ModularInversion.cleanRegisters
          (inversionData x).addInverseIntoTarget).2.1 = _
  rw [MAU.Inversion.MK.Correction.publicTargetWord_get]
  simp only [ModularInversion.cleanRegisters, inversionData,
    MAU.Inversion.Data.addInverseIntoTarget, residueWord, lowInverseIndex,
    MAU.Inversion.MK.Correction.cleanCorrectionRegisters, zero_add]
  change
    ((MAU.Inversion.inverseResidue x.denominator).val %
      2 ^ ModularInversion.arithmeticWidth).testBit bit.val =
      (MAU.Inversion.inverseResidue x.denominator).val.testBit bit.val
  rw [Nat.mod_eq_of_lt]
  rw [ModularInversion.arithmeticWidth_eq]
  exact (ZMod.val_lt _).trans VariableModularMul.modulus_lt_capacity

/-- Loading the inverse into a clean product multiplicand establishes the
canonical product-ready state. -/
theorem loadStep_inverseReady (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val) :
    loadStep (inverseReadyRegisters x accumulator) =
      productReadyRegisters x accumulator := by
  have h := EncodedBit.Word.xorIntoStep_eq_set_of_clean
    inverseSourceWord productTargetWord inverseSource_productTarget_ne
    readProductMultiplicand loadFrame setProductMultiplicand
    setProductMultiplicand_decompose productTargetWord_get
    productTargetWord_pairwise_ne productTarget_inverseSource_cross_ne
    loadFrame_flip (inverseReadyRegisters x accumulator)
    (residueWord (MAU.Inversion.inverseResidue x.denominator))
    (by simp [readProductMultiplicand, inverseReadyRegisters,
      VariableModularMul.cleanRegisters, productData,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState])
    (fun bit => inverseSourceWord_get_inverseReady x accumulator bit)
  simpa [loadStep, loadGates, EncodedBit.Word.xorIntoStep,
    productReadyRegisters, inverseReadyRegisters,
    setProductMultiplicand, loadFrame, readProductMultiplicand, residueWord,
    VariableModularMul.cleanRegisters, productData,
    MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using h

/-- Casting a canonical field representative into an `f`-bit product word
does not change its natural value. -/
theorem residueCast_val
    (value : ZMod params.modulus.val) :
    ((value.val : VariableModularMul.Word)).val = value.val := by
  exact ZMod.val_natCast_of_lt
    ((ZMod.val_lt value).trans VariableModularMul.modulus_lt_capacity)

@[simp] theorem fieldCast_val (value : ZMod params.modulus.val) :
    (value.cast : VariableModularMul.Word).val = value.val := by
  exact ZMod.val_cast_eq_val_of_lt
    ((ZMod.val_lt value).trans VariableModularMul.modulus_lt_capacity)

private theorem cleanRegisters_injective : Function.Injective cleanRegisters := by
  intro left right h
  rcases left with ⟨leftDenominator, leftNumerator, leftTarget, leftFlag⟩
  rcases right with ⟨rightDenominator, rightNumerator, rightTarget, rightFlag⟩
  have hdenominatorVal := congrArg (fun state => state.1.1.val) h
  have hdenominator : leftDenominator = rightDenominator := by
    apply Units.ext
    apply ZMod.val_injective
    simpa [cleanRegisters, cleanRegistersWithAccumulator, inversionData,
      ModularInversion.cleanRegisters, ModularInversion.inputWord]
      using hdenominatorVal
  have hnumeratorVal := congrArg (fun state => state.2.multiplier.val) h
  have hnumerator : leftNumerator = rightNumerator := by
    apply ZMod.val_injective
    simpa [cleanRegisters, cleanRegistersWithAccumulator, productData,
      VariableModularMul.cleanRegisters] using hnumeratorVal
  have htargetVal := congrArg (fun state => state.2.accumulator.val) h
  have htarget : leftTarget = rightTarget := by
    apply ZMod.val_injective
    simpa [cleanRegisters, cleanRegistersWithAccumulator, productData,
      VariableModularMul.cleanRegisters] using htargetVal
  have hflag : leftFlag = rightFlag := by
    simpa [cleanRegisters, cleanRegistersWithAccumulator, inversionData,
      ModularInversion.cleanRegisters]
      using congrArg (fun state => state.1.2.2) h
  cases hdenominator
  cases hnumerator
  cases htarget
  cases hflag
  rfl

/-- Faithful public division encoding into the fully clean physical carrier. -/
def encoding : BinaryLabelEncoding (MAU.Division.Data params.modulus.val) where
  width := rawEncoding.width
  encode := fun x => rawEncoding.encode (cleanRegisters x)
  encode_injective := by
    intro left right h
    exact cleanRegisters_injective (rawEncoding.encode_injective h)

/-- Exact width of a width-`f` composed inversion and product carrier. -/
def physicalWidthFor (f : Nat) : Nat :=
  24 * f + 19 + 3 * ModularInversion.counterWidthFor f

/-- Exact width of the composed inversion and product carrier. -/
theorem encoding_width_exact : encoding.width = physicalWidthFor params.width := by
  change ModularInversion.rawEncoding.width +
      VariableModularMul.encoding.width = _
  have hinversion : ModularInversion.rawEncoding.width =
      ModularInversion.physicalWidthFor params.width :=
    ModularInversion.encoding_width_exact
  have hproduct : VariableModularMul.encoding.width =
      VariableModularMul.physicalWidthFor params.width :=
    VariableModularMul.encoding_width_exact
  calc
    ModularInversion.rawEncoding.width + VariableModularMul.encoding.width =
        ModularInversion.physicalWidthFor params.width +
          VariableModularMul.physicalWidthFor params.width := by
      rw [hinversion, hproduct]
    _ = physicalWidthFor params.width := by
      simp only [ModularInversion.physicalWidthFor,
        VariableModularMul.physicalWidthFor, physicalWidthFor]
      omega

/-- Literal inversion schedule lifted over the untouched product carrier. -/
def inverseProgramGates : List (EncodedBit.GateSpec rawEncoding) :=
  ModularInversion.gates.map
    (EncodedBit.GateSpec.prodLeft VariableModularMul.encoding)

/-- Literal variable-multiplication schedule, relabeled to the named product
carrier and lifted over the retained inversion carrier. -/
def productProgramGates : List (EncodedBit.GateSpec rawEncoding) :=
  (VariableModularMulSchedule.gates.map
    (EncodedBit.GateSpec.relabel VariableModularMul.registersEquiv)).map
    (EncodedBit.GateSpec.prodRight ModularInversion.rawEncoding)

/-- Complete inverse/load/product/unload/uncompute gate schedule. -/
def gates : List (EncodedBit.GateSpec rawEncoding) :=
  inverseProgramGates ++ loadGates ++ productProgramGates ++
    loadGates.reverse ++ inverseProgramGates.reverse

/-- Lifting the inversion schedule over the untouched product carrier changes
only wire addresses. -/
theorem inverseProgramGates_length :
    inverseProgramGates.length = ModularInversion.gates.length := by
  unfold inverseProgramGates
  exact EncodedBit.GateSpec.length_prodLeft VariableModularMul.encoding _

/-- The lifted inversion schedule preserves its ordered primitive-event
trace. -/
theorem inverseProgramGates_map_event :
    inverseProgramGates.map (EncodedBit.GateSpec.event .empty) =
      ModularInversion.gates.map (EncodedBit.GateSpec.event .empty) := by
  unfold inverseProgramGates
  exact EncodedBit.GateSpec.map_event_prodLeft VariableModularMul.encoding _

/-- Relabeling and lifting the multiplication schedule change only wire
addresses. -/
theorem productProgramGates_length :
    productProgramGates.length = VariableModularMulSchedule.gates.length := by
  unfold productProgramGates
  simp only [List.length_map]

/-- The lifted product schedule preserves its ordered primitive-event trace. -/
theorem productProgramGates_map_event :
    productProgramGates.map (EncodedBit.GateSpec.event .empty) =
      VariableModularMulSchedule.gates.map (EncodedBit.GateSpec.event .empty) := by
  unfold productProgramGates
  exact
    (EncodedBit.GateSpec.map_event_prodRight ModularInversion.rawEncoding _).trans
      (EncodedBit.GateSpec.map_event_relabel .empty
        VariableModularMul.registersEquiv _)

/-- The low-word inverse router has one primitive gate per field bit. -/
theorem loadGates_length : loadGates.length = params.width := by
  exact EncodedBit.Word.xorIntoGates_length
    inverseSourceWord productTargetWord inverseSource_productTarget_ne

/-- The low-word inverse router contains exactly one CNOT per field bit. -/
theorem loadGates_cnotMultiplicity_sum :
    (loadGates.map EncodedBit.GateSpec.cnotMultiplicity).sum = params.width := by
  exact EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    inverseSourceWord productTargetWord inverseSource_productTarget_ne

/-- The low-word inverse router contains no X gates. -/
theorem loadGates_xMultiplicity_sum :
    (loadGates.map EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  apply List.sum_eq_zero
  intro count hcount
  rcases List.mem_map.mp hcount with ⟨gate, hgate, rfl⟩
  rw [loadGates, EncodedBit.Word.xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨_bit, rfl⟩
  rfl

/-- The low-word inverse router contains no Toffoli gates. -/
theorem loadGates_toffoliMultiplicity_sum :
    (loadGates.map EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  exact EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum
    inverseSourceWord productTargetWord inverseSource_productTarget_ne

/-- Exact primitive-event length decomposition of the complete division
schedule. -/
theorem gates_length :
    gates.length =
      2 * ModularInversion.gates.length + 2 * params.width +
        VariableModularMulSchedule.gates.length := by
  simp only [gates, List.length_append, List.length_reverse,
    inverseProgramGates_length, productProgramGates_length, loadGates_length]
  omega

/-- Width-only primitive-leaf bound for a width-`f`
inverse/load/product/unload/uncompute ledger. -/
def gateLengthBoundFor (f : Nat) : Nat :=
  2 * ModularInversion.gateLengthBoundFor f + 2 * f +
    VariableModularMulSchedule.eventCountBoundFor f

/-- Width-only literal-X bound for a width-`f`
inverse/load/product/unload/uncompute ledger. -/
def xBoundFor (f : Nat) : Nat :=
  2 * ModularInversion.xBoundFor f +
    VariableModularMulSchedule.xBoundFor f

/-- Width-only CNOT-coordinate bound for a width-`f`
inverse/load/product/unload/uncompute ledger. -/
def cnotBoundFor (f : Nat) : Nat :=
  2 * ModularInversion.cnotBoundFor f + 2 * f +
    VariableModularMulSchedule.cnotBoundFor f

/-- Width-only Toffoli-coordinate bound for a width-`f`
inverse/load/product/unload/uncompute ledger. -/
def toffoliBoundFor (f : Nat) : Nat :=
  2 * ModularInversion.toffoliBoundFor f +
    VariableModularMulSchedule.toffoliBoundFor f

/-- Width-only unit-depth bound for a width-`f`
inverse/load/product/unload/uncompute ledger. -/
def unitDepthBoundFor (f : Nat) : Nat :=
  gateLengthBoundFor f

/-- Width-only primitive-leaf bound for the instantiated
inverse/load/product/unload/uncompute ledger. -/
def gateLengthBound : Nat :=
  gateLengthBoundFor params.width

/-- Width-only literal-X bound for the instantiated
inverse/load/product/unload/uncompute ledger. -/
def xBound : Nat :=
  xBoundFor params.width

/-- Width-only CNOT-coordinate bound for the instantiated
inverse/load/product/unload/uncompute ledger. -/
def cnotBound : Nat :=
  cnotBoundFor params.width

/-- Width-only Toffoli-coordinate bound for the instantiated
inverse/load/product/unload/uncompute ledger. -/
def toffoliBound : Nat :=
  toffoliBoundFor params.width

/-- Width-only unit-depth bound for the instantiated
inverse/load/product/unload/uncompute ledger. -/
def unitDepthBound : Nat :=
  unitDepthBoundFor params.width

/-- The literal division schedule obeys its named width-only bound. -/
theorem gates_length_le : gates.length ≤ gateLengthBound := by
  have hinverse : ModularInversion.gates.length ≤
      ModularInversion.gateLengthBoundFor params.width := by
    simpa only [ModularInversion.gateLengthBound] using
      ModularInversion.gates_length_le
  have hproduct : VariableModularMulSchedule.gates.length ≤
      VariableModularMulSchedule.eventCountBoundFor params.width := by
    simpa only [VariableModularMulSchedule.eventCountBound] using
      VariableModularMulSchedule.gates_length_le
  rw [gates_length]
  unfold gateLengthBound gateLengthBoundFor
  omega

/-- Exact X decomposition of the complete division schedule, projected from
the literal gate list. -/
theorem gates_xMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum =
      2 * (ModularInversion.gates.map
        EncodedBit.GateSpec.xMultiplicity).sum +
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.xMultiplicity).sum := by
  have hinverse := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    inverseProgramGates_map_event
  have hproduct := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    productProgramGates_map_event
  simp only [gates, List.map_append, List.sum_append, List.map_reverse,
    List.sum_reverse]
  rw [hinverse, hproduct, loadGates_xMultiplicity_sum]
  omega

/-- The complete literal division schedule obeys its named width-only
X-coordinate bound. -/
theorem gates_xMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ xBound := by
  rw [gates_xMultiplicity_sum]
  have hinverse :
      (ModularInversion.gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤
        ModularInversion.xBoundFor params.width := by
    simpa only [ModularInversion.xBound] using
      ModularInversion.gates_xMultiplicity_sum_le
  have hproduct :
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.xMultiplicity).sum ≤
        VariableModularMulSchedule.xBoundFor params.width := by
    simpa only [VariableModularMulSchedule.xBound] using
      VariableModularMulSchedule.gates_xMultiplicity_sum_le
  unfold xBound xBoundFor
  omega

/-- Exact CNOT decomposition of the complete division schedule, projected
from the literal gate list. -/
theorem gates_cnotMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * (ModularInversion.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum +
      2 * params.width +
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum := by
  have hinverse := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    inverseProgramGates_map_event
  have hproduct := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    productProgramGates_map_event
  simp only [gates, List.map_append, List.sum_append, List.map_reverse,
    List.sum_reverse]
  rw [hinverse, hproduct, loadGates_cnotMultiplicity_sum]
  omega

/-- The complete literal division schedule obeys its named width-only
CNOT-coordinate bound. -/
theorem gates_cnotMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤ cnotBound := by
  rw [gates_cnotMultiplicity_sum]
  have hinverse :
      (ModularInversion.gates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤
        ModularInversion.cnotBoundFor params.width := by
    simpa only [ModularInversion.cnotBound] using
      ModularInversion.gates_cnotMultiplicity_sum_le
  have hproduct :
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
        VariableModularMulSchedule.cnotBoundFor params.width := by
    simpa only [VariableModularMulSchedule.cnotBound] using
      VariableModularMulSchedule.gates_cnotMultiplicity_sum_le
  unfold cnotBound cnotBoundFor
  omega

/-- Exact Toffoli decomposition of the complete division schedule, projected
from the literal gate list. -/
theorem gates_toffoliMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * (ModularInversion.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum +
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  have hinverse := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    inverseProgramGates_map_event
  have hproduct := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    productProgramGates_map_event
  simp only [gates, List.map_append, List.sum_append, List.map_reverse,
    List.sum_reverse]
  rw [hinverse, hproduct, loadGates_toffoliMultiplicity_sum]
  omega

/-- The complete literal division schedule obeys its named width-only
Toffoli-coordinate bound. -/
theorem gates_toffoliMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      toffoliBound := by
  rw [gates_toffoliMultiplicity_sum]
  have hinverse :
      (ModularInversion.gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
        ModularInversion.toffoliBoundFor params.width := by
    simpa only [ModularInversion.toffoliBound] using
      ModularInversion.gates_toffoliMultiplicity_sum_le
  have hproduct :
      (VariableModularMulSchedule.gates.map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
        VariableModularMulSchedule.toffoliBoundFor params.width := by
    simpa only [VariableModularMulSchedule.toffoliBound] using
      VariableModularMulSchedule.gates_toffoliMultiplicity_sum_le
  unfold toffoliBound toffoliBoundFor
  omega

/-- Actual division circuit compiled from its complete gate schedule. -/
def circuit : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates

/-- The literal public division circuit obeys its closed unit-depth bound. -/
theorem circuit_unitDepth_le :
    circuit.evaluatedEventDepth (fun _ => 1) ≤ unitDepthBound := by
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    gates).evaluatedEventDepth
      (fun _ => 1) ≤ _
  rw [EncodedBit.GateSpec.programList_evaluatedEventDepth_unit]
  exact gates_length_le

/-- The lifted inversion list has exactly the named raw-carrier action. -/
theorem inverseProgramGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList inverseProgramGates state =
      (ModularInversion.rawStep state.1, state.2) := by
  simp only [inverseProgramGates, rawEncoding,
    EncodedBit.GateSpec.stepList_prodLeft,
    ModularInversion.gates_stepList]

/-- The lifted and relabeled product list has exactly the named schedule
action on the product carrier. -/
theorem productProgramGates_stepList (state : RawRegisters) :
    EncodedBit.GateSpec.stepList productProgramGates state =
      (state.1, VariableModularMulSchedule.step state.2) := by
  simp only [productProgramGates, rawEncoding,
    EncodedBit.GateSpec.stepList_prodRight]
  rw [EncodedBit.GateSpec.stepList_relabel]
  rw [VariableModularMulSchedule.gates_stepList]
  rw [VariableModularMulSchedule.rawStep_registersEquiv]
  simp only [Equiv.symm_apply_apply]

/-- The lifted inversion gate fold establishes the inverse-ready state. -/
theorem inverseProgramGates_clean
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val) :
    EncodedBit.GateSpec.stepList inverseProgramGates
        (cleanRegistersWithAccumulator x accumulator) =
      inverseReadyRegisters x accumulator := by
  rw [inverseProgramGates_stepList]
  have hstep :
      ModularInversion.rawStep
          (cleanRegistersWithAccumulator x accumulator).1 =
        (inverseReadyRegisters x accumulator).1 := by
    simpa only [cleanRegistersWithAccumulator, inverseReadyRegisters] using
      (ModularInversion.rawStep_cleanEndpoint (inversionData x))
  apply Prod.ext
  · exact hstep
  · rfl

/-- The lifted product gate fold adds the selected quotient to the accumulator. -/
theorem productProgramGates_productReady
    (x : MAU.Division.Data params.modulus.val)
    (accumulator : ZMod params.modulus.val) :
    EncodedBit.GateSpec.stepList productProgramGates
        (productReadyRegisters x accumulator) =
      productReadyRegisters x
        (accumulator + MAU.Division.quotientResidue
          x.denominator x.numerator) := by
  rw [productProgramGates_stepList]
  have hstep :
      VariableModularMulSchedule.step
          (productReadyRegisters x accumulator).2 =
        (productReadyRegisters x
          (accumulator + MAU.Division.quotientResidue
            x.denominator x.numerator)).2 := by
    simpa only [productReadyRegisters, productData,
      VariableModularMul.Data.addProduct, MAU.Division.quotientResidue] using
      (VariableModularMulSchedule.step_cleanEndpoint
        (productData x (MAU.Inversion.inverseResidue x.denominator)
          accumulator))
  apply Prod.ext
  · rfl
  · exact hstep

/-- The complete literal division schedule maps every clean public carrier to
the corresponding clean quotient-updated carrier. -/
theorem gates_cleanEndpoint
    (x : MAU.Division.Data params.modulus.val) :
    EncodedBit.GateSpec.stepList gates (cleanRegisters x) =
      cleanRegisters x.addQuotientIntoTarget := by
  let result := x.target +
    MAU.Division.quotientResidue x.denominator x.numerator
  have hinverseStart :
      EncodedBit.GateSpec.stepList inverseProgramGates
          (cleanRegistersWithAccumulator x x.target) =
        inverseReadyRegisters x x.target :=
    inverseProgramGates_clean x x.target
  have hloadStart :
      EncodedBit.GateSpec.stepList loadGates
          (inverseReadyRegisters x x.target) =
        productReadyRegisters x x.target := by
    exact loadStep_inverseReady x x.target
  have hproduct :
      EncodedBit.GateSpec.stepList productProgramGates
          (productReadyRegisters x x.target) =
        productReadyRegisters x result := by
    simpa only [result] using productProgramGates_productReady x x.target
  have hloadResult :
      EncodedBit.GateSpec.stepList loadGates
          (inverseReadyRegisters x result) =
        productReadyRegisters x result := by
    exact loadStep_inverseReady x result
  have hunload :
      EncodedBit.GateSpec.stepList loadGates.reverse
          (productReadyRegisters x result) =
        inverseReadyRegisters x result := by
    rw [← hloadResult]
    exact EncodedBit.GateSpec.stepList_reverse_stepList loadGates _
  have hinverseResult :
      EncodedBit.GateSpec.stepList inverseProgramGates
          (cleanRegistersWithAccumulator x result) =
        inverseReadyRegisters x result :=
    inverseProgramGates_clean x result
  have huncompute :
      EncodedBit.GateSpec.stepList inverseProgramGates.reverse
          (inverseReadyRegisters x result) =
        cleanRegistersWithAccumulator x result := by
    rw [← hinverseResult]
    exact EncodedBit.GateSpec.stepList_reverse_stepList inverseProgramGates _
  change EncodedBit.GateSpec.stepList gates
      (cleanRegistersWithAccumulator x x.target) = _
  simp only [gates, EncodedBit.GateSpec.stepList_append]
  rw [hinverseStart, hloadStart, hproduct, hunload, huncompute]
  simp only [result, cleanRegisters, cleanRegistersWithAccumulator,
    MAU.Division.Data.addQuotientIntoTarget, inversionData, productData]

/-- The composed actual circuit realizes public unit-denominator modular
division. -/
theorem realizes : UnitaryCircuit.Realizes encoding circuit
    (MAU.Division.Data.addQuotientIntoTarget) where
  apply_encoded_ket := by
    intro x
    have hrealizes :=
      (EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty gates).apply_encoded_ket
        (cleanRegisters x)
    rw [gates_cleanEndpoint] at hrealizes
    change circuit.applyNormalized
        (NormalizedVector.ket ((QubitLayout.canonical rawEncoding.width).basisEquiv.symm
          (rawEncoding.encode (cleanRegisters x)))) =
      NormalizedVector.ket ((QubitLayout.canonical rawEncoding.width).basisEquiv.symm
        (rawEncoding.encode (cleanRegisters x.addQuotientIntoTarget)))
    exact hrealizes

/-- Structured modular-division witness consumed by generic point addition. -/
def witness : MAU.Division.StructuredCircuitWitness params.modulus.val where
  encoding := encoding
  circuit := circuit
  realizes := realizes

end

end ModularDivision
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic

end
