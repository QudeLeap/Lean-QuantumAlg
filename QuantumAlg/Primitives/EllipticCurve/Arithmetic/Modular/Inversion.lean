/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication.Resource
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.BlockBank
import all QuantumAlg.Primitives.MAU.Inversion.MK.Resource
/-!
# Width-parameterized odd-modulus inversion

This module instantiates the existing fixed-round Montgomery--Kaliski circuit
on an `f`-bit data word.  Its coefficient registers already carry the required
extra bit.  The circuit executes exactly `2f` rounds and uses the source-sized
`clog₂(2f)` padding counter; no modulus bit pattern selects the program.
-/

section

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic
namespace ModularInversion

open Nat.FixedWidth

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

variable [params : VariableModularMul.Parameters]

local instance modulusNeZero : NeZero params.modulus.val :=
  ⟨Nat.ne_of_gt params.modulusPos⟩

/-- Tail parameter whose successor is the source field width. -/
def tailWidthFor (f : Nat) : Nat :=
  f - 1

/-- Kaliski `u,v` word width.  The lower layout allocates its coefficient
margin separately as words of width `f+1`. -/
@[implicit_reducible]
def arithmeticWidthFor (f : Nat) : Nat :=
  (tailWidthFor f).succ

/-- Logarithmic padding-counter width for the exact `2f` fixed schedule. -/
def counterWidthFor (f : Nat) : Nat :=
  Nat.clog 2 (2 * f)

omit params in
/-- The P-256 fixed schedule uses the paper-aligned nine-bit counter. -/
lemma counterWidthFor_256 : counterWidthFor 256 = 9 := by
  norm_num [counterWidthFor]

/-- Tail parameter for the instantiated field. -/
abbrev tailWidth : Nat := tailWidthFor params.width

/-- Arithmetic word width for the instantiated field. -/
abbrev arithmeticWidth : Nat := arithmeticWidthFor params.width

/-- Static counter width for the instantiated field. -/
abbrev counterWidth : Nat := counterWidthFor params.width

/-- The positive declared field width agrees with the lower tail-successor
carrier. -/
lemma arithmeticWidth_eq : arithmeticWidth = params.width := by
  simpa [arithmeticWidth, arithmeticWidthFor, tailWidthFor] using
    Nat.sub_add_cancel params.widthPos

/-- The modulus embedded into the arithmetic-width carrier. -/
abbrev modulusWord : Word arithmeticWidth :=
  ⟨params.modulus.val, by
    simpa only [arithmeticWidth_eq] using
      VariableModularMul.modulus_lt_capacity⟩

/-- Canonical arithmetic-width word for a unit input. -/
def inputWord (u : (ZMod params.modulus.val)ˣ) : Word arithmeticWidth :=
  ⟨(u : ZMod params.modulus.val).val, by
    exact (ZMod.val_lt (u : ZMod params.modulus.val)).trans
      modulusWord.isLt⟩

/-- Final comparison bit required by the fixed-round endpoint. -/
def comparisonIndex : Fin arithmeticWidth :=
  Fin.last tailWidth

/-- A nontrivial modulus fitting the declared word forces at least two field
bits. -/
lemma one_lt_width : 1 < params.width := by
  by_contra h
  have hpos := params.widthPos
  have hmod := params.one_lt_modulus
  have hwidth : params.width = 1 := by omega
  have hfit := VariableModularMul.modulus_lt_capacity
  have hpow := congrArg (fun width : Nat => 2 ^ width) hwidth
  norm_num at hpow
  omega

/-- The logarithmic counter has a nonempty carry-work suffix. -/
lemma one_lt_counterWidth : 1 < counterWidth := by
  apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < (2 : Nat))).2
  norm_num
  have hwidth := one_lt_width
  omega

/-- Reusable low counter-work bit. -/
def workIndex : Fin (counterWidth - 1) :=
  ⟨0, by
    have := one_lt_counterWidth
    omega⟩

/-- The exact `2f` fixed-round budget fits the logarithmic counter capacity.
Equality is intentional when `2f` is a power of two. -/
lemma counter_capacity : 2 * arithmeticWidth ≤ 2 ^ counterWidth := by
  rw [arithmeticWidth_eq]
  exact Nat.le_pow_clog (by norm_num : 1 < (2 : Nat)) (2 * params.width)

/-- The selected comparison bit is the final arithmetic-word bit. -/
lemma comparisonIndex_final : comparisonIndex.val + 1 = arithmeticWidth := by
  simp [comparisonIndex, arithmeticWidth, arithmeticWidthFor, tailWidth,
    tailWidthFor]

/-- Raw physical carrier: a preserved input copy, the Kaliski correction
workspace, and the public clean flag. -/
abbrev RawRegisters :=
  Word arithmeticWidth ×
    (MAU.Inversion.MK.Correction.Registers tailWidth counterWidth × Bool)

/-- Raw binary layout of the inversion adapter. -/
@[implicit_reducible]
def rawEncoding : BinaryLabelEncoding RawRegisters :=
  BinaryLabelEncoding.prod
    (MAU.Inversion.MK.wordEncoding arithmeticWidth)
    (BinaryLabelEncoding.prod
      (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
      BinaryLabelEncoding.bool)

/-! ## Input-independent loading boundary -/

/-- Complete arithmetic-width view of the preserved inversion input copy. -/
def preservedInputWord : EncodedBit.Word rawEncoding arithmeticWidth where
  bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit
      (MAU.Inversion.MK.wordEncoding arithmeticWidth)
      (BinaryLabelEncoding.prod
        (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.finIdentityBit arithmeticWidth
        (WireAddress.littleEndianWire bit))

/-- Complete arithmetic-width view of the Kaliski working `v` input copy. -/
def workingInputWord : EncodedBit.Word rawEncoding arithmeticWidth where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit
      (MAU.Inversion.MK.wordEncoding arithmeticWidth)
      (BinaryLabelEncoding.prod
        (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodLeftBit
        (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
        BinaryLabelEncoding.bool
        (MAU.Inversion.MK.Correction.liftFixedBit tailWidth counterWidth
          (MAU.Inversion.MK.Circuit.liftCoeffStateBit
            tailWidth counterWidth
            ((MAU.Inversion.MK.coeffAdderVWord arithmeticWidth counterWidth).bit
              bit))))

/-- Read the complete preserved inversion input word. -/
def readPreservedInput (state : RawRegisters) : Word arithmeticWidth :=
  state.1

/-- Replace the complete preserved inversion input word. -/
def setPreservedInput (state : RawRegisters) (value : Word arithmeticWidth) :
    RawRegisters :=
  (value, state.2)

/-- Read the complete working Kaliski `v` input word. -/
def readWorkingInput (state : RawRegisters) : Word arithmeticWidth :=
  (MAU.Inversion.MK.Circuit.dataRegisters tailWidth counterWidth
    state.2.1.1.1).v

/-- Replace only the complete working Kaliski `v` input word, preserving all
other arithmetic, route-history, correction, target, and flag fields. -/
def setWorkingInput (state : RawRegisters) (value : Word arithmeticWidth) :
    RawRegisters :=
  let correction := state.2.1
  let fixed := correction.1.1
  let pathControl := fixed.1
  let pathWork := pathControl.1
  let fullRoundWork := pathWork.1
  let coeffState := fullRoundWork.1
  let comparisonState := coeffState.1
  let data := comparisonState.1
  let updatedData := { data with v := value }
  let updatedComparisonState := (updatedData, comparisonState.2)
  let updatedCoeffState := (updatedComparisonState, coeffState.2)
  let updatedFullRoundWork := (updatedCoeffState, fullRoundWork.2)
  let updatedPathWork := (updatedFullRoundWork, pathWork.2)
  let updatedPathControl := (updatedPathWork, pathControl.2)
  let updatedFixed := (updatedPathControl, fixed.2)
  let updatedCorrection := ((updatedFixed, correction.1.2), correction.2)
  (state.1, (updatedCorrection, state.2.2))

@[simp] lemma preservedInputWord_get (bit : Fin arithmeticWidth)
    (state : RawRegisters) :
    (preservedInputWord.bit bit).get state =
      (readPreservedInput state).val.testBit bit.val := by
  change
    (BinaryLabelEncoding.finIdentityBit arithmeticWidth
      (WireAddress.littleEndianWire bit)).get state.1 =
        state.1.val.testBit bit.val
  simp [BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit]

@[simp] lemma workingInputWord_get (bit : Fin arithmeticWidth)
    (state : RawRegisters) :
    (workingInputWord.bit bit).get state =
      (readWorkingInput state).val.testBit bit.val := by
  exact MAU.Inversion.MK.coeffAdderVWord_get_testBit
    arithmeticWidth counterWidth bit state.2.1.1.1.1.1.1.1

lemma preservedInputWord_pairwise_ne (left right : Fin arithmeticWidth)
    (hne : left ≠ right) :
    (preservedInputWord.bit left).wire ≠
      (preservedInputWord.bit right).wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne
  intro hwire
  apply hne
  exact WireAddress.bitIndex_injective hwire

lemma workingInputWord_pairwise_ne (left right : Fin arithmeticWidth)
    (hne : left ≠ right) :
    (workingInputWord.bit left).wire ≠
      (workingInputWord.bit right).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne
  apply EncodedBit.GateSpec.prodLeftWire_ne
  simp only [MAU.Inversion.MK.Correction.liftFixedBit,
    MAU.Inversion.MK.Circuit.liftCoeffStateBit,
    MAU.Inversion.MK.Circuit.liftFullRoundBit,
    MAU.Inversion.MK.Circuit.liftPathControlBit,
    MAU.Inversion.MK.liftFullRoundWorkBitToPathControlWork,
    MAU.Inversion.MK.liftFullRoundWorkBitToPathWork,
    MAU.Inversion.MK.liftFullRoundPathWorkBitToControlWork,
    MAU.Inversion.MK.liftCoeffAdderStateBitToFullRoundWork]
  apply EncodedBit.GateSpec.prodLeftWire_ne
  apply EncodedBit.GateSpec.prodLeftWire_ne
  apply EncodedBit.GateSpec.prodLeftWire_ne
  apply EncodedBit.GateSpec.prodLeftWire_ne
  apply EncodedBit.GateSpec.prodLeftWire_ne
  apply EncodedBit.GateSpec.prodLeftWire_ne
  exact MAU.Inversion.MK.coeffAdderVWordBit_coeffAdderVWordBit_wire_ne
    arithmeticWidth counterWidth left right hne

/-- Structural port for the complete preserved inversion input copy. -/
def preservedInputPort : BlockBank.WordPort rawEncoding arithmeticWidth where
  word := preservedInputWord
  read := readPreservedInput
  set := setPreservedInput
  set_read := by intro state; cases state; rfl
  read_set := by intro state value; rfl
  set_set := by intro state first second; rfl
  get_bit := preservedInputWord_get
  pairwise_ne := preservedInputWord_pairwise_ne
  clear_flip := by intro bit state; cases state; rfl

/-- Structural port for the complete working Kaliski `v` input copy. -/
def workingInputPort : BlockBank.WordPort rawEncoding arithmeticWidth where
  word := workingInputWord
  read := readWorkingInput
  set := setWorkingInput
  set_read := by
    intro state
    rcases state with ⟨preserved, ⟨correction, flag⟩⟩
    rcases correction with ⟨⟨fixed, vbe⟩, target⟩
    rcases fixed with ⟨pathControl, history⟩
    rcases pathControl with ⟨pathWork, controlWork⟩
    rcases pathWork with ⟨fullRoundWork, path⟩
    rcases fullRoundWork with ⟨coeffState, counterWork⟩
    rcases coeffState with ⟨comparisonState, coeffWork⟩
    rcases comparisonState with ⟨data, comparisonWork⟩
    cases data
    rfl
  read_set := by
    intro state value
    rcases state with ⟨preserved, ⟨correction, flag⟩⟩
    rcases correction with ⟨⟨fixed, vbe⟩, target⟩
    rcases fixed with ⟨pathControl, history⟩
    rcases pathControl with ⟨pathWork, controlWork⟩
    rcases pathWork with ⟨fullRoundWork, path⟩
    rcases fullRoundWork with ⟨coeffState, counterWork⟩
    rcases coeffState with ⟨comparisonState, coeffWork⟩
    rcases comparisonState with ⟨data, comparisonWork⟩
    cases data
    rfl
  set_set := by
    intro state first second
    rcases state with ⟨preserved, ⟨correction, flag⟩⟩
    rcases correction with ⟨⟨fixed, vbe⟩, target⟩
    rcases fixed with ⟨pathControl, history⟩
    rcases pathControl with ⟨pathWork, controlWork⟩
    rcases pathWork with ⟨fullRoundWork, path⟩
    rcases fullRoundWork with ⟨coeffState, counterWork⟩
    rcases coeffState with ⟨comparisonState, coeffWork⟩
    rcases comparisonState with ⟨data, comparisonWork⟩
    cases data
    rfl
  get_bit := workingInputWord_get
  pairwise_ne := workingInputWord_pairwise_ne
  clear_flip := by
    intro bit state
    rcases state with ⟨preserved, ⟨correction, flag⟩⟩
    rcases correction with ⟨⟨fixed, vbe⟩, target⟩
    rcases fixed with ⟨pathControl, history⟩
    rcases pathControl with ⟨pathWork, controlWork⟩
    rcases pathWork with ⟨fullRoundWork, path⟩
    rcases fullRoundWork with ⟨coeffState, counterWork⟩
    rcases coeffState with ⟨comparisonState, coeffWork⟩
    rcases comparisonState with ⟨data, comparisonWork⟩
    cases data
    rfl

/-- Reindex one public field bit into the definitionally tail-successor
Kaliski word. -/
def lowInputIndex (bit : Fin params.width) : Fin arithmeticWidth :=
  Fin.cast arithmeticWidth_eq.symm bit

/-- Low public-width view of the preserved inversion input copy. -/
def preservedInputLowWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit
      (MAU.Inversion.MK.wordEncoding arithmeticWidth)
      (BinaryLabelEncoding.prod
        (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.finIdentityBit arithmeticWidth
        (WireAddress.littleEndianWire (lowInputIndex bit)))

/-- Low public-width view of the Kaliski working `v` input copy. -/
def workingInputLowWord : EncodedBit.Word rawEncoding params.width where
  bit := fun bit =>
    BinaryLabelEncoding.prodRightBit
      (MAU.Inversion.MK.wordEncoding arithmeticWidth)
      (BinaryLabelEncoding.prod
        (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodLeftBit
        (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
        BinaryLabelEncoding.bool
        (MAU.Inversion.MK.Correction.liftFixedBit tailWidth counterWidth
          (MAU.Inversion.MK.Circuit.liftCoeffStateBit
            tailWidth counterWidth
            ((MAU.Inversion.MK.coeffAdderVWord arithmeticWidth counterWidth).bit
              (lowInputIndex bit)))))

/-- The preserved and working Kaliski input copies occupy disjoint product
slices. -/
lemma preservedInput_workingInput_wire_ne (bit : Fin params.width) :
    (preservedInputLowWord.bit bit).wire ≠
      (workingInputLowWord.bit bit).wire :=
  Ne.symm
    (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      (MAU.Inversion.MK.wordEncoding arithmeticWidth)
      (BinaryLabelEncoding.prod
        (MAU.Inversion.MK.Correction.encoding tailWidth counterWidth)
        BinaryLabelEncoding.bool)
      _ _)

/-- Canonical input-independent Kaliski seed.  It has the same fixed modulus,
clean work, route history, correction workspace, target, and flag as a public
clean state, but both input copies are zero until a physical loader fills
them. -/
def blankRegisters : RawRegisters :=
  let input : Word arithmeticWidth := 0
  (input,
    (MAU.Inversion.MK.Correction.cleanCorrectionRegisters
      tailWidth counterWidth params.modulus.val
      (MAU.Inversion.MK.Circuit.withCleanRouteHistory
        arithmeticWidth counterWidth
        (MAU.Inversion.MK.initialRegisters
          arithmeticWidth counterWidth modulusWord input))
      0 0,
    false))

/-- Clean physical representation of the public inversion data. -/
def cleanRegisters (x : MAU.Inversion.Data params.modulus.val) : RawRegisters :=
  let input := inputWord x.input
  (input,
    (MAU.Inversion.MK.Correction.cleanCorrectionRegisters
      tailWidth counterWidth params.modulus.val
      (MAU.Inversion.MK.Circuit.withCleanRouteHistory
        arithmeticWidth counterWidth
        (MAU.Inversion.MK.initialRegisters
          arithmeticWidth counterWidth modulusWord input))
      0 x.target,
    x.flag))

private lemma inputWord_injective : Function.Injective inputWord := by
  intro left right h
  apply Units.ext
  apply ZMod.val_injective
  exact congrArg (fun word => word.val) h

private lemma cleanRegisters_injective : Function.Injective cleanRegisters := by
  intro left right h
  rcases left with ⟨leftInput, leftTarget, leftFlag⟩
  rcases right with ⟨rightInput, rightTarget, rightFlag⟩
  change
    (inputWord leftInput,
      (MAU.Inversion.MK.Correction.cleanCorrectionRegisters
        tailWidth counterWidth params.modulus.val
        (MAU.Inversion.MK.Circuit.withCleanRouteHistory
          arithmeticWidth counterWidth
          (MAU.Inversion.MK.initialRegisters arithmeticWidth counterWidth
            modulusWord (inputWord leftInput)))
        0 leftTarget,
      leftFlag)) = _ at h
  have hinput : leftInput = rightInput :=
    inputWord_injective (congrArg (fun x => x.1) h)
  have hflag : leftFlag = rightFlag :=
    congrArg (fun x => x.2.2) h
  have htargetWord := congrArg (fun x => x.2.1.2) h
  have htarget : leftTarget = rightTarget := by
    apply ZMod.val_injective
    have hval := congrArg (fun word => word.val) htargetWord
    have hleftLt : leftTarget.val < 2 ^ arithmeticWidth :=
      (ZMod.val_lt leftTarget).trans modulusWord.isLt
    have hrightLt : rightTarget.val < 2 ^ arithmeticWidth :=
      (ZMod.val_lt rightTarget).trans modulusWord.isLt
    change leftTarget.val % 2 ^ arithmeticWidth =
      rightTarget.val % 2 ^ arithmeticWidth at hval
    rw [Nat.mod_eq_of_lt hleftLt, Nat.mod_eq_of_lt hrightLt] at hval
    exact hval
  cases hinput
  cases htarget
  cases hflag
  rfl

/-- Faithful public-data encoding into the clean Kaliski carrier. -/
def encoding : BinaryLabelEncoding (MAU.Inversion.Data params.modulus.val) where
  width := rawEncoding.width
  encode := fun x => rawEncoding.encode (cleanRegisters x)
  encode_injective := by
    intro left right h
    exact cleanRegisters_injective (rawEncoding.encode_injective h)

/-- Exact qubit width of the width-`f` Kaliski inversion adapter, including
the three physical occurrences of the logarithmic counter width. -/
def physicalWidthFor (f : Nat) : Nat :=
  17 * f + 14 + 3 * counterWidthFor f

/-- Exact qubit width of the padded Kaliski inversion adapter. -/
lemma encoding_width_exact : encoding.width = physicalWidthFor params.width := by
  have hwidth := one_lt_width
  have hcounter := one_lt_counterWidth
  have htail : params.width - 1 + 1 = params.width :=
    Nat.sub_add_cancel params.widthPos
  have hcounterTail :
      1 + (Nat.clog 2 (2 * params.width) - 1) =
        Nat.clog 2 (2 * params.width) := by
    change 1 < Nat.clog 2 (2 * params.width) at hcounter
    omega
  simp only [encoding, rawEncoding, arithmeticWidthFor, tailWidthFor,
    Nat.succ_eq_add_one, tailWidth, counterWidth, counterWidthFor,
    MAU.Inversion.MK.Correction.encoding,
    MAU.Inversion.MK.Circuit.encoding,
    MAU.Inversion.MK.registersWithFullRoundPathControlWorkEncoding,
    MAU.Inversion.MK.registersWithFullRoundPathWorkEncoding,
    MAU.Inversion.MK.registersWithFullRoundWorkEncoding,
    MAU.Inversion.MK.registersWithCoeffAdderWorkEncoding,
    MAU.Inversion.MK.registersWithComparisonWorkEncoding,
    MAU.Inversion.MK.registerEncoding,
    MAU.Inversion.MK.registerTupleEncoding,
    MAU.Inversion.MK.coeffAdderWorkEncoding,
    MAU.Inversion.MK.counterIncrementWorkEncoding,
    BinaryLabelEncoding.prod_width, MAU.Inversion.MK.wordEncoding_width,
    BinaryLabelEncoding.relabel_width, BinaryLabelEncoding.bool_width,
    MAU.Inversion.MK.comparisonWorkEncoding_width,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding_width,
    add_tsub_cancel_right,
    MAU.Multiplication.Accumulate.VBECircuit.encoding_width,
    physicalWidthFor]
  rw [htail, hcounterTail]
  omega

/-- Literal unscaled Kaliski gate schedule, lifted past the clean flag and the
preserved input copy. -/
def gates : List (EncodedBit.GateSpec rawEncoding) :=
  ((MAU.Inversion.MK.Resource.unscaledInversionGates
      tailWidth counterWidth params.modulus.val comparisonIndex workIndex
      params.modulusOdd).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodRight
      (MAU.Inversion.MK.wordEncoding arithmeticWidth))

/-- The public inversion adapter only lifts the unscaled inversion schedule
across the clean flag and retained input word, so it preserves the source-list
length. -/
lemma gates_length :
    gates.length =
      (MAU.Inversion.MK.Resource.unscaledInversionGates
        tailWidth counterWidth params.modulus.val comparisonIndex workIndex
        params.modulusOdd).length := by
  unfold gates
  simp only [List.length_map]

/-- Width-only primitive-leaf bound for a width-`f` scale-removing inversion
ledger. -/
def gateLengthBoundFor (f : Nat) : Nat :=
  MAU.Inversion.MK.Resource.unscaledInversionGateLengthBound
    (tailWidthFor f) (counterWidthFor f)

/-- Width-only literal-X bound for a width-`f` scale-removing inversion ledger. -/
def xBoundFor (f : Nat) : Nat :=
  gateLengthBoundFor f

/-- Width-only CNOT-coordinate bound for a width-`f` scale-removing inversion
ledger. -/
def cnotBoundFor (f : Nat) : Nat :=
  MAU.Inversion.MK.Resource.unscaledInversionCnotBound
    (tailWidthFor f) (counterWidthFor f)

/-- Width-only Toffoli-coordinate bound for a width-`f` scale-removing inversion
ledger. -/
def toffoliBoundFor (f : Nat) : Nat :=
  MAU.Inversion.MK.Resource.unscaledInversionToffoliBound
    (tailWidthFor f) (counterWidthFor f)

/-- Width-only unit-depth bound for a width-`f` scale-removing inversion ledger. -/
def unitDepthBoundFor (f : Nat) : Nat :=
  gateLengthBoundFor f

/-- Width-only primitive-leaf bound for the instantiated scale-removing
inversion ledger. -/
def gateLengthBound : Nat :=
  gateLengthBoundFor params.width

/-- Width-only literal-X bound for the instantiated scale-removing inversion
ledger. -/
def xBound : Nat :=
  xBoundFor params.width

/-- Width-only CNOT-coordinate bound for the instantiated scale-removing
inversion ledger. -/
def cnotBound : Nat :=
  cnotBoundFor params.width

/-- Width-only Toffoli-coordinate bound for the instantiated scale-removing
inversion ledger. -/
def toffoliBound : Nat :=
  toffoliBoundFor params.width

/-- Width-only unit-depth bound for the instantiated scale-removing inversion
ledger. -/
def unitDepthBound : Nat :=
  unitDepthBoundFor params.width

/-- The lifted public inversion schedule obeys its width-only source-ledger
bound. -/
lemma gates_length_le : gates.length ≤ gateLengthBound := by
  rw [gates_length]
  exact MAU.Inversion.MK.Resource.unscaledInversionGates_length_le
    tailWidth counterWidth params.modulus.val comparisonIndex workIndex
      params.modulusOdd

/-- The literal public inversion schedule obeys its closed X-coordinate bound. -/
lemma gates_xMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ xBound := by
  have hcoordinates := EncodedBit.GateSpec.length_eq_multiplicity_sums gates
  have hx :
      (gates.map EncodedBit.GateSpec.xMultiplicity).sum ≤ gates.length := by
    rw [hcoordinates]
    omega
  simpa only [xBound, xBoundFor, gateLengthBound] using
    hx.trans gates_length_le

/-- The public inversion adapter preserves the ordered primitive-event trace
of the unscaled inversion schedule. -/
lemma gates_map_event :
    gates.map (EncodedBit.GateSpec.event .empty) =
      (MAU.Inversion.MK.Resource.unscaledInversionGates
        tailWidth counterWidth params.modulus.val comparisonIndex workIndex
        params.modulusOdd).map (EncodedBit.GateSpec.event .empty) := by
  unfold gates
  exact
    (EncodedBit.GateSpec.map_event_prodRight
      (MAU.Inversion.MK.wordEncoding arithmeticWidth) _).trans
      (EncodedBit.GateSpec.map_event_prodLeft BinaryLabelEncoding.bool _)

/-- The public inversion adapter preserves the exact CNOT coordinate of the
unscaled inversion schedule. -/
lemma gates_cnotMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum =
      ((MAU.Inversion.MK.Resource.unscaledInversionGates
        tailWidth counterWidth params.modulus.val comparisonIndex workIndex
        params.modulusOdd).map
          EncodedBit.GateSpec.cnotMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty
    gates_map_event

/-- The lifted public inversion schedule obeys its source-ledger
CNOT-coordinate bound. -/
lemma gates_cnotMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum ≤ cnotBound := by
  rw [gates_cnotMultiplicity_sum]
  simpa only [cnotBound, cnotBoundFor] using
    MAU.Inversion.MK.Resource.unscaledInversionGates_cnotMultiplicity_sum_le
      tailWidth counterWidth params.modulus.val comparisonIndex workIndex
      params.modulusOdd

/-- The public inversion adapter preserves the exact Toffoli coordinate of
the unscaled inversion schedule. -/
lemma gates_toffoliMultiplicity_sum :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      ((MAU.Inversion.MK.Resource.unscaledInversionGates
        tailWidth counterWidth params.modulus.val comparisonIndex workIndex
        params.modulusOdd).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty
    gates_map_event

/-- The lifted public inversion schedule obeys its source-ledger
Toffoli-coordinate bound. -/
lemma gates_toffoliMultiplicity_sum_le :
    (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      toffoliBound := by
  rw [gates_toffoliMultiplicity_sum]
  simpa only [toffoliBound, toffoliBoundFor] using
    MAU.Inversion.MK.Resource.unscaledInversionGates_toffoliMultiplicity_sum_le
      tailWidth counterWidth params.modulus.val comparisonIndex workIndex
      params.modulusOdd

/-- Actual unscaled Kaliski inversion program compiled from its complete
lifted gate schedule. -/
def circuit : UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical (rawEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty gates

/-- The literal public inversion circuit obeys its closed unit-depth bound. -/
lemma circuit_unitDepth_le :
    circuit.evaluatedEventDepth (fun _ => 1) ≤ unitDepthBound := by
  change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    gates).evaluatedEventDepth
      (fun _ => 1) ≤ _
  rw [EncodedBit.GateSpec.programList_evaluatedEventDepth_unit]
  exact gates_length_le

/-- Total physical action of the lifted inversion program on the raw carrier. -/
def rawStep : RawRegisters → RawRegisters :=
  fun x =>
    (x.1,
      (MAU.Inversion.MK.Resource.unscaledInversionStep
        tailWidth counterWidth params.modulus.val comparisonIndex workIndex
        params.modulusOdd x.2.1,
      x.2.2))

/-- The lifted gate schedule has exactly the named raw-carrier action. -/
lemma gates_stepList (x : RawRegisters) :
    EncodedBit.GateSpec.stepList gates x = rawStep x := by
  simp only [gates, rawStep, rawEncoding,
    MAU.Inversion.MK.Resource.unscaledInversionStep,
    EncodedBit.GateSpec.stepList_prodRight,
    EncodedBit.GateSpec.stepList_prodLeft]

/-- The actual lifted circuit realizes its total raw-carrier action. -/
lemma rawRealizes : UnitaryCircuit.Realizes rawEncoding circuit environment rawStep := by
  unfold circuit
  exact EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty gates gates_stepList

/-- The static circuit adds the inverse of a unit input into its target and
restores all work registers. -/
lemma cleanEndpoint (x : MAU.Inversion.Data params.modulus.val) :
    let base := MAU.Inversion.MK.Resource.unscaledInversionStep
      tailWidth counterWidth params.modulus.val comparisonIndex workIndex
      params.modulusOdd
    base (cleanRegisters x).2.1 =
      (cleanRegisters x.addInverseIntoTarget).2.1 := by
  let input := inputWord x.input
  have hinput : (input.val : ZMod params.modulus.val) =
      (x.input : ZMod params.modulus.val) := by
    simp [input, inputWord]
  let _ : Fact (1 < params.modulus.val) :=
    ⟨params.one_lt_modulus⟩
  have hinputPos : 0 < input.val := by
    dsimp only [input, inputWord]
    exact (ZMod.val_pos).mpr (Units.ne_zero x.input)
  have hinputUnit : IsUnit (input.val : ZMod params.modulus.val) := by
    rw [hinput]
    exact x.input.isUnit
  have hinputCoprime : Nat.Coprime input.val params.modulus.val :=
    (ZMod.isUnit_iff_coprime input.val params.modulus.val).mp hinputUnit
  have hfinish :
      (NumberTheory.BinaryGCD.Trace.ofInput arithmeticWidth params.modulus.val
        input.val).finish.u = 1 := by
    change (NumberTheory.BinaryGCD.RoundState.fixedRoundState arithmeticWidth
      params.modulus.val input.val).u = 1
    exact
      NumberTheory.BinaryGCD.RoundState.fixedRoundState_u_eq_one_of_coprime_of_lt_two_pow
        arithmeticWidth params.modulus.val input.val params.modulusOdd.pos
        modulusWord.isLt input.isLt hinputCoprime.symm
  have hendpoint :=
    MAU.Inversion.MK.Resource.unscaledInversionProgram_cleanUnitEndpoint
      tailWidth counterWidth modulusWord input comparisonIndex workIndex
      params.modulusOdd hinputPos counter_capacity comparisonIndex_final
      (fun roundIndex state invariant =>
        MAU.Inversion.MK.Circuit.cleanPrefixInvariant_arithmeticCertificate
          tailWidth counterWidth modulusWord input roundIndex.val state invariant)
      x.input hinput hfinish x.target
  dsimp only [input] at hendpoint
  simpa only [cleanRegisters, MAU.Inversion.Data.addInverseIntoTarget,
    MAU.Inversion.inverseResidue, arithmeticWidth, arithmeticWidthFor,
    tailWidth, tailWidthFor] using
    hendpoint

/-- The total raw action specializes to the clean public inversion endpoint. -/
lemma rawStep_cleanEndpoint (x : MAU.Inversion.Data params.modulus.val) :
    rawStep (cleanRegisters x) =
      cleanRegisters x.addInverseIntoTarget := by
  let baseStep :=
    MAU.Inversion.MK.Resource.unscaledInversionStep
      tailWidth counterWidth params.modulus.val comparisonIndex workIndex
      params.modulusOdd
  have hclean : baseStep (cleanRegisters x).2.1 =
      (cleanRegisters x.addInverseIntoTarget).2.1 := by
    simpa [baseStep] using cleanEndpoint x
  dsimp only [baseStep] at hclean
  simp only [rawStep]
  rw [hclean]
  simp only [cleanRegisters, MAU.Inversion.Data.addInverseIntoTarget]

/-- The actual lifted circuit realizes the public inversion update. -/
lemma realizes : UnitaryCircuit.Realizes encoding circuit environment
    (MAU.Inversion.Data.addInverseIntoTarget) := by
  constructor
  intro x
  have happly := (rawRealizes (environment := environment)).apply_encoded_ket (cleanRegisters x)
  rw [rawStep_cleanEndpoint] at happly
  exact happly

/-- Structured witness consumed by modular-division and ECADD assembly. -/
def witness : MAU.Inversion.StructuredCircuitWitness params.modulus.val where
  encoding := encoding
  circuit := circuit
  realizes := fun environment => realizes (environment := environment)

end

end ModularInversion
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic

end
