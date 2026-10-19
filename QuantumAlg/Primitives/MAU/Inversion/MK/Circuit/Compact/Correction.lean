/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Invariant
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit

/-!
# Compact Montgomery--Kaliski correction circuit

This leaf builds the correction arithmetic directly on the compact inversion
carrier.  The VBE carry bank is the only linear-width workspace: source
routing, modular doubling, sign correction, and output copy borrow the existing
MK data registers and return them before the fixed-round fold is reversed.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit
namespace CompactCorrection

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open MK
open MK.Compact
open Nat.FixedWidth

/-! ## Compact VBE arithmetic view -/

/-- Full little-endian `s` coefficient word lifted into the compact carrier. -/
def sCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word (MK.Compact.encoding n counterWidth) (n + 1) where
  bit := fun bit => liftCoreBit n counterWidth
    (RegisterBits.sCoeffValueBit n counterWidth bit)

/-- Full little-endian `r` coefficient word lifted into the compact carrier. -/
def rCoeffValueWord (n counterWidth : Nat) :
    EncodedBit.Word (MK.Compact.encoding n counterWidth) (n + 1) where
  bit := fun bit => liftCoreBit n counterWidth
    (RegisterBits.rCoeffValueBit n counterWidth bit)

@[simp] lemma sCoeffValueWord_get (n counterWidth : Nat)
    (bit : Fin (n + 1)) (x : MK.Compact.Registers n counterWidth) :
    ((sCoeffValueWord n counterWidth).bit bit).get x =
      x.core.sCoeff.val.testBit bit.val := by
  change (RegisterBits.sCoeffValueBit n counterWidth bit).get x.core = _
  exact RegisterBits.sCoeffValueBit_get n counterWidth bit x.core

@[simp] lemma rCoeffValueWord_get (n counterWidth : Nat)
    (bit : Fin (n + 1)) (x : MK.Compact.Registers n counterWidth) :
    ((rCoeffValueWord n counterWidth).bit bit).get x =
      x.core.rCoeff.val.testBit bit.val := by
  change (RegisterBits.rCoeffValueBit n counterWidth bit).get x.core = _
  exact RegisterBits.rCoeffValueBit_get n counterWidth bit x.core

/-- The VBE active source borrows `v` and its adjacent clean active flag. -/
def activeSourceWord (fieldTail counterWidth : Nat) :
    EncodedBit.Word
      (MK.Compact.encoding fieldTail.succ counterWidth) (fieldTail.succ + 1) where
  bit := fun bit =>
    Fin.lastCases (activeBit fieldTail.succ counterWidth)
      (fun low => (vValueWord fieldTail.succ counterWidth).bit low) bit

/-- The VBE arithmetic target borrows `u` and its adjacent clean comparison
flag. -/
def arithmeticTargetWord (fieldTail counterWidth : Nat) :
    EncodedBit.Word
      (MK.Compact.encoding fieldTail.succ counterWidth) (fieldTail.succ + 1) where
  bit := fun bit =>
    Fin.lastCases (compareBit fieldTail.succ counterWidth)
      (fun low => (uValueWord fieldTail.succ counterWidth).bit low) bit

/-- The low `n` bits of the active source, used by the VBE source swap. -/
def activeSourceLowWord (fieldTail counterWidth : Nat) :
    EncodedBit.Word
      (MK.Compact.encoding fieldTail.succ counterWidth) fieldTail.succ :=
  vValueWord fieldTail.succ counterWidth

/-- The low `n` bits of `s`, which hold the modulus at the fixed-round
endpoint. -/
def parkedModulusWord (fieldTail counterWidth : Nat) :
    EncodedBit.Word
      (MK.Compact.encoding fieldTail.succ counterWidth) fieldTail.succ where
  bit := fun bit =>
    (sCoeffValueWord fieldTail.succ counterWidth).bit (Fin.castSucc bit)

@[simp] lemma activeSourceWord_bit_last (fieldTail counterWidth : Nat) :
    (activeSourceWord fieldTail counterWidth).bit (Fin.last fieldTail.succ) =
      activeBit fieldTail.succ counterWidth := by
  simp [activeSourceWord]

@[simp] lemma activeSourceWord_bit_castSucc
    (fieldTail counterWidth : Nat) (bit : Fin fieldTail.succ) :
    (activeSourceWord fieldTail counterWidth).bit (Fin.castSucc bit) =
      (vValueWord fieldTail.succ counterWidth).bit bit := by
  simp [activeSourceWord]

@[simp] lemma arithmeticTargetWord_bit_last
    (fieldTail counterWidth : Nat) :
    (arithmeticTargetWord fieldTail counterWidth).bit
        (Fin.last fieldTail.succ) = compareBit fieldTail.succ counterWidth := by
  simp [arithmeticTargetWord]

@[simp] lemma arithmeticTargetWord_bit_castSucc
    (fieldTail counterWidth : Nat) (bit : Fin fieldTail.succ) :
    (arithmeticTargetWord fieldTail counterWidth).bit (Fin.castSucc bit) =
      (uValueWord fieldTail.succ counterWidth).bit bit := by
  simp [arithmeticTargetWord]

private lemma activeSourceWord_pairwise_ne
    (fieldTail counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((activeSourceWord fieldTail counterWidth).bit left).wire ≠
        ((activeSourceWord fieldTail counterWidth).bit right).wire := by
  intro left right hne
  revert hne
  revert right
  refine Fin.lastCases ?_ ?_ left
  · intro right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · exact fun h => (h rfl).elim
    · intro low _
      simpa [activeSourceWord, vValueWord, activeBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.active_v_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low))
  · intro low right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · intro _
      simpa [activeSourceWord, vValueWord, activeBit,
        RegisterBits.vValueBit] using
        Ne.symm (liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.active_v_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low)))
    · intro other hne
      have hlow : low ≠ other := by
        intro heq
        apply hne
        subst other
        rfl
      simpa [activeSourceWord, vValueWord, RegisterBits.vValueBit] using
        liftCoreBit_wire_ne fieldTail.succ counterWidth
          (v_v_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire other)
            (littleEndianWire_ne hlow))

private lemma arithmeticTargetWord_pairwise_ne
    (fieldTail counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((arithmeticTargetWord fieldTail counterWidth).bit left).wire ≠
        ((arithmeticTargetWord fieldTail counterWidth).bit right).wire := by
  intro left right hne
  revert hne
  revert right
  refine Fin.lastCases ?_ ?_ left
  · intro right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · exact fun h => (h rfl).elim
    · intro low _
      simpa [arithmeticTargetWord, uValueWord, compareBit,
        RegisterBits.uValueBit] using
        Ne.symm (liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.u_compare_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low)))
  · intro low right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · intro _
      simpa [arithmeticTargetWord, uValueWord, compareBit,
        RegisterBits.uValueBit] using
        liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.u_compare_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low))
    · intro other hne
      have hlow : low ≠ other := by
        intro heq
        apply hne
        subst other
        rfl
      simpa [arithmeticTargetWord, uValueWord, RegisterBits.uValueBit] using
        liftCoreBit_wire_ne fieldTail.succ counterWidth
          (u_u_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire other)
            (littleEndianWire_ne hlow))

private lemma activeSource_target_ne (fieldTail counterWidth : Nat) :
    forall source target,
      ((activeSourceWord fieldTail counterWidth).bit source).wire ≠
        ((arithmeticTargetWord fieldTail counterWidth).bit target).wire := by
  intro source target
  revert target
  refine Fin.lastCases ?_ ?_ source
  · intro target
    refine Fin.lastCases ?_ ?_ target
    · simpa [activeSourceWord, arithmeticTargetWord, activeBit, compareBit] using
        liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.active_compare_wire_ne fieldTail.succ counterWidth)
    · intro low
      simpa [activeSourceWord, arithmeticTargetWord, activeBit, uValueWord,
        RegisterBits.uValueBit] using
        liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.active_u_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low))
  · intro source target
    refine Fin.lastCases ?_ ?_ target
    · simpa [activeSourceWord, arithmeticTargetWord, vValueWord, compareBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.v_compare_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire source))
    · intro target
      simpa [activeSourceWord, arithmeticTargetWord, vValueWord, uValueWord,
        RegisterBits.vValueBit, RegisterBits.uValueBit] using
        Ne.symm (liftCoreBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.u_v_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire target)
            (WireAddress.littleEndianWire source)))

private lemma activeSource_carry_ne (fieldTail counterWidth : Nat) :
    forall bit,
      ((activeSourceWord fieldTail counterWidth).bit bit).wire ≠
        (coefficientCarryInBit fieldTail.succ counterWidth).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [activeSourceWord, activeBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.activeBit fieldTail.succ counterWidth)
  · intro low
    simpa [activeSourceWord, vValueWord] using
      liftCoreBit_coefficientCarryInBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.vValueBit fieldTail.succ counterWidth low)

private lemma target_carry_ne (fieldTail counterWidth : Nat) :
    forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).wire ≠
        (coefficientCarryInBit fieldTail.succ counterWidth).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [arithmeticTargetWord, compareBit] using
      liftCoreBit_coefficientCarryInBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.compareBit fieldTail.succ counterWidth)
  · intro low
    simpa [arithmeticTargetWord, uValueWord] using
      liftCoreBit_coefficientCarryInBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.uValueBit fieldTail.succ counterWidth low)

private lemma activeSource_work_ne (fieldTail counterWidth : Nat) :
    forall source work,
      ((activeSourceWord fieldTail counterWidth).bit source).wire ≠
        ((coefficientCarryWorkWord fieldTail.succ counterWidth).bit work).wire := by
  intro source work
  refine Fin.lastCases ?_ ?_ source
  · simpa [activeSourceWord, activeBit, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.activeBit fieldTail.succ counterWidth) work
  · intro low
    simpa [activeSourceWord, vValueWord, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.vValueBit fieldTail.succ counterWidth low) work

private lemma target_work_ne (fieldTail counterWidth : Nat) :
    forall target work,
      ((arithmeticTargetWord fieldTail counterWidth).bit target).wire ≠
        ((coefficientCarryWorkWord fieldTail.succ counterWidth).bit work).wire := by
  intro target work
  refine Fin.lastCases ?_ ?_ target
  · simpa [arithmeticTargetWord, compareBit, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.compareBit fieldTail.succ counterWidth) work
  · intro low
    simpa [arithmeticTargetWord, uValueWord, coefficientCarryWorkWord] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.uValueBit fieldTail.succ counterWidth low) work

/-- The one compact VBE layout used by every modular-reduction pass. -/
def arithmeticLayout (fieldTail counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := MK.Compact.encoding fieldTail.succ counterWidth)
      (fieldTail.succ + 1) where
  left := activeSourceWord fieldTail counterWidth
  right := arithmeticTargetWord fieldTail counterWidth
  carryIn := coefficientCarryInBit fieldTail.succ counterWidth
  workCarry := coefficientCarryWorkWord fieldTail.succ counterWidth
  leftLeft_ne := activeSourceWord_pairwise_ne fieldTail counterWidth
  rightRight_ne := arithmeticTargetWord_pairwise_ne fieldTail counterWidth
  leftRight_ne := activeSource_target_ne fieldTail counterWidth
  leftCarryIn_ne := activeSource_carry_ne fieldTail counterWidth
  rightCarryIn_ne := target_carry_ne fieldTail counterWidth
  leftWork_ne := activeSource_work_ne fieldTail counterWidth
  rightWork_ne := target_work_ne fieldTail counterWidth
  carryInWork_ne := coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
    fieldTail.succ counterWidth
  workWork_ne := by
    intro left right hne
    simpa [coefficientCarryWorkWord] using
      coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth hne

private lemma carryWorkLayout_get_workCarry_natAddCarry
    {Carrier : Type} {encoding : BinaryLabelEncoding Carrier} {width : Nat}
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding) width)
    (left right : Nat) (j : Fin (width - 1)) (x : Carrier)
    (hleft : forall bit,
      (layout.left.bit bit).get x = left.testBit bit.val)
    (hright : forall bit,
      (layout.right.bit bit).get x = right.testBit bit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : forall bit, (layout.workCarry.bit bit).get x = false) :
    (layout.workCarry.bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left right (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x
  change (layout.workCarry.bit j).get stage = _
  have hmain : forall m, forall k : Fin (width - 1), k.val = m ->
      (layout.workCarry.bit k).get stage =
        Nat.BinaryArithmetic.natAddCarry left right (k.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro k hkm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            layout k x hwork
        change (layout.workCarry.bit k).get stage = _
        change (layout.workCarry.bit k).get
            (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) = _
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : k.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              layout x
          rw [hdata, hcarry]
          rw [hleft, hright]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let previous :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex k hzero
          have hpreviousLt : previous.val < m := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hprevious := ih previous.val hpreviousLt previous rfl
          have hpreviousSucc : previous.val + 1 = k.val := by
            dsimp [previous,
              PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          change
            Bool.carry
                ((layout.left.bit
                  (PlainAdder.Schedule.CarryWorkLayout.lowIndex k)).get x)
                ((layout.right.bit
                  (PlainAdder.Schedule.CarryWorkLayout.lowIndex k)).get x)
                ((layout.workCarry.bit previous).get
                  (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
                    layout x)) = _
          rw [hprevious, hpreviousSucc, hleft, hright]
          simp [PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

private lemma carryWorkLayout_get_carryBeforeSum_natAddCarry
    {Carrier : Type} {encoding : BinaryLabelEncoding Carrier} {width : Nat}
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding) width)
    (left right : Nat) (bit : Fin width) (x : Carrier)
    (hleft : forall bit,
      (layout.left.bit bit).get x = left.testBit bit.val)
    (hright : forall bit,
      (layout.right.bit bit).get x = right.testBit bit.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : forall work, (layout.workCarry.bit work).get x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum layout bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep layout x) =
      Nat.BinaryArithmetic.natAddCarry left right bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        layout x
    rw [hdata, hcarry]
    simp [Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : bit.val - 1 < width - 1 := by
      have hbit := bit.isLt
      omega
    let j : Fin (width - 1) := ⟨bit.val - 1, hjLt⟩
    have hj := carryWorkLayout_get_workCarry_natAddCarry
      layout left right j x hleft hright hcarry hwork
    have hjSucc : j.val + 1 = bit.val := by
      dsimp [j]
      omega
    simpa only [j, hjSucc] using hj

private lemma cleanCarrySumStep_get_right_add_of_clean
    {Carrier : Type} {encoding : BinaryLabelEncoding Carrier} {width : Nat}
    (layout : PlainAdder.Schedule.CarryWorkLayout
      (encoding := encoding) width)
    (left right : Word width) (bit : Fin width) (x : Carrier)
    (hleft : forall source,
      (layout.left.bit source).get x = left.val.testBit source.val)
    (hright : forall target,
      (layout.right.bit target).get x = right.val.testBit target.val)
    (hcarry : layout.carryIn.get x = false)
    (hwork : forall work, (layout.workCarry.bit work).get x = false) :
    (layout.right.bit bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
      (right + left).val.testBit bit.val := by
  have htarget :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      layout bit x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at htarget
  rw [carryWorkLayout_get_carryBeforeSum_natAddCarry
    layout left.val right.val bit x hleft hright hcarry hwork] at htarget
  calc
    (layout.right.bit bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep layout x) =
      ((right.val.testBit bit.val ^^ left.val.testBit bit.val) ^^
        Nat.BinaryArithmetic.natAddCarry left.val right.val bit.val) := by
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        hleft bit, hright bit] using htarget
    _ = (right + left).val.testBit bit.val :=
      (word_add_testBit_eq_xor3 width left right bit).symm

/-- Embed an `n`-bit fixed-width word into the low bits of an `(n+1)`-bit
word. -/
def widenFixedWord (n : Nat) (word : Word n) : Word (n + 1) :=
  ⟨word.val, by
    have hword := word.isLt
    rw [pow_succ]
    omega⟩

@[simp] lemma widenFixedWord_val (n : Nat) (word : Word n) :
    (widenFixedWord n word).val = word.val :=
  rfl

lemma widenFixedWord_zero (n : Nat) :
    widenFixedWord n (0 : Word n) = (0 : Word (n + 1)) := by
  apply Fin.ext
  rfl

/-- Retain the low `n` bits of an `(n+1)`-bit fixed-width word. -/
def truncateFixedWord (n : Nat) (word : Word (n + 1)) : Word n :=
  ⟨word.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

@[simp] lemma truncateFixedWord_val (n : Nat)
    (word : Word (n + 1)) :
    (truncateFixedWord n word).val = word.val % 2 ^ n :=
  rfl

@[simp] lemma truncateFixedWord_widenFixedWord (n : Nat)
    (word : Word n) :
    truncateFixedWord n (widenFixedWord n word) = word := by
  apply Fin.ext
  simp [truncateFixedWord, Nat.mod_eq_of_lt word.isLt]

/-- Truncation followed by widening is exact when the widened word already
fits in the low `n` bits. -/
lemma widenFixedWord_truncateFixedWord_of_lt (n : Nat)
    (word : Word (n + 1)) (hword : word.val < 2 ^ n) :
    widenFixedWord n (truncateFixedWord n word) = word := by
  apply Fin.ext
  simp [truncateFixedWord, Nat.mod_eq_of_lt hword]

/-- Canonical compact state exposing the borrowed VBE arithmetic registers.
Every field outside this view is inherited from `base`. -/
def arithmeticState (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    MK.Compact.Registers fieldTail.succ counterWidth where
  core :=
    { base.core with
      u := truncateFixedWord fieldTail.succ target
      v := truncateFixedWord fieldTail.succ active
      compare := target.val.testBit fieldTail.succ
      sCoeff := widenFixedWord fieldTail.succ parked
      scratchA := flag
      active := active.val.testBit fieldTail.succ }
  shared :=
    { base.shared with
      coefficientAdder := cleanCoeffAdderWork fieldTail.succ }
  target := base.target

@[simp] private lemma arithmeticState_activeSource_get
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (bit : Fin (fieldTail.succ + 1)) :
    ((activeSourceWord fieldTail counterWidth).bit bit).get
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      active.val.testBit bit.val := by
  refine Fin.lastCases ?_ ?_ bit
  · simp [activeSourceWord, arithmeticState]
  · intro low
    rw [activeSourceWord_bit_castSucc, vValueWord_get]
    simp only [arithmeticState, truncateFixedWord_val]
    rw [Nat.testBit_mod_two_pow]
    simp [low.isLt]

@[simp] private lemma arithmeticState_target_get
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (bit : Fin (fieldTail.succ + 1)) :
    ((arithmeticTargetWord fieldTail counterWidth).bit bit).get
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      target.val.testBit bit.val := by
  refine Fin.lastCases ?_ ?_ bit
  · simp [arithmeticTargetWord, arithmeticState]
  · intro low
    rw [arithmeticTargetWord_bit_castSucc, uValueWord_get]
    simp only [arithmeticState, truncateFixedWord_val]
    rw [Nat.testBit_mod_two_pow]
    simp [low.isLt]

@[simp] private lemma arithmeticState_parked_get
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (bit : Fin fieldTail.succ) :
    ((parkedModulusWord fieldTail counterWidth).bit bit).get
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      parked.val.testBit bit.val := by
  simp [parkedModulusWord, arithmeticState]

private lemma arithmeticState_carryIn_get
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    (coefficientCarryInBit fieldTail.succ counterWidth).get
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      false := by
  simp [arithmeticState, cleanCoeffAdderWork]

private lemma arithmeticState_workCarry_get
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (bit : Fin fieldTail.succ) :
    (coefficientCarryWorkBit fieldTail.succ counterWidth bit).get
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      false := by
  simp [arithmeticState, cleanCoeffAdderWork,
    PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]

/-! ## Literal VBE reduction ledger -/

private lemma activeSourceLow_parked_ne
    (fieldTail counterWidth : Nat) (source target : Fin fieldTail.succ) :
    ((activeSourceLowWord fieldTail counterWidth).bit source).wire ≠
      ((parkedModulusWord fieldTail counterWidth).bit target).wire := by
  simpa [activeSourceLowWord, parkedModulusWord, vValueWord, sCoeffValueWord,
    RegisterBits.vValueBit, RegisterBits.sCoeffValueBit] using
    liftCoreBit_wire_ne fieldTail.succ counterWidth
      (RegisterBits.v_sCoeff_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire source)
        (WireAddress.littleEndianWire (Fin.castSucc target)))

private lemma activeSourceLowWord_pairwise_ne
    (fieldTail counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((activeSourceLowWord fieldTail counterWidth).bit left).wire ≠
        ((activeSourceLowWord fieldTail counterWidth).bit right).wire := by
  intro left right hne
  simpa [activeSourceLowWord, vValueWord, RegisterBits.vValueBit] using
    liftCoreBit_wire_ne fieldTail.succ counterWidth
      (v_v_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire left)
        (WireAddress.littleEndianWire right)
        (littleEndianWire_ne hne))

private lemma parkedModulusWord_pairwise_ne
    (fieldTail counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((parkedModulusWord fieldTail counterWidth).bit left).wire ≠
        ((parkedModulusWord fieldTail counterWidth).bit right).wire := by
  intro left right hne
  simpa [parkedModulusWord, sCoeffValueWord,
    RegisterBits.sCoeffValueBit] using
    liftCoreBit_wire_ne fieldTail.succ counterWidth
      (sCoeff_sCoeff_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire (Fin.castSucc left))
        (WireAddress.littleEndianWire (Fin.castSucc right))
        (littleEndianWire_ne (fun h => hne (Fin.castSucc_injective _ h))))

private lemma activeSourceLow_sCoeffHigh_ne
    (fieldTail counterWidth : Nat) :
    forall bit,
      ((activeSourceLowWord fieldTail counterWidth).bit bit).wire ≠
        ((sCoeffValueWord fieldTail.succ counterWidth).bit
          (Fin.last fieldTail.succ)).wire := by
  intro bit
  simpa [activeSourceLowWord, vValueWord, sCoeffValueWord,
    RegisterBits.vValueBit, RegisterBits.sCoeffValueBit] using
    liftCoreBit_wire_ne fieldTail.succ counterWidth
      (RegisterBits.v_sCoeff_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit)
        (WireAddress.littleEndianWire (Fin.last fieldTail.succ)))

private lemma parkedModulus_sCoeffHigh_ne
    (fieldTail counterWidth : Nat) :
    forall bit,
      ((parkedModulusWord fieldTail counterWidth).bit bit).wire ≠
        ((sCoeffValueWord fieldTail.succ counterWidth).bit
          (Fin.last fieldTail.succ)).wire := by
  intro bit
  simpa [parkedModulusWord, sCoeffValueWord,
    RegisterBits.sCoeffValueBit] using
    liftCoreBit_wire_ne fieldTail.succ counterWidth
      (sCoeff_sCoeff_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire (Fin.castSucc bit))
        (WireAddress.littleEndianWire (Fin.last fieldTail.succ))
        (littleEndianWire_ne (ne_of_lt (Fin.castSucc_lt_last bit))))

/-- Three-CNOT-per-bit exchange of the active low source and parked modulus. -/
def sourceSwapGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.Word.swapGates
    (activeSourceLowWord fieldTail counterWidth)
    (parkedModulusWord fieldTail counterWidth)
    (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)

/-- Fixed `(n+1)`-bit label of the public modulus. -/
def modulusWordLabel (fieldTail p : Nat) : Fin (2 ^ (fieldTail.succ + 1)) :=
  MAU.Addition.VBECircuit.modulusWordLabel fieldTail.succ p

private lemma modulusWordLabel_val (fieldTail p : Nat)
    (hp : p < 2 ^ fieldTail.succ) :
    (modulusWordLabel fieldTail p).val = p := by
  simp [modulusWordLabel, MAU.Addition.VBECircuit.modulusWordLabel,
    PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv,
    MAU.Addition.VBECircuit.widenWord_val, ZMod.val_natCast_of_lt hp]

private lemma fin_sub_val_eq_zmod_sub_val {modulus : Nat} [NeZero modulus]
    (left right : Fin modulus) :
    (left - right).val =
      (((left.val : ZMod modulus) - (right.val : ZMod modulus)).val) := by
  rw [MAU.Addition.VBEArithmetic.zmodVal_natCast_sub_natCast
    left.isLt right.isLt]
  by_cases hle : right ≤ left
  · have hleVal : right.val ≤ left.val := hle
    rw [if_pos hleVal]
    exact Fin.sub_val_of_le hle
  · have hnleVal : ¬right.val ≤ left.val := by simpa using hle
    rw [if_neg hnleVal]
    have hfin := Fin.intCast_val_sub_eq_sub_add_ite left right
    simp [hle] at hfin
    omega

def reducedWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (raw : Word (fieldTail.succ + 1)) (hraw : raw.val < 2 * p) :
    Word (fieldTail.succ + 1) :=
  ⟨MAU.Addition.VBEArithmetic.reduceOnce p raw.val, by
    have hltP := MAU.Addition.VBEArithmetic.reduceOnce_lt hpPos hraw
    have hpow : 2 ^ fieldTail.succ < 2 ^ (fieldTail.succ + 1) :=
      Nat.pow_lt_pow_right (by decide) fieldTail.succ.lt_succ_self
    exact hltP.trans (hp.trans hpow)⟩

@[simp] lemma reducedWord_val (fieldTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (raw : Word (fieldTail.succ + 1)) (hraw : raw.val < 2 * p) :
    (reducedWord fieldTail p hpPos hp raw hraw).val =
      MAU.Addition.VBEArithmetic.reduceOnce p raw.val :=
  rfl

lemma reducedWord_val_eq_mod (fieldTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (raw : Word (fieldTail.succ + 1)) (hraw : raw.val < 2 * p) :
    (reducedWord fieldTail p hpPos hp raw hraw).val = raw.val % p := by
  rw [reducedWord_val]
  exact MAU.Addition.VBEArithmetic.reduceOnce_eq_mod hpPos hraw

/-- Proof-independent reduced representative of an arbitrary widened word. -/
def canonicalResidueWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (raw : Word (fieldTail.succ + 1)) : Word (fieldTail.succ + 1) :=
  ⟨raw.val % p, by
    have hmod := Nat.mod_lt raw.val hpPos
    have hpow : 2 ^ fieldTail.succ < 2 ^ (fieldTail.succ + 1) :=
      Nat.pow_lt_pow_right (by decide) fieldTail.succ.lt_succ_self
    exact hmod.trans (hp.trans hpow)⟩

@[simp] lemma canonicalResidueWord_val (fieldTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (raw : Word (fieldTail.succ + 1)) :
    (canonicalResidueWord fieldTail p hpPos hp raw).val = raw.val % p :=
  rfl

/-- Reducing a widened coefficient does not change its residue class. -/
lemma canonicalResidueWord_cast (fieldTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (raw : Word (fieldTail.succ + 1)) :
    ((canonicalResidueWord fieldTail p hpPos hp raw).val : ZMod p) =
      (raw.val : ZMod p) := by
  rw [canonicalResidueWord_val, ZMod.natCast_mod]

/-- The one-subtraction circuit representative is the canonical residue;
the bound proof used to justify the subtraction does not affect the word. -/
lemma reducedWord_eq_canonicalResidueWord (fieldTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (raw : Word (fieldTail.succ + 1)) (hraw : raw.val < 2 * p) :
    reducedWord fieldTail p hpPos hp raw hraw =
      canonicalResidueWord fieldTail p hpPos hp raw := by
  apply Fin.ext
  exact reducedWord_val_eq_mod fieldTail p hpPos hp raw hraw

private lemma reductionFlag_activeSource_ne
    (fieldTail counterWidth : Nat) :
    forall bit,
      (scratchABit fieldTail.succ counterWidth).wire ≠
        ((activeSourceWord fieldTail counterWidth).bit bit).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [activeSourceWord] using
      Ne.symm (activeBit_scratchABit_wire_ne fieldTail.succ counterWidth)
  · intro low
    simpa [activeSourceWord, vValueWord, scratchABit,
      RegisterBits.vValueBit] using
      Ne.symm (liftCoreBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.v_scratchA_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire low)))

/-- X/CNOT pair recording whether the widened target survived subtraction by
the modulus. -/
def copyReductionFlagGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  [ .x (scratchABit fieldTail.succ counterWidth),
    .cnot (compareBit fieldTail.succ counterWidth)
      (scratchABit fieldTail.succ counterWidth)
      (compareBit_scratchABit_wire_ne fieldTail.succ counterWidth) ]

/-- Conditionally xor the modulus into the borrowed active source. -/
def clearActiveModulusGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.Word.controlledXorConstantGates
    (scratchABit fieldTail.succ counterWidth)
    (activeSourceWord fieldTail counterWidth)
    (modulusWordLabel fieldTail p)
    (reductionFlag_activeSource_ne fieldTail counterWidth)

/-- Restore the conditionally cleared active modulus word. -/
def restoreActiveModulusGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  (clearActiveModulusGates fieldTail counterWidth p).reverse

/-- Final CNOT erasing the retained modular-reduction flag. -/
def cleanupReductionFlagGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  [ .cnot (compareBit fieldTail.succ counterWidth)
      (scratchABit fieldTail.succ counterWidth)
      (compareBit_scratchABit_wire_ne fieldTail.succ counterWidth) ]

/-- The sole cleanup-aware VBE adder ledger shared across reduction stages. -/
def arithmeticAdderGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (arithmeticLayout fieldTail counterWidth)

/-- Eleven-stage VBE modular reduction instantiated directly on the compact
carrier.  The active source is initially zero, so this reduces the widened
target without adding an independent residue. -/
def modularReduceGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  arithmeticAdderGates fieldTail counterWidth ++
    sourceSwapGates fieldTail counterWidth ++
    (arithmeticAdderGates fieldTail counterWidth).reverse ++
    copyReductionFlagGates fieldTail counterWidth ++
    clearActiveModulusGates fieldTail counterWidth p ++
    arithmeticAdderGates fieldTail counterWidth ++
    restoreActiveModulusGates fieldTail counterWidth p ++
    sourceSwapGates fieldTail counterWidth ++
    (arithmeticAdderGates fieldTail counterWidth).reverse ++
    cleanupReductionFlagGates fieldTail counterWidth ++
    arithmeticAdderGates fieldTail counterWidth

/-- One forward use of the shared compact VBE adder. -/
def arithmeticAdderStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (arithmeticAdderGates fieldTail counterWidth)

/-- One reverse use of the shared compact VBE adder. -/
def arithmeticAdderReverseStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (arithmeticAdderGates fieldTail counterWidth).reverse

private lemma arithmeticAdderStep_get_observed
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hright : forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).wire ≠
        observed.wire)
    (hwork : forall bit,
      (coefficientCarryWorkBit fieldTail.succ counterWidth bit).wire ≠
        observed.wire)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    observed.get (arithmeticAdderStep fieldTail counterWidth x) =
      observed.get x := by
  simpa [arithmeticAdderStep, arithmeticAdderGates, arithmeticLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (arithmeticLayout fieldTail counterWidth) observed hright
      (by
        intro bit
        simpa [arithmeticLayout, coefficientCarryWorkWord] using hwork bit)
      x

private lemma arithmeticTargetWord_liftCoreBit_ne
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (registerEncoding fieldTail.succ counterWidth))
    (hlow : forall bit,
      (RegisterBits.uValueBit fieldTail.succ counterWidth bit).wire ≠
        observed.wire)
    (hhigh :
      (RegisterBits.compareBit fieldTail.succ counterWidth).wire ≠
        observed.wire) :
    forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).wire ≠
        (liftCoreBit fieldTail.succ counterWidth observed).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [arithmeticTargetWord, compareBit] using
      liftCoreBit_wire_ne fieldTail.succ counterWidth hhigh
  · intro low
    simpa [arithmeticTargetWord, uValueWord] using
      liftCoreBit_wire_ne fieldTail.succ counterWidth (hlow low)

private lemma arithmeticAdderStep_get_coreBit
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (registerEncoding fieldTail.succ counterWidth))
    (hlow : forall bit,
      (RegisterBits.uValueBit fieldTail.succ counterWidth bit).wire ≠
        observed.wire)
    (hhigh :
      (RegisterBits.compareBit fieldTail.succ counterWidth).wire ≠
        observed.wire)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (liftCoreBit fieldTail.succ counterWidth observed).get
        (arithmeticAdderStep fieldTail counterWidth x) =
      (liftCoreBit fieldTail.succ counterWidth observed).get x := by
  exact arithmeticAdderStep_get_observed fieldTail counterWidth
    (liftCoreBit fieldTail.succ counterWidth observed)
    (arithmeticTargetWord_liftCoreBit_ne fieldTail counterWidth observed
      hlow hhigh)
    (fun bit => Ne.symm
      (liftCoreBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth
        observed bit))
    x

private lemma arithmeticAdderStep_activeSource_get
    (fieldTail counterWidth : Nat)
    (bit : Fin (fieldTail.succ + 1))
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    ((activeSourceWord fieldTail counterWidth).bit bit).get
        (arithmeticAdderStep fieldTail counterWidth x) =
      ((activeSourceWord fieldTail counterWidth).bit bit).get x := by
  simpa [arithmeticAdderStep, arithmeticAdderGates, arithmeticLayout] using
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (arithmeticLayout fieldTail counterWidth) bit x

private lemma arithmeticAdderStep_target_get_add
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (bit : Fin (fieldTail.succ + 1)) :
    ((arithmeticTargetWord fieldTail counterWidth).bit bit).get
        (arithmeticAdderStep fieldTail counterWidth
          (arithmeticState fieldTail counterWidth base active target parked flag)) =
      (target + active).val.testBit bit.val := by
  simpa [arithmeticAdderStep, arithmeticAdderGates, arithmeticLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using
    cleanCarrySumStep_get_right_add_of_clean
      (arithmeticLayout fieldTail counterWidth) active target bit
      (arithmeticState fieldTail counterWidth base active target parked flag)
      (arithmeticState_activeSource_get fieldTail counterWidth base active
        target parked flag)
      (arithmeticState_target_get fieldTail counterWidth base active target
        parked flag)
      (by
        simpa [arithmeticLayout] using
          arithmeticState_carryIn_get fieldTail counterWidth base active
            target parked flag)
      (by
        intro work
        simpa [arithmeticLayout, coefficientCarryWorkWord] using
          arithmeticState_workCarry_get fieldTail counterWidth base active
            target parked flag work)

private lemma arithmeticAdderStep_carryIn_get
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (coefficientCarryInBit fieldTail.succ counterWidth).get
        (arithmeticAdderStep fieldTail counterWidth x) =
      (coefficientCarryInBit fieldTail.succ counterWidth).get x := by
  simpa [arithmeticAdderStep, arithmeticAdderGates, arithmeticLayout] using
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (arithmeticLayout fieldTail counterWidth) x

private lemma arithmeticAdderStep_workCarry_clean
    (fieldTail counterWidth : Nat) (bit : Fin fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ counterWidth)
    (hclean : forall workBit,
      (coefficientCarryWorkBit fieldTail.succ counterWidth workBit).get x =
        false) :
    (coefficientCarryWorkBit fieldTail.succ counterWidth bit).get
        (arithmeticAdderStep fieldTail counterWidth x) = false := by
  simpa [arithmeticAdderStep, arithmeticAdderGates, arithmeticLayout,
    coefficientCarryWorkWord] using
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (arithmeticLayout fieldTail counterWidth) bit x
      (by
        intro work
        simpa [arithmeticLayout, coefficientCarryWorkWord] using hclean work)

private lemma arithmeticAdderStep_sCoeff
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).core.sCoeff =
      x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [← sCoeffValueWord_get fieldTail.succ counterWidth bit]
  rw [← sCoeffValueWord_get fieldTail.succ counterWidth bit]
  exact arithmeticAdderStep_get_coreBit fieldTail counterWidth
    (RegisterBits.sCoeffValueBit fieldTail.succ counterWidth bit)
    (fun low => by
      simpa [RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
        RegisterBits.u_sCoeff_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire low)
          (WireAddress.littleEndianWire bit))
    (by
      simpa [RegisterBits.sCoeffValueBit] using
        RegisterBits.compare_sCoeff_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire bit))
    x

private lemma arithmeticAdderStep_rCoeff
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).core.rCoeff =
      x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [← rCoeffValueWord_get fieldTail.succ counterWidth bit]
  rw [← rCoeffValueWord_get fieldTail.succ counterWidth bit]
  exact arithmeticAdderStep_get_coreBit fieldTail counterWidth
    (RegisterBits.rCoeffValueBit fieldTail.succ counterWidth bit)
    (fun low => by
      simpa [RegisterBits.uValueBit, RegisterBits.rCoeffValueBit] using
        RegisterBits.u_rCoeff_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire low)
          (WireAddress.littleEndianWire bit))
    (by
      simpa [RegisterBits.rCoeffValueBit] using
        RegisterBits.compare_rCoeff_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire bit))
    x

private lemma arithmeticAdderStep_scratchA
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).core.scratchA =
      x.core.scratchA := by
  rw [← scratchABit_get fieldTail.succ counterWidth]
  rw [← scratchABit_get fieldTail.succ counterWidth]
  exact arithmeticAdderStep_get_coreBit fieldTail counterWidth
    (RegisterBits.scratchABit fieldTail.succ counterWidth)
    (fun low => by
      simpa [RegisterBits.uValueBit] using
        RegisterBits.u_scratchA_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire low))
    (RegisterBits.compare_scratchA_wire_ne fieldTail.succ counterWidth)
    x

private lemma arithmeticAdderStep_scratchB
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).core.scratchB =
      x.core.scratchB := by
  rw [← scratchBBit_get fieldTail.succ counterWidth]
  rw [← scratchBBit_get fieldTail.succ counterWidth]
  exact arithmeticAdderStep_get_coreBit fieldTail counterWidth
    (RegisterBits.scratchBBit fieldTail.succ counterWidth)
    (fun low => by
      simpa [RegisterBits.uValueBit] using
        RegisterBits.u_scratchB_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire low))
    (RegisterBits.compare_scratchB_wire_ne fieldTail.succ counterWidth)
    x

private lemma arithmeticAdderStep_history
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).core.history =
      x.core.history := by
  apply word_eq_of_testBit_eq
  intro bit
  have hread := arithmeticAdderStep_get_coreBit fieldTail counterWidth
      (RegisterBits.historyBit fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun low => by
        simpa [RegisterBits.uValueBit] using
          RegisterBits.u_history_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire bit))
      (RegisterBits.compare_history_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      x
  change
    (RegisterBits.historyBit fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit)).get
        (arithmeticAdderStep fieldTail counterWidth x).core =
      (RegisterBits.historyBit fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit)).get x.core at hread
  simpa only [RegisterBits.historyBit_get,
    WireAddress.bitIndex_littleEndianWire] using hread

private lemma arithmeticAdderStep_counter
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).core.counter =
      x.core.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  have hread := arithmeticAdderStep_get_coreBit fieldTail counterWidth
      (RegisterBits.counterBit fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun low => by
        simpa [RegisterBits.uValueBit] using
          RegisterBits.u_counter_wire_ne fieldTail.succ counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire bit))
      (RegisterBits.compare_counter_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      x
  change
    (RegisterBits.counterBit fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit)).get
        (arithmeticAdderStep fieldTail counterWidth x).core =
      (RegisterBits.counterBit fieldTail.succ counterWidth
        (WireAddress.littleEndianWire bit)).get x.core at hread
  simpa only [RegisterBits.counterBit_get,
    WireAddress.bitIndex_littleEndianWire] using hread

private lemma arithmeticTargetWord_liftSharedBit_ne
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (sharedWorkEncoding fieldTail.succ counterWidth)) :
    forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).wire ≠
        (liftSharedBit fieldTail.succ counterWidth observed).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [arithmeticTargetWord, compareBit] using
      liftCoreBit_liftSharedBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.compareBit fieldTail.succ counterWidth) observed
  · intro low
    simpa [arithmeticTargetWord, uValueWord] using
      liftCoreBit_liftSharedBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.uValueBit fieldTail.succ counterWidth low) observed

private lemma arithmeticTargetWord_targetBit_ne
    (fieldTail counterWidth : Nat) (observed : Fin fieldTail.succ) :
    forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).wire ≠
        (targetBit fieldTail.succ counterWidth observed).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [arithmeticTargetWord, compareBit] using
      liftCoreBit_targetBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.compareBit fieldTail.succ counterWidth) observed
  · intro low
    simpa [arithmeticTargetWord, uValueWord] using
      liftCoreBit_targetBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.uValueBit fieldTail.succ counterWidth low) observed

private lemma arithmeticAdderStep_correctionCounter
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).shared.correctionCounter =
      x.shared.correctionCounter := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [← correctionCounterValueBit_get fieldTail.succ counterWidth bit]
  rw [← correctionCounterValueBit_get fieldTail.succ counterWidth bit]
  exact arithmeticAdderStep_get_observed fieldTail counterWidth
    (correctionCounterValueBit fieldTail.succ counterWidth bit)
    (by
      simpa [correctionCounterValueBit, correctionCounterBit] using
        arithmeticTargetWord_liftSharedBit_ne fieldTail counterWidth
          (sharedCorrectionCounterBit fieldTail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
    (fun work => by
      simpa [correctionCounterValueBit] using Ne.symm
        (correctionCounterBit_coefficientCarryWorkBit_wire_ne
          fieldTail.succ counterWidth (WireAddress.littleEndianWire bit) work))
    x

private lemma arithmeticAdderStep_path
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).shared.path =
      x.shared.path := by
  rw [← pathBit_get fieldTail.succ counterWidth]
  rw [← pathBit_get fieldTail.succ counterWidth]
  exact arithmeticAdderStep_get_observed fieldTail counterWidth
    (pathBit fieldTail.succ counterWidth)
    (by
      simpa [pathBit] using
        arithmeticTargetWord_liftSharedBit_ne fieldTail counterWidth
          (sharedPathBit fieldTail.succ counterWidth))
    (fun work => Ne.symm
      (pathBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth work))
    x

private lemma arithmeticAdderStep_control
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).shared.control =
      x.shared.control := by
  rw [← controlBit_get fieldTail.succ counterWidth]
  rw [← controlBit_get fieldTail.succ counterWidth]
  exact arithmeticAdderStep_get_observed fieldTail counterWidth
    (controlBit fieldTail.succ counterWidth)
    (by
      simpa [controlBit] using
        arithmeticTargetWord_liftSharedBit_ne fieldTail counterWidth
          (sharedControlBit fieldTail.succ counterWidth))
    (fun work => Ne.symm
      (controlBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth
        work))
    x

private lemma arithmeticAdderStep_publicTarget
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (arithmeticAdderStep fieldTail counterWidth x).target = x.target := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [← targetValueBit_get fieldTail.succ counterWidth bit]
  rw [← targetValueBit_get fieldTail.succ counterWidth bit]
  exact arithmeticAdderStep_get_observed fieldTail counterWidth
    (targetValueBit fieldTail.succ counterWidth bit)
    (by
      simpa [targetValueBit] using
        arithmeticTargetWord_targetBit_ne fieldTail counterWidth
          (WireAddress.littleEndianWire bit))
    (fun work => by
      simpa [targetValueBit, coefficientCarryWorkBit] using
        liftSharedBit_targetBit_wire_ne fieldTail.succ counterWidth
          (sharedCoefficientCarryWorkBit fieldTail.succ counterWidth work)
          (WireAddress.littleEndianWire bit))
    x

/-- One forward use of the shared VBE bank adds the active widened source into
the borrowed target and restores the bank to its canonical clean value. -/
lemma arithmeticAdderStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    arithmeticAdderStep fieldTail counterWidth
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      arithmeticState fieldTail counterWidth base active (target + active)
        parked flag := by
  let input := arithmeticState fieldTail counterWidth base active target parked flag
  let output := arithmeticAdderStep fieldTail counterWidth input
  let expected := arithmeticState fieldTail counterWidth base active
    (target + active) parked flag
  have hu : output.core.u = expected.core.u := by
    apply word_eq_of_testBit_eq
    intro bit
    have htarget := arithmeticAdderStep_target_get_add fieldTail counterWidth
      base active target parked flag (Fin.castSucc bit)
    have hexpected := arithmeticState_target_get fieldTail counterWidth base
      active (target + active) parked flag (Fin.castSucc bit)
    simpa only [output, input, expected,
      arithmeticTargetWord_bit_castSucc, uValueWord_get] using
      htarget.trans hexpected.symm
  have hv : output.core.v = expected.core.v := by
    apply word_eq_of_testBit_eq
    intro bit
    have hpreserve := arithmeticAdderStep_activeSource_get fieldTail
      counterWidth (Fin.castSucc bit) input
    have hinput := arithmeticState_activeSource_get fieldTail counterWidth base
      active target parked flag (Fin.castSucc bit)
    have hexpected := arithmeticState_activeSource_get fieldTail counterWidth base
      active (target + active) parked flag (Fin.castSucc bit)
    simpa only [output, expected, activeSourceWord_bit_castSucc,
      vValueWord_get] using hpreserve.trans (hinput.trans hexpected.symm)
  have hcompare : output.core.compare = expected.core.compare := by
    have htarget := arithmeticAdderStep_target_get_add fieldTail counterWidth
      base active target parked flag (Fin.last fieldTail.succ)
    have hexpected := arithmeticState_target_get fieldTail counterWidth base
      active (target + active) parked flag (Fin.last fieldTail.succ)
    simpa only [output, input, expected, arithmeticTargetWord_bit_last,
      compareBit_get] using htarget.trans hexpected.symm
  have hsCoeff : output.core.sCoeff = expected.core.sCoeff := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_sCoeff fieldTail counterWidth input
  have hrCoeff : output.core.rCoeff = expected.core.rCoeff := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_rCoeff fieldTail counterWidth input
  have hscratchA : output.core.scratchA = expected.core.scratchA := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_scratchA fieldTail counterWidth input
  have hscratchB : output.core.scratchB = expected.core.scratchB := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_scratchB fieldTail counterWidth input
  have hhistory : output.core.history = expected.core.history := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_history fieldTail counterWidth input
  have hactive : output.core.active = expected.core.active := by
    have hpreserve := arithmeticAdderStep_activeSource_get fieldTail
      counterWidth (Fin.last fieldTail.succ) input
    have hinput := arithmeticState_activeSource_get fieldTail counterWidth base
      active target parked flag (Fin.last fieldTail.succ)
    have hexpected := arithmeticState_activeSource_get fieldTail counterWidth base
      active (target + active) parked flag (Fin.last fieldTail.succ)
    simpa only [output, expected, activeSourceWord_bit_last, activeBit_get] using
      hpreserve.trans (hinput.trans hexpected.symm)
  have hcounter : output.core.counter = expected.core.counter := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_counter fieldTail counterWidth input
  have hcore : output.core = expected.core := by
    apply (MK.registerTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.registerTupleEquiv, hu, hv, hcompare, hsCoeff, hrCoeff,
      hscratchA, hscratchB, hhistory, hactive, hcounter]
  have hcoefficientAdder :
      output.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ := by
    apply Prod.ext
    · change output.shared.coefficientAdder.1 = false
      rw [← coefficientCarryInBit_get fieldTail.succ counterWidth]
      change
        (coefficientCarryInBit fieldTail.succ counterWidth).get
            (arithmeticAdderStep fieldTail counterWidth input) = false
      rw [arithmeticAdderStep_carryIn_get]
      exact arithmeticState_carryIn_get fieldTail counterWidth base active
        target parked flag
    · change output.shared.coefficientAdder.2 =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (fieldTail.succ + 1)
      change output.shared.coefficientAdder.2 = 0
      let work : Fin (2 ^ fieldTail.succ) :=
        ⟨output.shared.coefficientAdder.2.val, by
          simpa only [Nat.add_sub_cancel] using
            output.shared.coefficientAdder.2.isLt⟩
      have hwork : work = 0 := by
        apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
        intro bit
        have hclean := arithmeticAdderStep_workCarry_clean fieldTail counterWidth
          bit input
          (arithmeticState_workCarry_get fieldTail counterWidth base active
            target parked flag)
        rw [coefficientCarryWorkBit_get] at hclean
        change output.shared.coefficientAdder.2.val.testBit
          (WireAddress.bitIndex bit).val = false at hclean
        change work.val.testBit (WireAddress.bitIndex bit).val = false
        exact hclean
      apply Fin.ext
      exact congrArg Fin.val hwork
  have hcorrectionCounter :
      output.shared.correctionCounter = expected.shared.correctionCounter := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_correctionCounter fieldTail counterWidth input
  have hpath : output.shared.path = expected.shared.path := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_path fieldTail counterWidth input
  have hcontrol : output.shared.control = expected.shared.control := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_control fieldTail counterWidth input
  have hshared : output.shared = expected.shared := by
    apply (MK.Compact.sharedWorkTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.Compact.sharedWorkTupleEquiv, expected, arithmeticState,
      hcoefficientAdder, hcorrectionCounter, hpath, hcontrol]
  have hpublicTarget : output.target = expected.target := by
    simpa [output, input, expected, arithmeticState] using
      arithmeticAdderStep_publicTarget fieldTail counterWidth input
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ counterWidth).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, hpublicTarget]

/-- Reversing the shared VBE bank subtracts the unchanged active source from
the borrowed target and again leaves its carry workspace clean. -/
lemma arithmeticAdderReverseStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    arithmeticAdderReverseStep fieldTail counterWidth
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      arithmeticState fieldTail counterWidth base active (target - active)
        parked flag := by
  let pre := arithmeticState fieldTail counterWidth base active
    (target - active) parked flag
  have hforward := arithmeticAdderStep_state fieldTail counterWidth base active
    (target - active) parked flag
  have hinverse := EncodedBit.GateSpec.stepList_reverse_stepList
    (arithmeticAdderGates fieldTail counterWidth) pre
  change arithmeticAdderReverseStep fieldTail counterWidth
      (arithmeticAdderStep fieldTail counterWidth pre) = pre at hinverse
  rw [hforward] at hinverse
  simpa [pre, sub_add_cancel] using hinverse

/-- Folded action of the active-source/parked-modulus exchange. -/
def sourceSwapStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (sourceSwapGates fieldTail counterWidth)

/-- The compact source swap exchanges the zero-extended active low word and
the parked modulus while preserving the complete surrounding carrier. -/
lemma sourceSwapStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active parked : Word fieldTail.succ)
    (target : Word (fieldTail.succ + 1)) (flag : Bool) :
    sourceSwapStep fieldTail counterWidth
        (arithmeticState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ active) target parked flag) =
      arithmeticState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ parked) target active flag := by
  let input := arithmeticState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ active) target parked flag
  let output := sourceSwapStep fieldTail counterWidth input
  let expected := arithmeticState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ parked) target active flag
  let eraseCore : MK.Registers fieldTail.succ counterWidth ->
      MK.Registers fieldTail.succ counterWidth :=
    fun core => { core with v := 0, sCoeff := 0 }
  have hcoreFrame : eraseCore output.core = eraseCore input.core := by
    have hpreserve := EncodedBit.Word.swapStep_preserves_projection
      (activeSourceLowWord fieldTail counterWidth)
      (parkedModulusWord fieldTail counterWidth)
      (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
      (fun current => eraseCore current.core)
      (fun _ _ => rfl) (fun _ _ => rfl) input
    simpa only [output, sourceSwapStep, sourceSwapGates,
      EncodedBit.Word.swapStep] using hpreserve
  have hleft := EncodedBit.Word.swapStep_get_left_word
    (activeSourceLowWord fieldTail counterWidth)
    (parkedModulusWord fieldTail counterWidth)
    (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
    (activeSourceLowWord_pairwise_ne fieldTail counterWidth)
    (parkedModulusWord_pairwise_ne fieldTail counterWidth)
    (activeSourceLow_parked_ne fieldTail counterWidth) input
  have hright := EncodedBit.Word.swapStep_get_right_word
    (activeSourceLowWord fieldTail counterWidth)
    (parkedModulusWord fieldTail counterWidth)
    (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
    (activeSourceLowWord_pairwise_ne fieldTail counterWidth)
    (parkedModulusWord_pairwise_ne fieldTail counterWidth)
    (activeSourceLow_parked_ne fieldTail counterWidth) input
  have hactiveHigh : active.val.testBit fieldTail.succ = false :=
    Nat.testBit_lt_two_pow active.isLt
  have hparkedHigh : parked.val.testBit fieldTail.succ = false :=
    Nat.testBit_lt_two_pow parked.isLt
  have hv : output.core.v = expected.core.v := by
    apply word_eq_of_testBit_eq
    intro bit
    have hread := congrFun hleft bit
    calc
      output.core.v.val.testBit bit.val =
          ((activeSourceLowWord fieldTail counterWidth).bit bit).get output := by
        simp [activeSourceLowWord]
      _ = ((parkedModulusWord fieldTail counterWidth).bit bit).get input := by
        simpa [output, sourceSwapStep, sourceSwapGates,
          EncodedBit.Word.swapStep] using hread
      _ = parked.val.testBit bit.val := by
        exact arithmeticState_parked_get fieldTail counterWidth base
          (widenFixedWord fieldTail.succ active) target parked flag bit
      _ = expected.core.v.val.testBit bit.val := by
        simp [expected, arithmeticState]
  have hsCoeff : output.core.sCoeff = expected.core.sCoeff := by
    apply word_eq_of_testBit_eq
    intro bit
    refine Fin.lastCases ?_ ?_ bit
    · have hread := EncodedBit.Word.swapStep_get_observed_of_swap_ne
        (activeSourceLowWord fieldTail counterWidth)
        (parkedModulusWord fieldTail counterWidth)
        (fun low => activeSourceLow_parked_ne fieldTail counterWidth low low)
        ((sCoeffValueWord fieldTail.succ counterWidth).bit
          (Fin.last fieldTail.succ))
        (activeSourceLow_sCoeffHigh_ne fieldTail counterWidth)
        (parkedModulus_sCoeffHigh_ne fieldTail counterWidth) input
      simpa [output, input, expected, sourceSwapStep, sourceSwapGates,
        EncodedBit.Word.swapStep, arithmeticState, hactiveHigh,
        hparkedHigh] using hread
    · intro low
      have hread := congrFun hright low
      calc
        output.core.sCoeff.val.testBit low.val =
            ((parkedModulusWord fieldTail counterWidth).bit low).get output := by
          simp [parkedModulusWord]
        _ = ((activeSourceLowWord fieldTail counterWidth).bit low).get input := by
          simpa [output, sourceSwapStep, sourceSwapGates,
            EncodedBit.Word.swapStep] using hread
        _ = (widenFixedWord fieldTail.succ active).val.testBit low.val := by
          simpa [input, activeSourceLowWord] using
            arithmeticState_activeSource_get fieldTail counterWidth base
              (widenFixedWord fieldTail.succ active) target parked flag
              (Fin.castSucc low)
        _ = expected.core.sCoeff.val.testBit low.val := by
          simp [expected, arithmeticState]
  have hu : output.core.u = expected.core.u := by
    have h := congrArg (fun core => core.u) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState] using h
  have hcompare : output.core.compare = expected.core.compare := by
    have h := congrArg (fun core => core.compare) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState] using h
  have hrCoeff : output.core.rCoeff = expected.core.rCoeff := by
    have h := congrArg (fun core => core.rCoeff) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState] using h
  have hscratchA : output.core.scratchA = expected.core.scratchA := by
    have h := congrArg (fun core => core.scratchA) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState] using h
  have hscratchB : output.core.scratchB = expected.core.scratchB := by
    have h := congrArg (fun core => core.scratchB) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState] using h
  have hhistory : output.core.history = expected.core.history := by
    have h := congrArg (fun core => core.history) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState] using h
  have hactive : output.core.active = expected.core.active := by
    have h := congrArg (fun core => core.active) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState, hactiveHigh,
      hparkedHigh] using h
  have hcounter : output.core.counter = expected.core.counter := by
    have h := congrArg (fun core => core.counter) hcoreFrame
    simpa [eraseCore, input, expected, arithmeticState] using h
  have hcore : output.core = expected.core := by
    apply (MK.registerTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.registerTupleEquiv, hu, hv, hcompare, hsCoeff, hrCoeff,
      hscratchA, hscratchB, hhistory, hactive, hcounter]
  have houter : (output.shared, output.target) =
      (input.shared, input.target) := by
    have hpreserve := EncodedBit.Word.swapStep_preserves_projection
      (activeSourceLowWord fieldTail counterWidth)
      (parkedModulusWord fieldTail counterWidth)
      (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
      (fun current => (current.shared, current.target))
      (fun _ _ => rfl) (fun _ _ => rfl) input
    simpa only [output, sourceSwapStep, sourceSwapGates,
      EncodedBit.Word.swapStep] using hpreserve
  have hshared : output.shared = expected.shared := by
    have h := congrArg Prod.fst houter
    simpa [input, expected, arithmeticState] using h
  have htarget : output.target = expected.target := by
    have h := congrArg Prod.snd houter
    simpa [input, expected, arithmeticState] using h
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ counterWidth).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, htarget]

/-- Folded action that records the modular-reduction predicate. -/
def copyReductionFlagStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (copyReductionFlagGates fieldTail counterWidth)

@[simp] private lemma scratchABit_flip (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (scratchABit fieldTail.succ counterWidth).flip x =
      { x with core := { x.core with scratchA := !x.core.scratchA } } := by
  rcases x with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB,
    history, active, counter⟩, shared, target⟩
  rfl

@[simp] private lemma scratchBBit_flip (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (scratchBBit fieldTail.succ counterWidth).flip x =
      { x with core := { x.core with scratchB := !x.core.scratchB } } := by
  rcases x with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB,
    history, active, counter⟩, shared, target⟩
  rfl

/-- Exact record action of the compact X/CNOT reduction-predicate copy. -/
lemma copyReductionFlagStep_eq (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    copyReductionFlagStep fieldTail counterWidth x =
      { x with core :=
          { x.core with scratchA := (!x.core.scratchA) ^^ x.core.compare } } := by
  rcases x with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB,
    history, active, counter⟩, shared, target⟩
  by_cases hcompare : compare <;> cases scratchA <;>
    simp [copyReductionFlagStep, copyReductionFlagGates,
      EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
      EncodedBit.cnotStep, hcompare]

/-- On an arithmetic-state view, the copy stage changes only the retained
reduction flag. -/
lemma copyReductionFlagStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    copyReductionFlagStep fieldTail counterWidth
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      arithmeticState fieldTail counterWidth base active target parked
        ((!flag) ^^ target.val.testBit fieldTail.succ) := by
  rw [copyReductionFlagStep_eq]
  rfl

/-- Folded conditional clearing of the active modulus word. -/
def clearActiveModulusStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (clearActiveModulusGates fieldTail counterWidth p)

/-- Carrier projection omitting exactly the borrowed active-source word. -/
private structure NonActiveFrame (n counterWidth : Nat) where
  u : Word n
  compare : Bool
  sCoeff : Word (n + 1)
  rCoeff : Word (n + 1)
  scratchA : Bool
  scratchB : Bool
  history : Word (2 * n)
  counter : Word counterWidth
  shared : MK.Compact.SharedWork n counterWidth
  target : Word n

private def nonActiveFrame (n counterWidth : Nat)
    (current : MK.Compact.Registers n counterWidth) :
    NonActiveFrame n counterWidth where
  u := current.core.u
  compare := current.core.compare
  sCoeff := current.core.sCoeff
  rCoeff := current.core.rCoeff
  scratchA := current.core.scratchA
  scratchB := current.core.scratchB
  history := current.core.history
  counter := current.core.counter
  shared := current.shared
  target := current.target

/-- The conditional constant xor clears the active modulus exactly on the
retained reduction branch and preserves all borrowed surrounding fields. -/
lemma clearActiveModulusStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    clearActiveModulusStep fieldTail counterWidth p
        (arithmeticState fieldTail counterWidth base
          (modulusWordLabel fieldTail p) target parked flag) =
      arithmeticState fieldTail counterWidth base
        (if flag then 0 else modulusWordLabel fieldTail p)
        target parked flag := by
  let input := arithmeticState fieldTail counterWidth base
    (modulusWordLabel fieldTail p) target parked flag
  let output := clearActiveModulusStep fieldTail counterWidth p input
  let expected := arithmeticState fieldTail counterWidth base
    (if flag then 0 else modulusWordLabel fieldTail p) target parked flag
  have hframe : nonActiveFrame fieldTail.succ counterWidth output =
      nonActiveFrame fieldTail.succ counterWidth input := by
    have hpreserve :
        nonActiveFrame fieldTail.succ counterWidth
            (EncodedBit.GateSpec.stepList
              (clearActiveModulusGates fieldTail counterWidth p) input) =
          nonActiveFrame fieldTail.succ counterWidth input := by
      apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      intro gate hgate
      rw [clearActiveModulusGates,
        EncodedBit.Word.controlledXorConstantGates] at hgate
      rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
      refine Fin.lastCases ?_ ?_ bit
      · intro current
        rw [activeSourceWord_bit_last]
        rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
          scratchB, history, active, counter⟩, shared, publicTarget⟩
        rfl
      · intro low current
        rw [activeSourceWord_bit_castSucc]
        rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
          scratchB, history, active, counter⟩, shared, publicTarget⟩
        rfl
    simpa only [output, clearActiveModulusStep] using hpreserve
  have hactiveRead : forall bit,
      ((activeSourceWord fieldTail counterWidth).bit bit).get output =
        ((activeSourceWord fieldTail counterWidth).bit bit).get expected := by
    intro bit
    have hread := EncodedBit.Word.controlledXorConstantStep_get_target
      (scratchABit fieldTail.succ counterWidth)
      (activeSourceWord fieldTail counterWidth)
      (modulusWordLabel fieldTail p)
      (reductionFlag_activeSource_ne fieldTail counterWidth)
      bit (fun other hother =>
        activeSourceWord_pairwise_ne fieldTail counterWidth other bit hother)
      input
    have hstep :
        ((activeSourceWord fieldTail counterWidth).bit bit).get output =
          (((activeSourceWord fieldTail counterWidth).bit bit).get input ^^
            (flag && (modulusWordLabel fieldTail p).val.testBit bit.val)) := by
      simpa [output, clearActiveModulusStep, clearActiveModulusGates,
        EncodedBit.Word.controlledXorConstantStep, input, arithmeticState] using
        hread
    have hinput := arithmeticState_activeSource_get fieldTail counterWidth base
      (modulusWordLabel fieldTail p) target parked flag bit
    have hexpected := arithmeticState_activeSource_get fieldTail counterWidth base
      (if flag then 0 else modulusWordLabel fieldTail p) target parked flag bit
    rw [hstep]
    rw [show ((activeSourceWord fieldTail counterWidth).bit bit).get input =
        (modulusWordLabel fieldTail p).val.testBit bit.val by
      simpa only [input] using hinput]
    rw [show ((activeSourceWord fieldTail counterWidth).bit bit).get expected =
        (if flag then 0 else modulusWordLabel fieldTail p).val.testBit bit.val by
      simpa only [expected] using hexpected]
    cases flag <;> simp
  have hv : output.core.v = expected.core.v := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [activeSourceWord_bit_castSucc, vValueWord_get] using
      hactiveRead (Fin.castSucc bit)
  have hactive : output.core.active = expected.core.active := by
    simpa only [activeSourceWord_bit_last, activeBit_get] using
      hactiveRead (Fin.last fieldTail.succ)
  have hframeExpected : nonActiveFrame fieldTail.succ counterWidth output =
      nonActiveFrame fieldTail.succ counterWidth expected := by
    calc
      nonActiveFrame fieldTail.succ counterWidth output =
          nonActiveFrame fieldTail.succ counterWidth input := hframe
      _ = nonActiveFrame fieldTail.succ counterWidth expected := by
        simp [nonActiveFrame, input, expected, arithmeticState]
  have hu : output.core.u = expected.core.u := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.u hframeExpected
  have hcompare : output.core.compare = expected.core.compare := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.compare hframeExpected
  have hsCoeff : output.core.sCoeff = expected.core.sCoeff := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.sCoeff hframeExpected
  have hrCoeff : output.core.rCoeff = expected.core.rCoeff := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.rCoeff hframeExpected
  have hscratchA : output.core.scratchA = expected.core.scratchA := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.scratchA hframeExpected
  have hscratchB : output.core.scratchB = expected.core.scratchB := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.scratchB hframeExpected
  have hhistory : output.core.history = expected.core.history := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.history hframeExpected
  have hcounter : output.core.counter = expected.core.counter := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.counter hframeExpected
  have hshared : output.shared = expected.shared := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.shared hframeExpected
  have htarget : output.target = expected.target := by
    simpa [nonActiveFrame] using congrArg NonActiveFrame.target hframeExpected
  have hcore : output.core = expected.core := by
    apply (MK.registerTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.registerTupleEquiv, hu, hv, hcompare, hsCoeff, hrCoeff,
      hscratchA, hscratchB, hhistory, hactive, hcounter]
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ counterWidth).injective
  apply Prod.ext
  · exact hcore
  · apply Prod.ext
    · exact hshared
    · exact htarget

/-- Folded inverse of the active-modulus clearing step. -/
def restoreActiveModulusStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (restoreActiveModulusGates fieldTail counterWidth p)

/-- The reverse constant-xor stage restores the active modulus after the
matching clear stage on either reduction branch. -/
lemma restoreActiveModulusStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    restoreActiveModulusStep fieldTail counterWidth p
        (arithmeticState fieldTail counterWidth base
          (if flag then 0 else modulusWordLabel fieldTail p)
          target parked flag) =
      arithmeticState fieldTail counterWidth base
        (modulusWordLabel fieldTail p) target parked flag := by
  let original := arithmeticState fieldTail counterWidth base
    (modulusWordLabel fieldTail p) target parked flag
  have hclear := clearActiveModulusStep_state fieldTail counterWidth p base
    target parked flag
  have hinverse :=
    EncodedBit.Word.controlledXorConstantUnloadStep_after_controlledXorConstantStep
      (scratchABit fieldTail.succ counterWidth)
      (activeSourceWord fieldTail counterWidth)
      (modulusWordLabel fieldTail p)
      (reductionFlag_activeSource_ne fieldTail counterWidth) original
  change restoreActiveModulusStep fieldTail counterWidth p
      (clearActiveModulusStep fieldTail counterWidth p original) =
    original at hinverse
  rw [hclear] at hinverse
  simpa [original] using hinverse

/-- Folded cleanup of the retained modular-reduction flag. -/
def cleanupReductionFlagStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (cleanupReductionFlagGates fieldTail counterWidth)

/-- Exact record action of the final CNOT reduction-flag cleanup. -/
lemma cleanupReductionFlagStep_eq (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    cleanupReductionFlagStep fieldTail counterWidth x =
      { x with core :=
          { x.core with scratchA := x.core.scratchA ^^ x.core.compare } } := by
  rcases x with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB,
    history, active, counter⟩, shared, target⟩
  by_cases hcompare : compare <;> cases scratchA <;>
    simp [cleanupReductionFlagStep, cleanupReductionFlagGates,
      EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
      EncodedBit.cnotStep, hcompare]

/-- On an arithmetic-state view, cleanup xors the subtraction high bit back
out of the retained flag. -/
lemma cleanupReductionFlagStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    cleanupReductionFlagStep fieldTail counterWidth
        (arithmeticState fieldTail counterWidth base active target parked flag) =
      arithmeticState fieldTail counterWidth base active target parked
        (flag ^^ target.val.testBit fieldTail.succ) := by
  rw [cleanupReductionFlagStep_eq]
  rfl

/-- Folded action of the complete eleven-stage compact VBE reduction. -/
def modularReduceStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (modularReduceGates fieldTail counterWidth p)

/-- The flattened reduction ledger executes the eleven named compact stages
in source order. -/
lemma modularReduceStep_eq_stages (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    modularReduceStep fieldTail counterWidth p x =
      arithmeticAdderStep fieldTail counterWidth
        (cleanupReductionFlagStep fieldTail counterWidth
          (arithmeticAdderReverseStep fieldTail counterWidth
            (sourceSwapStep fieldTail counterWidth
              (restoreActiveModulusStep fieldTail counterWidth p
                (arithmeticAdderStep fieldTail counterWidth
                  (clearActiveModulusStep fieldTail counterWidth p
                    (copyReductionFlagStep fieldTail counterWidth
                      (arithmeticAdderReverseStep fieldTail counterWidth
                        (sourceSwapStep fieldTail counterWidth
                          (arithmeticAdderStep fieldTail counterWidth
                            x)))))))))) := by
  simp only [modularReduceStep, modularReduceGates,
    arithmeticAdderStep, arithmeticAdderReverseStep, sourceSwapStep,
    copyReductionFlagStep, clearActiveModulusStep,
    restoreActiveModulusStep, cleanupReductionFlagStep,
    EncodedBit.GateSpec.stepList_append]

/-- The eleven-stage compact ledger performs one conditional subtraction on
the two-modulus input range and retains the public reduction predicate. -/
lemma modularReduceStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (raw : Word (fieldTail.succ + 1))
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hraw : raw.val < 2 * p) :
    modularReduceStep fieldTail counterWidth p
        (arithmeticState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ 0) raw ⟨p, hp⟩ false) =
      arithmeticState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ 0)
        (reducedWord fieldTail p hpPos hp raw hraw) ⟨p, hp⟩
        (decide (p ≤ raw.val)) := by
  let modulus : Word fieldTail.succ := ⟨p, hp⟩
  let zero : Word fieldTail.succ := 0
  let zeroWide : Word (fieldTail.succ + 1) :=
    widenFixedWord fieldTail.succ zero
  let modulusWide : Word (fieldTail.succ + 1) := modulusWordLabel fieldTail p
  let subWord : Word (fieldTail.succ + 1) := raw - modulusWide
  let reduced : Word (fieldTail.succ + 1) :=
    reducedWord fieldTail p hpPos hp raw hraw
  let reducedFlag : Bool := decide (p ≤ raw.val)
  have hzeroWide : zeroWide = 0 := by
    apply Fin.ext
    rfl
  have hmodulusWide : widenFixedWord fieldTail.succ modulus = modulusWide := by
    apply Fin.ext
    simp [modulus, modulusWide, modulusWordLabel_val fieldTail p hp]
  have hsubBit : subWord.val.testBit fieldTail.succ =
      decide (raw.val < p) := by
    calc
      subWord.val.testBit fieldTail.succ =
          ((((raw.val : ZMod (2 ^ (fieldTail.succ + 1))) -
            ((modulusWide.val : Nat) :
              ZMod (2 ^ (fieldTail.succ + 1)))).val).testBit
              fieldTail.succ) := by
        simp only [subWord]
        rw [fin_sub_val_eq_zmod_sub_val]
      _ = ((((raw.val : ZMod (2 ^ (fieldTail.succ + 1))) -
            (p : ZMod (2 ^ (fieldTail.succ + 1)))).val).testBit
              fieldTail.succ) := by
        rw [show modulusWide.val = p by
          exact modulusWordLabel_val fieldTail p hp]
      _ = decide (raw.val < p) :=
        MAU.Addition.VBEArithmetic.subtractModulusRaw_msb
          hpPos hp hraw
  have hunderflow : decide (raw.val < p) = !reducedFlag := by
    by_cases hreduce : p ≤ raw.val
    · have hnlt : ¬raw.val < p := Nat.not_lt_of_ge hreduce
      simp [reducedFlag, hreduce, hnlt]
    · have hlt : raw.val < p := Nat.lt_of_not_ge hreduce
      simp [reducedFlag, hreduce, hlt]
  have hsubVal : subWord.val =
      if p ≤ raw.val then raw.val - p
      else 2 ^ (fieldTail.succ + 1) + raw.val - p := by
    simp only [subWord]
    rw [fin_sub_val_eq_zmod_sub_val]
    rw [MAU.Addition.VBEArithmetic.zmodVal_natCast_sub_natCast
      raw.isLt modulusWide.isLt]
    simp [modulusWide, modulusWordLabel_val fieldTail p hp]
  have haddBack :
      subWord + (if reducedFlag then 0 else modulusWide) = reduced := by
    apply Fin.ext
    by_cases hreduce : p ≤ raw.val
    · have hsubOrd : subWord.val = raw.val - p := by
        rw [hsubVal, if_pos hreduce]
      simp [reducedFlag, hreduce, reduced,
        reducedWord, MAU.Addition.VBEArithmetic.reduceOnce, hsubOrd]
    · have hlt : raw.val < p := Nat.lt_of_not_ge hreduce
      have hsubWrap : subWord.val =
          2 ^ (fieldTail.succ + 1) + raw.val - p := by
        rw [hsubVal, if_neg hreduce]
      rw [Fin.val_add]
      simp only [reducedFlag, decide_eq_false hreduce, Bool.false_eq_true,
        if_false, reduced, reducedWord]
      rw [hsubWrap]
      simp only [modulusWide]
      rw [modulusWordLabel_val fieldTail p hp]
      rw [MAU.Addition.VBEArithmetic.reduceOnce, if_neg hreduce]
      have hsum :
          (2 ^ (fieldTail.succ + 1) + raw.val - p) + p =
            2 ^ (fieldTail.succ + 1) + raw.val := by omega
      rw [hsum]
      simp [Nat.mod_eq_of_lt raw.isLt]
  have hreducedHigh : reduced.val.testBit fieldTail.succ = false := by
    apply Nat.testBit_lt_two_pow
    change MAU.Addition.VBEArithmetic.reduceOnce p raw.val <
      2 ^ fieldTail.succ
    exact (MAU.Addition.VBEArithmetic.reduceOnce_lt hpPos hraw).trans hp
  let s0 := arithmeticState fieldTail counterWidth base zeroWide raw modulus false
  let s1 := arithmeticState fieldTail counterWidth base zeroWide raw modulus false
  let s2 := arithmeticState fieldTail counterWidth base modulusWide raw zero false
  let s3 := arithmeticState fieldTail counterWidth base modulusWide subWord zero false
  let s4 := arithmeticState fieldTail counterWidth base modulusWide subWord zero
    reducedFlag
  let s5 := arithmeticState fieldTail counterWidth base
    (if reducedFlag then 0 else modulusWide) subWord zero reducedFlag
  let s6 := arithmeticState fieldTail counterWidth base
    (if reducedFlag then 0 else modulusWide) reduced zero reducedFlag
  let s7 := arithmeticState fieldTail counterWidth base modulusWide reduced zero
    reducedFlag
  let s8 := arithmeticState fieldTail counterWidth base zeroWide reduced modulus
    reducedFlag
  let s9 := arithmeticState fieldTail counterWidth base zeroWide
    (reduced - zeroWide) modulus reducedFlag
  let s10 := arithmeticState fieldTail counterWidth base zeroWide
    (reduced - zeroWide) modulus reducedFlag
  let s11 := arithmeticState fieldTail counterWidth base zeroWide reduced modulus
    reducedFlag
  have hs1 : arithmeticAdderStep fieldTail counterWidth s0 = s1 := by
    simpa [s0, s1, hzeroWide] using
      arithmeticAdderStep_state fieldTail counterWidth base zeroWide raw
        modulus false
  have hs2 : sourceSwapStep fieldTail counterWidth s1 = s2 := by
    simpa [s1, s2, zeroWide, zero, hmodulusWide] using
      sourceSwapStep_state fieldTail counterWidth base zero modulus raw false
  have hs3 : arithmeticAdderReverseStep fieldTail counterWidth s2 = s3 := by
    simpa [s2, s3, subWord] using
      arithmeticAdderReverseStep_state fieldTail counterWidth base modulusWide
        raw zero false
  have hs4 : copyReductionFlagStep fieldTail counterWidth s3 = s4 := by
    simpa [s3, s4, hsubBit, hunderflow] using
      copyReductionFlagStep_state fieldTail counterWidth base modulusWide
        subWord zero false
  have hs5 : clearActiveModulusStep fieldTail counterWidth p s4 = s5 := by
    simpa [s4, s5, modulusWide] using
      clearActiveModulusStep_state fieldTail counterWidth p base subWord zero
        reducedFlag
  have hs6 : arithmeticAdderStep fieldTail counterWidth s5 = s6 := by
    simpa [s5, s6, haddBack] using
      arithmeticAdderStep_state fieldTail counterWidth base
        (if reducedFlag then 0 else modulusWide) subWord zero reducedFlag
  have hs7 : restoreActiveModulusStep fieldTail counterWidth p s6 = s7 := by
    simpa [s6, s7, modulusWide] using
      restoreActiveModulusStep_state fieldTail counterWidth p base reduced zero
        reducedFlag
  have hs8 : sourceSwapStep fieldTail counterWidth s7 = s8 := by
    simpa [s7, s8, zeroWide, zero, hmodulusWide] using
      sourceSwapStep_state fieldTail counterWidth base modulus zero reduced
        reducedFlag
  have hs9 : arithmeticAdderReverseStep fieldTail counterWidth s8 = s9 := by
    simpa [s8, s9] using
      arithmeticAdderReverseStep_state fieldTail counterWidth base zeroWide
        reduced modulus reducedFlag
  have hs10 : cleanupReductionFlagStep fieldTail counterWidth s9 = s10 := by
    simpa [s9, s10, hzeroWide, hreducedHigh] using
      cleanupReductionFlagStep_state fieldTail counterWidth base zeroWide
        (reduced - zeroWide) modulus reducedFlag
  have hs11 : arithmeticAdderStep fieldTail counterWidth s10 = s11 := by
    simpa [s10, s11, hzeroWide] using
      arithmeticAdderStep_state fieldTail counterWidth base zeroWide
        (reduced - zeroWide) modulus reducedFlag
  change modularReduceStep fieldTail counterWidth p s0 = s11
  rw [modularReduceStep_eq_stages, hs1, hs2, hs3, hs4, hs5, hs6, hs7,
    hs8, hs9, hs10, hs11]

/-- Canonical widened representative of the modular sum of two field words. -/
def modularSumWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (a b : Word fieldTail.succ) :
    Word (fieldTail.succ + 1) :=
  ⟨(a.val + b.val) % p, by
    have hmod := Nat.mod_lt (a.val + b.val) hpPos
    have hpow : 2 ^ fieldTail.succ < 2 ^ (fieldTail.succ + 1) :=
      Nat.pow_lt_pow_right (by decide) fieldTail.succ.lt_succ_self
    exact hmod.trans (hp.trans hpow)⟩

@[simp] lemma modularSumWord_val (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (a b : Word fieldTail.succ) :
    (modularSumWord fieldTail p hpPos hp a b).val =
      (a.val + b.val) % p :=
  rfl

/-- Canonical field-width representative of the modular sum of two field
words. -/
def modularSumFixedWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (a b : Word fieldTail.succ) :
    Word fieldTail.succ :=
  ⟨(a.val + b.val) % p, (Nat.mod_lt _ hpPos).trans hp⟩

@[simp] lemma modularSumFixedWord_val
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (a b : Word fieldTail.succ) :
    (modularSumFixedWord fieldTail p hpPos hp a b).val =
      (a.val + b.val) % p :=
  rfl

/-- Canonical field-width representative of `target - source` modulo `p`. -/
def modularDifferenceWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (target source : Word fieldTail.succ) : Word fieldTail.succ :=
  ⟨(target.val + p - source.val) % p,
    (Nat.mod_lt _ hpPos).trans hp⟩

@[simp] lemma modularDifferenceWord_val
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (target source : Word fieldTail.succ) :
    (modularDifferenceWord fieldTail p hpPos hp target source).val =
      (target.val + p - source.val) % p :=
  rfl

/-- The fixed-width target update is subtraction in the residue field. -/
lemma modularDifferenceWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (target source : Word fieldTail.succ) (hsource : source.val < p) :
    ((modularDifferenceWord fieldTail p hpPos hp target source).val : ZMod p) =
      (target.val : ZMod p) - (source.val : ZMod p) := by
  rw [modularDifferenceWord_val, ZMod.natCast_mod]
  have hle : source.val <= target.val + p := by omega
  rw [Nat.cast_sub hle, Nat.cast_add]
  simp

/-- Subtracting the source from its canonical modular sum with a target
recovers that target. -/
lemma modularDifferenceWord_sum
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (target source : Word fieldTail.succ)
    (htarget : target.val < p) (hsource : source.val < p) :
    modularDifferenceWord fieldTail p hpPos hp
        (modularSumFixedWord fieldTail p hpPos hp target source) source =
      target := by
  let sum := modularSumFixedWord fieldTail p hpPos hp target source
  let difference := modularDifferenceWord fieldTail p hpPos hp sum source
  have hcast : (difference.val : ZMod p) = (target.val : ZMod p) := by
    calc
      (difference.val : ZMod p) =
          (sum.val : ZMod p) - (source.val : ZMod p) := by
        exact modularDifferenceWord_cast fieldTail p hpPos hp sum source hsource
      _ = ((target.val + source.val) : ZMod p) -
          (source.val : ZMod p) := by
        rw [show (sum.val : ZMod p) =
            ((target.val + source.val) : ZMod p) by
          simp [sum, modularSumFixedWord]]
      _ = (target.val : ZMod p) := by ring
  have hmod :=
    (ZMod.natCast_eq_natCast_iff' difference.val target.val p).mp hcast
  have hdifference : difference.val < p := by
    exact Nat.mod_lt _ hpPos
  apply Fin.ext
  change difference.val = target.val
  simpa [Nat.mod_eq_of_lt hdifference, Nat.mod_eq_of_lt htarget] using hmod

/-- Adding a source to the canonical modular difference recovers the target.
This is the arithmetic bridge used to run the exact modular-add ledger in
reverse on an arbitrary canonical target. -/
lemma modularSumWord_difference
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (source target : Word fieldTail.succ)
    (hsource : source.val < p) (htarget : target.val < p) :
    modularSumWord fieldTail p hpPos hp source
        (modularDifferenceWord fieldTail p hpPos hp target source) =
      widenFixedWord fieldTail.succ target := by
  apply Fin.ext
  change
    (source.val + ((target.val + p - source.val) % p)) % p = target.val
  by_cases hle : source.val ≤ target.val
  · have hsplit :
        target.val + p - source.val = p + (target.val - source.val) := by
      omega
    have hdiffLt : target.val - source.val < p := by omega
    have hinner :
        (target.val + p - source.val) % p = target.val - source.val := by
      rw [hsplit]
      simp [Nat.mod_eq_of_lt hdiffLt]
    rw [hinner]
    have hsum : source.val + (target.val - source.val) = target.val := by
      omega
    rw [hsum, Nat.mod_eq_of_lt htarget]
  · have hlt : target.val < source.val := Nat.lt_of_not_ge hle
    have hinnerLt : target.val + p - source.val < p := by omega
    rw [Nat.mod_eq_of_lt hinnerLt]
    have hsum :
        source.val + (target.val + p - source.val) = target.val + p := by
      omega
    rw [hsum]
    simp [Nat.mod_eq_of_lt htarget]

/-- The same eleven-stage compact ledger is a general modular adder when both
the active source and borrowed target start as canonical residues.  In
particular, the parked modulus and every borrowed comparison/carry bit are
restored, so reversing this exact ledger gives modular subtraction without a
second arithmetic workspace. -/
lemma modularReduceStep_add_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (a b : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (ha : a.val < p) (hb : b.val < p) :
    modularReduceStep fieldTail counterWidth p
        (arithmeticState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ a)
          (widenFixedWord fieldTail.succ b) ⟨p, hp⟩ false) =
      arithmeticState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ a)
        (modularSumWord fieldTail p hpPos hp a b) ⟨p, hp⟩ false := by
  let modulus : Word fieldTail.succ := ⟨p, hp⟩
  let active : Word (fieldTail.succ + 1) :=
    widenFixedWord fieldTail.succ a
  let target : Word (fieldTail.succ + 1) :=
    widenFixedWord fieldTail.succ b
  let modulusWide : Word (fieldTail.succ + 1) := modulusWordLabel fieldTail p
  let sumWord : Word (fieldTail.succ + 1) := target + active
  have hsumVal : sumWord.val = a.val + b.val := by
    simp only [sumWord, target, active, Fin.val_add, widenFixedWord_val]
    have hsum : a.val + b.val < 2 ^ (fieldTail.succ + 1) :=
      MAU.Addition.VBEArithmetic.sum_lt_wordModulus
        (Nat.le_of_lt hp) ha hb
    have hsum' : b.val + a.val < 2 ^ (fieldTail.succ + 1) := by omega
    rw [Nat.mod_eq_of_lt hsum']
    omega
  have hraw : sumWord.val < 2 * p := by
    rw [hsumVal]
    omega
  let subWord : Word (fieldTail.succ + 1) := sumWord - modulusWide
  let reduced : Word (fieldTail.succ + 1) :=
    reducedWord fieldTail p hpPos hp sumWord hraw
  let reducedFlag : Bool := decide (p ≤ a.val + b.val)
  have hmodulusWide : widenFixedWord fieldTail.succ modulus = modulusWide := by
    apply Fin.ext
    simp [modulus, modulusWide, modulusWordLabel_val fieldTail p hp]
  have hsubBit :
      subWord.val.testBit fieldTail.succ =
        decide (a.val + b.val < p) := by
    calc
      subWord.val.testBit fieldTail.succ =
          (((((sumWord.val : Nat) : ZMod (2 ^ (fieldTail.succ + 1))) -
            ((modulusWide.val : Nat) :
              ZMod (2 ^ (fieldTail.succ + 1)))).val).testBit
                fieldTail.succ) := by
        simp only [subWord]
        rw [fin_sub_val_eq_zmod_sub_val]
      _ = (((((a.val + b.val : Nat) :
            ZMod (2 ^ (fieldTail.succ + 1))) -
            (p : ZMod (2 ^ (fieldTail.succ + 1)))).val).testBit
                fieldTail.succ) := by
        rw [hsumVal, show modulusWide.val = p by
          exact modulusWordLabel_val fieldTail p hp]
      _ = decide (a.val + b.val < p) :=
        MAU.Addition.VBEArithmetic.subtractModulus_msb
          (Nat.le_of_lt hp) ha hb
  have hunderflow :
      decide (a.val + b.val < p) = !reducedFlag := by
    by_cases hreduce : p ≤ a.val + b.val
    · have hnlt : ¬a.val + b.val < p := Nat.not_lt_of_ge hreduce
      simp [reducedFlag, hreduce, hnlt]
    · have hlt : a.val + b.val < p := Nat.lt_of_not_ge hreduce
      simp [reducedFlag, hreduce, hlt]
  have hsubVal : subWord.val =
      if p ≤ a.val + b.val then a.val + b.val - p
      else 2 ^ (fieldTail.succ + 1) + (a.val + b.val) - p := by
    simp only [subWord]
    rw [fin_sub_val_eq_zmod_sub_val]
    rw [MAU.Addition.VBEArithmetic.zmodVal_natCast_sub_natCast
      sumWord.isLt modulusWide.isLt]
    simp [hsumVal, modulusWide, modulusWordLabel_val fieldTail p hp]
  have haddBack :
      subWord + (if reducedFlag then 0 else modulusWide) = reduced := by
    apply Fin.ext
    by_cases hreduce : p ≤ a.val + b.val
    · have hsubOrd : subWord.val = a.val + b.val - p := by
        rw [hsubVal, if_pos hreduce]
      simp [reducedFlag, hreduce, reduced, reducedWord,
        MAU.Addition.VBEArithmetic.reduceOnce, hsumVal, hsubOrd]
    · have hlt : a.val + b.val < p := Nat.lt_of_not_ge hreduce
      have hsubWrap : subWord.val =
          2 ^ (fieldTail.succ + 1) + (a.val + b.val) - p := by
        rw [hsubVal, if_neg hreduce]
      rw [Fin.val_add]
      simp only [reducedFlag, decide_eq_false hreduce, Bool.false_eq_true,
        if_false, reduced, reducedWord]
      rw [hsubWrap]
      rw [modulusWordLabel_val fieldTail p hp]
      rw [hsumVal]
      rw [MAU.Addition.VBEArithmetic.reduceOnce, if_neg hreduce]
      have hsum :
          (2 ^ (fieldTail.succ + 1) + (a.val + b.val) - p) + p =
            2 ^ (fieldTail.succ + 1) + (a.val + b.val) := by omega
      rw [hsum]
      have hwide : a.val + b.val < 2 ^ (fieldTail.succ + 1) :=
        MAU.Addition.VBEArithmetic.sum_lt_wordModulus
          (Nat.le_of_lt hp) ha hb
      simp [Nat.mod_eq_of_lt hwide]
  have hcleanupBit :
      (reduced - active).val.testBit fieldTail.succ = reducedFlag := by
    calc
      (reduced - active).val.testBit fieldTail.succ =
          (((((reduced.val : Nat) : ZMod (2 ^ (fieldTail.succ + 1))) -
            ((active.val : Nat) :
              ZMod (2 ^ (fieldTail.succ + 1)))).val).testBit
                fieldTail.succ) := by
        rw [fin_sub_val_eq_zmod_sub_val]
      _ = (((((MAU.Addition.VBEArithmetic.reduceOnce p
              (a.val + b.val) : Nat) :
              ZMod (2 ^ (fieldTail.succ + 1))) -
            (a.val : ZMod (2 ^ (fieldTail.succ + 1)))).val).testBit
                fieldTail.succ) := by
        rw [show reduced.val =
          MAU.Addition.VBEArithmetic.reduceOnce p (a.val + b.val) by
            simp [reduced, reducedWord, hsumVal]]
        rw [show active.val = a.val by rfl]
      _ = reducedFlag := by
        simpa [reducedFlag] using
          (MAU.Addition.VBEArithmetic.cleanupProbe_msb
            (n := fieldTail.succ) (N := p) (a := a.val) (b := b.val)
            (Nat.le_of_lt hp) ha hb)
  let s0 := arithmeticState fieldTail counterWidth base active target
    modulus false
  let s1 := arithmeticState fieldTail counterWidth base active sumWord
    modulus false
  let s2 := arithmeticState fieldTail counterWidth base modulusWide sumWord
    a false
  let s3 := arithmeticState fieldTail counterWidth base modulusWide subWord
    a false
  let s4 := arithmeticState fieldTail counterWidth base modulusWide subWord
    a reducedFlag
  let s5 := arithmeticState fieldTail counterWidth base
    (if reducedFlag then 0 else modulusWide) subWord a reducedFlag
  let s6 := arithmeticState fieldTail counterWidth base
    (if reducedFlag then 0 else modulusWide) reduced a reducedFlag
  let s7 := arithmeticState fieldTail counterWidth base modulusWide reduced
    a reducedFlag
  let s8 := arithmeticState fieldTail counterWidth base active reduced
    modulus reducedFlag
  let s9 := arithmeticState fieldTail counterWidth base active
    (reduced - active) modulus reducedFlag
  let s10 := arithmeticState fieldTail counterWidth base active
    (reduced - active) modulus false
  let s11 := arithmeticState fieldTail counterWidth base active reduced
    modulus false
  have hs1 : arithmeticAdderStep fieldTail counterWidth s0 = s1 := by
    simpa [s0, s1, sumWord] using
      arithmeticAdderStep_state fieldTail counterWidth base active target
        modulus false
  have hs2 : sourceSwapStep fieldTail counterWidth s1 = s2 := by
    simpa [s1, s2, active, modulus, hmodulusWide] using
      sourceSwapStep_state fieldTail counterWidth base a modulus sumWord false
  have hs3 : arithmeticAdderReverseStep fieldTail counterWidth s2 = s3 := by
    simpa [s2, s3, subWord] using
      arithmeticAdderReverseStep_state fieldTail counterWidth base modulusWide
        sumWord a false
  have hs4 : copyReductionFlagStep fieldTail counterWidth s3 = s4 := by
    simpa [s3, s4, hsubBit, hunderflow] using
      copyReductionFlagStep_state fieldTail counterWidth base modulusWide
        subWord a false
  have hs5 : clearActiveModulusStep fieldTail counterWidth p s4 = s5 := by
    simpa [s4, s5, modulusWide] using
      clearActiveModulusStep_state fieldTail counterWidth p base subWord a
        reducedFlag
  have hs6 : arithmeticAdderStep fieldTail counterWidth s5 = s6 := by
    simpa [s5, s6, haddBack] using
      arithmeticAdderStep_state fieldTail counterWidth base
        (if reducedFlag then 0 else modulusWide) subWord a reducedFlag
  have hs7 : restoreActiveModulusStep fieldTail counterWidth p s6 = s7 := by
    simpa [s6, s7, modulusWide] using
      restoreActiveModulusStep_state fieldTail counterWidth p base reduced a
        reducedFlag
  have hs8 : sourceSwapStep fieldTail counterWidth s7 = s8 := by
    simpa [s7, s8, active, modulus, hmodulusWide] using
      sourceSwapStep_state fieldTail counterWidth base modulus a reduced
        reducedFlag
  have hs9 : arithmeticAdderReverseStep fieldTail counterWidth s8 = s9 := by
    simpa [s8, s9] using
      arithmeticAdderReverseStep_state fieldTail counterWidth base active
        reduced modulus reducedFlag
  have hs10 : cleanupReductionFlagStep fieldTail counterWidth s9 = s10 := by
    simpa [s9, s10, hcleanupBit] using
      cleanupReductionFlagStep_state fieldTail counterWidth base active
        (reduced - active) modulus reducedFlag
  have hs11 : arithmeticAdderStep fieldTail counterWidth s10 = s11 := by
    simpa [s10, s11] using
      arithmeticAdderStep_state fieldTail counterWidth base active
        (reduced - active) modulus false
  change modularReduceStep fieldTail counterWidth p s0 = _
  rw [modularReduceStep_eq_stages, hs1, hs2, hs3, hs4, hs5, hs6, hs7,
    hs8, hs9, hs10, hs11]
  change arithmeticState fieldTail counterWidth base active reduced modulus false =
    arithmeticState fieldTail counterWidth base active
      (modularSumWord fieldTail p hpPos hp a b) modulus false
  have hreduced : reduced = modularSumWord fieldTail p hpPos hp a b := by
    apply Fin.ext
    change MAU.Addition.VBEArithmetic.reduceOnce p sumWord.val =
      (a.val + b.val) % p
    rw [hsumVal]
    exact MAU.Addition.VBEArithmetic.reduceOnce_eq_mod hpPos (by omega)
  rw [hreduced]

/-- Exact inverse ledger of compact modular addition. -/
def modularSubtractGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  (modularReduceGates fieldTail counterWidth p).reverse

/-- Circuit compiled from the literal reverse modular-add ledger. -/
def modularSubtractProgram (fieldTail counterWidth p : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (modularSubtractGates fieldTail counterWidth p)

/-- Folded action of the exact reverse modular-add ledger. -/
def modularSubtractStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (modularSubtractGates fieldTail counterWidth p)

/-- The reverse modular-add circuit realizes its literal gate-list action. -/
lemma modularSubtract_realizes (fieldTail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (MK.Compact.encoding fieldTail.succ counterWidth)
      (modularSubtractProgram fieldTail counterWidth p) environment
      (modularSubtractStep fieldTail counterWidth p) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (modularSubtractGates fieldTail counterWidth p)

/-- Reversing the general clean modular-add endpoint subtracts the preserved
active residue while restoring the parked modulus and every borrowed work bit.
This image-form theorem avoids introducing any extra subtraction flag. -/
lemma modularSubtractStep_add_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (a b : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (ha : a.val < p) (hb : b.val < p) :
    modularSubtractStep fieldTail counterWidth p
        (arithmeticState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ a)
          (modularSumWord fieldTail p hpPos hp a b) ⟨p, hp⟩ false) =
      arithmeticState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ a)
        (widenFixedWord fieldTail.succ b) ⟨p, hp⟩ false := by
  let original := arithmeticState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ a)
    (widenFixedWord fieldTail.succ b) ⟨p, hp⟩ false
  have hforward := modularReduceStep_add_state fieldTail counterWidth p base
    a b hpPos hp ha hb
  have hinverse := EncodedBit.GateSpec.stepList_reverse_stepList
    (modularReduceGates fieldTail counterWidth p) original
  change modularSubtractStep fieldTail counterWidth p
      (modularReduceStep fieldTail counterWidth p original) = original at hinverse
  rw [hforward] at hinverse
  exact hinverse

/-- On arbitrary canonical inputs, the inverse ledger subtracts the active
source modulo `p` and returns the complete compact arithmetic view clean. -/
lemma modularSubtractStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (source target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hsource : source.val < p) (htarget : target.val < p) :
    modularSubtractStep fieldTail counterWidth p
        (arithmeticState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ source)
          (widenFixedWord fieldTail.succ target) ⟨p, hp⟩ false) =
      arithmeticState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ source)
        (widenFixedWord fieldTail.succ
          (modularDifferenceWord fieldTail p hpPos hp target source))
        ⟨p, hp⟩ false := by
  let difference := modularDifferenceWord fieldTail p hpPos hp target source
  have hdifference : difference.val < p := by
    exact Nat.mod_lt _ hpPos
  have hinverse := modularSubtractStep_add_state fieldTail counterWidth p base
    source difference hpPos hp hsource hdifference
  have hsum := modularSumWord_difference fieldTail p hpPos hp source target
    hsource htarget
  rw [hsum] at hinverse
  simpa only [difference] using hinverse

/-! ## Width-neutral public-target update -/

/-- Arithmetic view used while the public target is borrowed.  The corrected
coefficient remains in `rCoeff`; only `u`/`compare`, `v`/`active`, and the
existing VBE bank are used transiently. -/
def targetUpdateState (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient active borrowedTarget : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (publicTarget : Word fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ counterWidth :=
  arithmeticState fieldTail counterWidth
    { base with
      core := { base.core with rCoeff := coefficient }
      target := publicTarget }
    active borrowedTarget parked flag

private lemma publicTarget_arithmeticTargetLow_ne
    (n counterWidth : Nat) (publicBit targetBit : Fin n) :
    ((targetValueWord n counterWidth).bit publicBit).wire ≠
      ((uValueWord n counterWidth).bit targetBit).wire := by
  simpa [targetValueWord, targetValueBit, uValueWord,
    RegisterBits.uValueBit] using
    Ne.symm (liftCoreBit_targetBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth targetBit)
      (WireAddress.littleEndianWire publicBit))

private lemma arithmeticTargetLow_pairwise_ne
    (n counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((uValueWord n counterWidth).bit left).wire ≠
        ((uValueWord n counterWidth).bit right).wire := by
  intro left right hne
  simpa [uValueWord, RegisterBits.uValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (u_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire left)
        (WireAddress.littleEndianWire right)
        (littleEndianWire_ne hne))

private lemma publicTarget_pairwise_ne
    (n counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((targetValueWord n counterWidth).bit left).wire ≠
        ((targetValueWord n counterWidth).bit right).wire := by
  intro left right hne hw
  apply littleEndianWire_ne hne
  apply Fin.ext
  have hval := congrArg Fin.val hw
  simpa [targetValueWord, targetValueBit, targetBit, rawTargetBit,
    registerTupleEncoding, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel] using hval

/-- Swap the public target with the low word of the borrowed arithmetic
target.  The adjacent comparison bit is not touched. -/
def targetSwapGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (MK.Compact.encoding n counterWidth)) :=
  EncodedBit.Word.swapGates
    (targetValueWord n counterWidth)
    (uValueWord n counterWidth)
    (fun bit => publicTarget_arithmeticTargetLow_ne n counterWidth bit bit)

/-- Folded action of the public/arithmetic target exchange. -/
def targetSwapStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (targetSwapGates n counterWidth)

/-- The target exchange swaps exactly the two low words and preserves the
complete surrounding compact carrier. -/
lemma targetSwapStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient active : Word (fieldTail.succ + 1))
    (borrowed publicTarget parked : Word fieldTail.succ)
    (flag : Bool) :
    targetSwapStep fieldTail.succ counterWidth
        (targetUpdateState fieldTail counterWidth base coefficient active
          (widenFixedWord fieldTail.succ borrowed) parked flag publicTarget) =
      targetUpdateState fieldTail counterWidth base coefficient active
        (widenFixedWord fieldTail.succ publicTarget) parked flag borrowed := by
  let input := targetUpdateState fieldTail counterWidth base coefficient active
    (widenFixedWord fieldTail.succ borrowed) parked flag publicTarget
  let output := targetSwapStep fieldTail.succ counterWidth input
  let expected := targetUpdateState fieldTail counterWidth base coefficient
    active (widenFixedWord fieldTail.succ publicTarget) parked flag borrowed
  have hborrowedHigh : borrowed.val.testBit fieldTail.succ = false :=
    Nat.testBit_lt_two_pow borrowed.isLt
  have hpublicHigh : publicTarget.val.testBit fieldTail.succ = false :=
    Nat.testBit_lt_two_pow publicTarget.isLt
  let eraseCore : MK.Registers fieldTail.succ counterWidth ->
      MK.Registers fieldTail.succ counterWidth :=
    fun core => { core with u := 0 }
  have hcoreFrame : eraseCore output.core = eraseCore input.core := by
    have hpreserve := EncodedBit.Word.swapStep_preserves_projection
      (targetValueWord fieldTail.succ counterWidth)
      (uValueWord fieldTail.succ counterWidth)
      (fun bit => publicTarget_arithmeticTargetLow_ne fieldTail.succ
        counterWidth bit bit)
      (fun current => eraseCore current.core)
      (fun _ current => by
        rcases current with ⟨core, shared, target⟩
        rfl)
      (fun _ current => by
        rcases current with
          ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history,
            activeFlag, counter⟩, shared, target⟩
        rfl) input
    simpa only [output, targetSwapStep, targetSwapGates,
      EncodedBit.Word.swapStep] using hpreserve
  have hshared : output.shared = expected.shared := by
    have hpreserve := EncodedBit.Word.swapStep_preserves_projection
      (targetValueWord fieldTail.succ counterWidth)
      (uValueWord fieldTail.succ counterWidth)
      (fun bit => publicTarget_arithmeticTargetLow_ne fieldTail.succ
        counterWidth bit bit)
      (fun current => current.shared)
      (fun _ _ => rfl) (fun _ _ => rfl) input
    simpa only [output, expected, input, targetUpdateState, arithmeticState,
      targetSwapStep, targetSwapGates, EncodedBit.Word.swapStep] using hpreserve
  have hleft := EncodedBit.Word.swapStep_get_left_word
    (targetValueWord fieldTail.succ counterWidth)
    (uValueWord fieldTail.succ counterWidth)
    (fun bit => publicTarget_arithmeticTargetLow_ne fieldTail.succ
      counterWidth bit bit)
    (publicTarget_pairwise_ne fieldTail.succ counterWidth)
    (arithmeticTargetLow_pairwise_ne fieldTail.succ counterWidth)
    (publicTarget_arithmeticTargetLow_ne fieldTail.succ counterWidth)
    input
  have hright := EncodedBit.Word.swapStep_get_right_word
    (targetValueWord fieldTail.succ counterWidth)
    (uValueWord fieldTail.succ counterWidth)
    (fun bit => publicTarget_arithmeticTargetLow_ne fieldTail.succ
      counterWidth bit bit)
    (publicTarget_pairwise_ne fieldTail.succ counterWidth)
    (arithmeticTargetLow_pairwise_ne fieldTail.succ counterWidth)
    (publicTarget_arithmeticTargetLow_ne fieldTail.succ counterWidth)
    input
  have hu : output.core.u = expected.core.u := by
    apply word_eq_of_testBit_eq
    intro bit
    have hread := congrFun hright bit
    calc
      output.core.u.val.testBit bit.val =
          ((uValueWord fieldTail.succ counterWidth).bit bit).get output := by
        simp
      _ = ((targetValueWord fieldTail.succ counterWidth).bit bit).get input := by
        simpa [output, targetSwapStep, targetSwapGates,
          EncodedBit.Word.swapStep] using hread
      _ = publicTarget.val.testBit bit.val := by
        change (targetValueBit fieldTail.succ counterWidth bit).get input = _
        rw [targetValueBit_get]
        simp [input, targetUpdateState, arithmeticState]
      _ = expected.core.u.val.testBit bit.val := by
        simp [expected, targetUpdateState, arithmeticState]
  have hv : output.core.v = expected.core.v := by
    have h := congrArg (fun core => core.v) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hcompare : output.core.compare = expected.core.compare := by
    have h := congrArg (fun core => core.compare) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState,
      hborrowedHigh, hpublicHigh] using h
  have hsCoeff : output.core.sCoeff = expected.core.sCoeff := by
    have h := congrArg (fun core => core.sCoeff) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hrCoeff : output.core.rCoeff = expected.core.rCoeff := by
    have h := congrArg (fun core => core.rCoeff) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hscratchA : output.core.scratchA = expected.core.scratchA := by
    have h := congrArg (fun core => core.scratchA) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hscratchB : output.core.scratchB = expected.core.scratchB := by
    have h := congrArg (fun core => core.scratchB) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hhistory : output.core.history = expected.core.history := by
    have h := congrArg (fun core => core.history) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hactive : output.core.active = expected.core.active := by
    have h := congrArg (fun core => core.active) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hcounter : output.core.counter = expected.core.counter := by
    have h := congrArg (fun core => core.counter) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hcore : output.core = expected.core := by
    apply (MK.registerTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.registerTupleEquiv, hu, hv, hcompare, hsCoeff, hrCoeff,
      hscratchA, hscratchB, hhistory, hactive, hcounter]
  have htarget : output.target = expected.target := by
    apply word_eq_of_testBit_eq
    intro bit
    have hread := congrFun hleft bit
    calc
      output.target.val.testBit bit.val =
          ((targetValueWord fieldTail.succ counterWidth).bit bit).get output := by
        simp [targetValueWord]
      _ = ((uValueWord fieldTail.succ counterWidth).bit bit).get input := by
        simpa [output, targetSwapStep, targetSwapGates,
          EncodedBit.Word.swapStep] using hread
      _ = borrowed.val.testBit bit.val := by
        simp [input, targetUpdateState, arithmeticState]
      _ = expected.target.val.testBit bit.val := by
        simp [expected, targetUpdateState, arithmeticState]
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ counterWidth).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, htarget]

/-- Low corrected-residue word borrowed as the modular-subtraction source. -/
def correctedValueWord (n counterWidth : Nat) :
    EncodedBit.Word (MK.Compact.encoding n counterWidth) n where
  bit := fun bit => (rCoeffValueWord n counterWidth).bit (Fin.castSucc bit)

private lemma correctedValue_activeSourceLow_ne
    (n counterWidth : Nat) (source target : Fin n) :
    ((correctedValueWord n counterWidth).bit source).wire ≠
      ((vValueWord n counterWidth).bit target).wire := by
  simpa [correctedValueWord, rCoeffValueWord, vValueWord,
    RegisterBits.rCoeffValueBit, RegisterBits.vValueBit] using
    Ne.symm (liftCoreBit_wire_ne n counterWidth
      (RegisterBits.v_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire target)
        (WireAddress.littleEndianWire (Fin.castSucc source))))

private lemma activeSourceLow_pairwise_ne (n counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((vValueWord n counterWidth).bit left).wire ≠
        ((vValueWord n counterWidth).bit right).wire := by
  intro left right hne
  simpa [vValueWord, RegisterBits.vValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (v_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire left)
        (WireAddress.littleEndianWire right)
        (littleEndianWire_ne hne))

/-- CNOT copy of the retained correction residue into the borrowed active
source word. -/
def coefficientLoadGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (MK.Compact.encoding n counterWidth)) :=
  EncodedBit.Word.xorIntoGates
    (correctedValueWord n counterWidth)
    (vValueWord n counterWidth)
    (fun bit => correctedValue_activeSourceLow_ne n counterWidth bit bit)

/-- Folded action of the correction-source CNOT copy. -/
def coefficientLoadStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (coefficientLoadGates n counterWidth)

/-- Loading a canonical corrected coefficient into clean borrowed `v` creates
the widened active source without changing the retained coefficient or any
other compact-carrier field. -/
lemma coefficientLoadStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (source : Word fieldTail.succ)
    (borrowedTarget : Word (fieldTail.succ + 1))
    (parked publicTarget : Word fieldTail.succ) (flag : Bool) :
    coefficientLoadStep fieldTail.succ counterWidth
        (targetUpdateState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ source)
          (widenFixedWord fieldTail.succ 0) borrowedTarget parked flag
          publicTarget) =
      targetUpdateState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ source)
        (widenFixedWord fieldTail.succ source) borrowedTarget parked flag
        publicTarget := by
  let input := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ 0) borrowedTarget parked flag publicTarget
  let output := coefficientLoadStep fieldTail.succ counterWidth input
  let expected := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ source) borrowedTarget parked flag publicTarget
  have hsourceHigh : source.val.testBit fieldTail.succ = false :=
    Nat.testBit_lt_two_pow source.isLt
  let eraseCore : MK.Registers fieldTail.succ counterWidth ->
      MK.Registers fieldTail.succ counterWidth :=
    fun core => { core with v := 0 }
  have hcoreFrame : eraseCore output.core = eraseCore input.core := by
    have hpreserve := EncodedBit.Word.xorIntoStep_preserves_projection
      (correctedValueWord fieldTail.succ counterWidth)
      (vValueWord fieldTail.succ counterWidth)
      (fun bit => correctedValue_activeSourceLow_ne fieldTail.succ
        counterWidth bit bit)
      (fun current => eraseCore current.core)
      (fun _ current => by
        rcases current with
          ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history,
            activeFlag, counter⟩, shared, target⟩
        rfl) input
    simpa only [output, coefficientLoadStep, coefficientLoadGates,
      EncodedBit.Word.xorIntoStep] using hpreserve
  have hshared : output.shared = expected.shared := by
    have hpreserve := EncodedBit.Word.xorIntoStep_preserves_projection
      (correctedValueWord fieldTail.succ counterWidth)
      (vValueWord fieldTail.succ counterWidth)
      (fun bit => correctedValue_activeSourceLow_ne fieldTail.succ
        counterWidth bit bit)
      (fun current => current.shared) (fun _ _ => rfl) input
    simpa only [output, expected, input, targetUpdateState, arithmeticState,
      coefficientLoadStep, coefficientLoadGates,
      EncodedBit.Word.xorIntoStep] using hpreserve
  have hv : output.core.v = expected.core.v := by
    apply word_eq_of_testBit_eq
    intro bit
    have hread := EncodedBit.Word.xorIntoStep_get_target
      (correctedValueWord fieldTail.succ counterWidth)
      (vValueWord fieldTail.succ counterWidth)
      (fun index => correctedValue_activeSourceLow_ne fieldTail.succ
        counterWidth index index)
      bit
      (fun other hne => activeSourceLow_pairwise_ne fieldTail.succ
        counterWidth other bit hne)
      (fun other => Ne.symm
        (correctedValue_activeSourceLow_ne fieldTail.succ counterWidth
          bit other)) input
    calc
      output.core.v.val.testBit bit.val =
          ((vValueWord fieldTail.succ counterWidth).bit bit).get output := by
        simp
      _ = (((vValueWord fieldTail.succ counterWidth).bit bit).get input ^^
          ((correctedValueWord fieldTail.succ counterWidth).bit bit).get
            input) := by
        simpa [output, coefficientLoadStep, coefficientLoadGates,
          EncodedBit.Word.xorIntoStep] using hread
      _ = source.val.testBit bit.val := by
        simp [input, targetUpdateState, arithmeticState, correctedValueWord]
      _ = expected.core.v.val.testBit bit.val := by
        simp [expected, targetUpdateState, arithmeticState]
  have hu : output.core.u = expected.core.u := by
    have h := congrArg (fun core => core.u) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hcompare : output.core.compare = expected.core.compare := by
    have h := congrArg (fun core => core.compare) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hsCoeff : output.core.sCoeff = expected.core.sCoeff := by
    have h := congrArg (fun core => core.sCoeff) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hrCoeff : output.core.rCoeff = expected.core.rCoeff := by
    have h := congrArg (fun core => core.rCoeff) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hscratchA : output.core.scratchA = expected.core.scratchA := by
    have h := congrArg (fun core => core.scratchA) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hscratchB : output.core.scratchB = expected.core.scratchB := by
    have h := congrArg (fun core => core.scratchB) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hhistory : output.core.history = expected.core.history := by
    have h := congrArg (fun core => core.history) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hactive : output.core.active = expected.core.active := by
    have h := congrArg (fun core => core.active) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState,
      hsourceHigh] using h
  have hcounter : output.core.counter = expected.core.counter := by
    have h := congrArg (fun core => core.counter) hcoreFrame
    simpa [eraseCore, input, expected, targetUpdateState, arithmeticState] using h
  have hcore : output.core = expected.core := by
    apply (MK.registerTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.registerTupleEquiv, hu, hv, hcompare, hsCoeff, hrCoeff,
      hscratchA, hscratchB, hhistory, hactive, hcounter]
  have htarget : output.target = expected.target := by
    have hpreserve := EncodedBit.Word.xorIntoStep_preserves_projection
      (correctedValueWord fieldTail.succ counterWidth)
      (vValueWord fieldTail.succ counterWidth)
      (fun bit => correctedValue_activeSourceLow_ne fieldTail.succ
        counterWidth bit bit)
      (fun current => current.target) (fun _ _ => rfl) input
    simpa only [output, expected, input, targetUpdateState, arithmeticState,
      coefficientLoadStep, coefficientLoadGates,
      EncodedBit.Word.xorIntoStep] using hpreserve
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ counterWidth).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, htarget]

/-- Exact inverse of the correction-source CNOT copy. -/
def coefficientUnloadStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (coefficientLoadGates n counterWidth).reverse

/-- Exact inverse of the public/arithmetic target exchange. -/
def targetSwapReverseStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (targetSwapGates n counterWidth).reverse

/-- Native target-update ledger: borrow the public target, copy the retained
correction into the active-source word, run the already-certified modular
adder backwards, and uncompute both transfers. -/
def targetUpdateGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  targetSwapGates fieldTail.succ counterWidth ++
    coefficientLoadGates fieldTail.succ counterWidth ++
    modularSubtractGates fieldTail counterWidth p ++
    (coefficientLoadGates fieldTail.succ counterWidth).reverse ++
    (targetSwapGates fieldTail.succ counterWidth).reverse

/-- Circuit compiled from the literal compact target-update ledger. -/
def targetUpdateProgram (fieldTail counterWidth p : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (targetUpdateGates fieldTail counterWidth p)

/-- Folded action of the exact compact target-update ledger. -/
def targetUpdateStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (targetUpdateGates fieldTail counterWidth p)

/-- Folded action of the exact inverse target-update ledger. -/
def targetUpdateReverseStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (targetUpdateGates fieldTail counterWidth p).reverse

/-- The flattened target-update ledger executes its five named stages in
physical order. -/
lemma targetUpdateStep_eq_stages (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    targetUpdateStep fieldTail counterWidth p x =
      targetSwapReverseStep fieldTail.succ counterWidth
        (coefficientUnloadStep fieldTail.succ counterWidth
          (modularSubtractStep fieldTail counterWidth p
            (coefficientLoadStep fieldTail.succ counterWidth
              (targetSwapStep fieldTail.succ counterWidth x)))) := by
  simp only [targetUpdateStep, targetUpdateGates, targetSwapStep,
    coefficientLoadStep, modularSubtractStep, coefficientUnloadStep,
    targetSwapReverseStep, EncodedBit.GateSpec.stepList_append]

/-- The native target-update circuit realizes its literal gate-list action. -/
lemma targetUpdate_realizes (fieldTail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (MK.Compact.encoding fieldTail.succ counterWidth)
      (targetUpdateProgram fieldTail counterWidth p) environment
      (targetUpdateStep fieldTail counterWidth p) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (targetUpdateGates fieldTail counterWidth p)

/-- Target update subtracts the retained corrected residue modulo `p`, which
is exactly addition of the source-required signed correction.  The retained
coefficient, parked modulus, public/core carrier, and sole VBE bank all return
to their clean boundary values. -/
lemma targetUpdateStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (source target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hsource : source.val < p) (htarget : target.val < p) :
    targetUpdateStep fieldTail counterWidth p
        (targetUpdateState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ source)
          (widenFixedWord fieldTail.succ 0)
          (widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false target) =
      targetUpdateState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ source)
        (widenFixedWord fieldTail.succ 0)
        (widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
        (modularDifferenceWord fieldTail p hpPos hp target source) := by
  let zero : Word fieldTail.succ := 0
  let modulus : Word fieldTail.succ := ⟨p, hp⟩
  let difference := modularDifferenceWord fieldTail p hpPos hp target source
  let s0 := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ zero)
    (widenFixedWord fieldTail.succ zero) modulus false target
  let s1 := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ zero)
    (widenFixedWord fieldTail.succ target) modulus false zero
  let s2 := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ target) modulus false zero
  let s3 := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ difference) modulus false zero
  let s4 := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ zero)
    (widenFixedWord fieldTail.succ difference) modulus false zero
  let s5 := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ zero)
    (widenFixedWord fieldTail.succ zero) modulus false difference
  have hswapInitial : targetSwapStep fieldTail.succ counterWidth s0 = s1 := by
    simpa [s0, s1, zero, modulus] using
      targetSwapStep_state fieldTail counterWidth base
        (widenFixedWord fieldTail.succ source)
        (widenFixedWord fieldTail.succ zero) zero target modulus false
  have hload : coefficientLoadStep fieldTail.succ counterWidth s1 = s2 := by
    simpa [s1, s2, zero, modulus] using
      coefficientLoadStep_state fieldTail counterWidth base source
        (widenFixedWord fieldTail.succ target) modulus zero false
  let workBase : MK.Compact.Registers fieldTail.succ counterWidth :=
    { base with
      core := { base.core with
        rCoeff := widenFixedWord fieldTail.succ source }
      target := zero }
  have hsubtract : modularSubtractStep fieldTail counterWidth p s2 = s3 := by
    have h := modularSubtractStep_state fieldTail counterWidth p workBase
      source target hpPos hp hsource htarget
    simpa [s2, s3, workBase, difference, zero, modulus,
      targetUpdateState] using h
  have hloadFinal : coefficientLoadStep fieldTail.succ counterWidth s4 = s3 := by
    simpa [s4, s3, zero, modulus, difference] using
      coefficientLoadStep_state fieldTail counterWidth base source
        (widenFixedWord fieldTail.succ difference) modulus zero false
  have hunload : coefficientUnloadStep fieldTail.succ counterWidth s3 = s4 := by
    have hinverse := EncodedBit.GateSpec.stepList_reverse_stepList
      (coefficientLoadGates fieldTail.succ counterWidth) s4
    change coefficientUnloadStep fieldTail.succ counterWidth
      (coefficientLoadStep fieldTail.succ counterWidth s4) = s4 at hinverse
    rw [hloadFinal] at hinverse
    exact hinverse
  have hswapFinal : targetSwapStep fieldTail.succ counterWidth s5 = s4 := by
    simpa [s5, s4, zero, modulus, difference] using
      targetSwapStep_state fieldTail counterWidth base
        (widenFixedWord fieldTail.succ source)
        (widenFixedWord fieldTail.succ zero) zero difference modulus false
  have hswapReverse :
      targetSwapReverseStep fieldTail.succ counterWidth s4 = s5 := by
    have hinverse := EncodedBit.GateSpec.stepList_reverse_stepList
      (targetSwapGates fieldTail.succ counterWidth) s5
    change targetSwapReverseStep fieldTail.succ counterWidth
      (targetSwapStep fieldTail.succ counterWidth s5) = s5 at hinverse
    rw [hswapFinal] at hinverse
    exact hinverse
  change targetUpdateStep fieldTail counterWidth p s0 = s5
  rw [targetUpdateStep_eq_stages, hswapInitial, hload, hsubtract, hunload,
    hswapReverse]

/-- Reversing target update adds the retained correction residue modulo `p`.
The complete compact arithmetic state, including its borrowed VBE bank, is
restored around the updated public target. -/
lemma targetUpdateReverseStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (source target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hsource : source.val < p) (htarget : target.val < p) :
    targetUpdateReverseStep fieldTail counterWidth p
        (targetUpdateState fieldTail counterWidth base
          (widenFixedWord fieldTail.succ source)
          (widenFixedWord fieldTail.succ 0)
          (widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false target) =
      targetUpdateState fieldTail counterWidth base
        (widenFixedWord fieldTail.succ source)
        (widenFixedWord fieldTail.succ 0)
        (widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false
        (modularSumFixedWord fieldTail p hpPos hp target source) := by
  let sum := modularSumFixedWord fieldTail p hpPos hp target source
  let input := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ 0)
    (widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false target
  let output := targetUpdateState fieldTail counterWidth base
    (widenFixedWord fieldTail.succ source)
    (widenFixedWord fieldTail.succ 0)
    (widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false sum
  have hsum : sum.val < p := by
    exact Nat.mod_lt _ hpPos
  have hforward :
      targetUpdateStep fieldTail counterWidth p output = input := by
    have h := targetUpdateStep_state fieldTail counterWidth p base source sum
      hpPos hp hsource hsum
    rw [modularDifferenceWord_sum fieldTail p hpPos hp target source
      htarget hsource] at h
    simpa only [output, input, sum] using h
  have hinverse := EncodedBit.GateSpec.stepList_reverse_stepList
    (targetUpdateGates fieldTail counterWidth p) output
  change targetUpdateReverseStep fieldTail counterWidth p
      (targetUpdateStep fieldTail counterWidth p output) = output at hinverse
  rw [hforward] at hinverse
  simpa only [input, output, sum] using hinverse

private lemma rCoeffValueWord_pairwise_ne_for_doubling
    (n counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((rCoeffValueWord n counterWidth).bit left).wire ≠
        ((rCoeffValueWord n counterWidth).bit right).wire := by
  intro left right hne
  simpa [rCoeffValueWord, RegisterBits.rCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (rCoeff_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire left)
        (WireAddress.littleEndianWire right)
        (littleEndianWire_ne hne))

private lemma rCoeff_target_ne
    (fieldTail counterWidth : Nat)
    (source target : Fin (fieldTail.succ + 1)) :
    ((rCoeffValueWord fieldTail.succ counterWidth).bit source).wire ≠
      ((arithmeticTargetWord fieldTail counterWidth).bit target).wire := by
  refine Fin.lastCases ?_ ?_ target
  · simpa [rCoeffValueWord, arithmeticTargetWord, compareBit,
      RegisterBits.rCoeffValueBit] using
      Ne.symm (liftCoreBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.compare_rCoeff_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire source)))
  · intro low
    simpa [rCoeffValueWord, arithmeticTargetWord, uValueWord,
      RegisterBits.rCoeffValueBit, RegisterBits.uValueBit] using
      Ne.symm (liftCoreBit_wire_ne fieldTail.succ counterWidth
        (RegisterBits.u_rCoeff_wire_ne fieldTail.succ counterWidth
          (WireAddress.littleEndianWire low)
          (WireAddress.littleEndianWire source)))

/-- Full word swap moving `r` into and out of the borrowed arithmetic target. -/
def doublingSwapGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.Word.swapGates
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)

/-- High-to-low adjacent swap sweep implementing a zero-filled left shift. -/
def doublingShiftGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.Word.adjacentShiftRightGates
    (arithmeticTargetWord fieldTail counterWidth)
    (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)

/-- Least-significant coefficient bit used to erase the VBE reduction flag. -/
def coefficientLowBit (fieldTail : Nat) : Fin fieldTail.succ :=
  (0 : Fin fieldTail.succ)

private lemma rCoeffLow_reductionFlag_ne
    (fieldTail counterWidth : Nat) :
    ((rCoeffValueWord fieldTail.succ counterWidth).bit
        (Fin.castSucc (coefficientLowBit fieldTail))).wire ≠
      (scratchABit fieldTail.succ counterWidth).wire := by
  simpa [rCoeffValueWord, scratchABit, RegisterBits.rCoeffValueBit] using
    liftCoreBit_wire_ne fieldTail.succ counterWidth
      (RegisterBits.rCoeff_scratchA_wire_ne fieldTail.succ counterWidth
        (WireAddress.littleEndianWire
          (Fin.castSucc (coefficientLowBit fieldTail))))

/-- The parity of an odd-modulus reduction equals the retained reduction flag,
so one final CNOT restores the scratch bit. -/
def doublingCleanupGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  [ .cnot
      ((rCoeffValueWord fieldTail.succ counterWidth).bit
        (Fin.castSucc (coefficientLowBit fieldTail)))
      (scratchABit fieldTail.succ counterWidth)
      (rCoeffLow_reductionFlag_ne fieldTail counterWidth) ]

/-- Literal in-place modular doubling ledger on the compact carrier. -/
def doublingGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  doublingSwapGates fieldTail counterWidth ++
    doublingShiftGates fieldTail counterWidth ++
    modularReduceGates fieldTail counterWidth p ++
    doublingSwapGates fieldTail counterWidth ++
    doublingCleanupGates fieldTail counterWidth

/-- Folded exchange of the coefficient residue and borrowed arithmetic
target. -/
def doublingSwapStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (doublingSwapGates fieldTail counterWidth)

/-- Folded zero-filled left shift of the borrowed widened target. -/
def doublingShiftStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (doublingShiftGates fieldTail counterWidth)

/-- Folded final parity-to-reduction-flag cleanup. -/
def doublingCleanupStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (doublingCleanupGates fieldTail counterWidth)

/-- Actual compact modular-doubling circuit compiled from its native gate
ledger. -/
def doublingProgram (fieldTail counterWidth p : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (doublingGates fieldTail counterWidth p)

/-- Folded semantic action of the literal compact modular-doubling ledger. -/
def doublingStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (doublingGates fieldTail counterWidth p)

/-- The flattened in-place doubling ledger executes swap, shift, reduction,
swap, and parity cleanup in source order. -/
lemma doublingStep_eq_stages (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    doublingStep fieldTail counterWidth p x =
      doublingCleanupStep fieldTail counterWidth
        (doublingSwapStep fieldTail counterWidth
          (modularReduceStep fieldTail counterWidth p
            (doublingShiftStep fieldTail counterWidth
              (doublingSwapStep fieldTail counterWidth x)))) := by
  simp only [doublingStep, doublingGates, doublingCleanupStep,
    doublingSwapStep, modularReduceStep, doublingShiftStep,
    EncodedBit.GateSpec.stepList_append]

/-- Canonical arithmetic view with an explicit live `r` coefficient.  This is
the state boundary used by the in-place doubling proof. -/
def doublingState (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    MK.Compact.Registers fieldTail.succ counterWidth :=
  arithmeticState fieldTail counterWidth
    { base with core := { base.core with rCoeff := coefficient } }
    active target parked flag

/-- The canonical widened representative of `2r mod p`. -/
def doublingResidueWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (coefficient : Word (fieldTail.succ + 1)) :
    Word (fieldTail.succ + 1) :=
  ⟨(2 * coefficient.val) % p, by
    have hmod := Nat.mod_lt (2 * coefficient.val) hpPos
    have hpow : 2 ^ fieldTail.succ < 2 ^ (fieldTail.succ + 1) :=
      Nat.pow_lt_pow_right (by decide) fieldTail.succ.lt_succ_self
    exact hmod.trans (hp.trans hpow)⟩

@[simp] lemma doublingResidueWord_val (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (coefficient : Word (fieldTail.succ + 1)) :
    (doublingResidueWord fieldTail p hpPos hp coefficient).val =
      (2 * coefficient.val) % p :=
  rfl

/-- The doubling exchange swaps the complete coefficient and borrowed target
words while preserving every other compact-carrier field. -/
lemma doublingSwapStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool) :
    doublingSwapStep fieldTail counterWidth
        (doublingState fieldTail counterWidth base coefficient active target
          parked flag) =
      doublingState fieldTail counterWidth base target active coefficient
        parked flag := by
  let input := doublingState fieldTail counterWidth base coefficient active
    target parked flag
  let output := doublingSwapStep fieldTail counterWidth input
  let expected := doublingState fieldTail counterWidth base target active
    coefficient parked flag
  let eraseCore : MK.Registers fieldTail.succ counterWidth ->
      MK.Registers fieldTail.succ counterWidth :=
    fun core => { core with rCoeff := 0, u := 0, compare := false }
  have hcoreFrame : eraseCore output.core = eraseCore input.core := by
    have hpreserve := EncodedBit.Word.swapStep_preserves_projection
      (rCoeffValueWord fieldTail.succ counterWidth)
      (arithmeticTargetWord fieldTail counterWidth)
      (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
      (fun current => eraseCore current.core)
      (fun _ _ => rfl)
      (fun bit current => by
        refine Fin.lastCases ?_ (fun low => ?_) bit
        · rw [arithmeticTargetWord_bit_last]
          rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
            scratchB, history, active, counter⟩, shared, publicTarget⟩
          rfl
        · rw [arithmeticTargetWord_bit_castSucc]
          rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
            scratchB, history, active, counter⟩, shared, publicTarget⟩
          rfl) input
    simpa only [output, doublingSwapStep, doublingSwapGates,
      EncodedBit.Word.swapStep] using hpreserve
  have hleft := EncodedBit.Word.swapStep_get_left_word
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
    (rCoeffValueWord_pairwise_ne_for_doubling fieldTail.succ counterWidth)
    (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)
    (rCoeff_target_ne fieldTail counterWidth) input
  have hright := EncodedBit.Word.swapStep_get_right_word
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
    (rCoeffValueWord_pairwise_ne_for_doubling fieldTail.succ counterWidth)
    (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)
    (rCoeff_target_ne fieldTail counterWidth) input
  have hrCoeff : output.core.rCoeff = expected.core.rCoeff := by
    apply word_eq_of_testBit_eq
    intro bit
    have hread := congrFun hleft bit
    calc
      output.core.rCoeff.val.testBit bit.val =
          ((rCoeffValueWord fieldTail.succ counterWidth).bit bit).get
            output := by
        simp [rCoeffValueWord]
      _ = ((arithmeticTargetWord fieldTail counterWidth).bit bit).get
            input := by
        simpa [output, doublingSwapStep, doublingSwapGates,
          EncodedBit.Word.swapStep] using hread
      _ = target.val.testBit bit.val := by
        exact arithmeticState_target_get fieldTail counterWidth
          { base with core := { base.core with rCoeff := coefficient } }
          active target parked flag bit
      _ = expected.core.rCoeff.val.testBit bit.val := by
        simp [expected, doublingState, arithmeticState]
  have htargetRead : forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).get output =
        ((arithmeticTargetWord fieldTail counterWidth).bit bit).get expected := by
    intro bit
    have hread := congrFun hright bit
    calc
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).get output =
          ((rCoeffValueWord fieldTail.succ counterWidth).bit bit).get input := by
        simpa [output, doublingSwapStep, doublingSwapGates,
          EncodedBit.Word.swapStep] using hread
      _ = coefficient.val.testBit bit.val := by
        simp [input, doublingState, arithmeticState, rCoeffValueWord]
      _ = ((arithmeticTargetWord fieldTail counterWidth).bit bit).get
            expected := by
        symm
        exact arithmeticState_target_get fieldTail counterWidth
          { base with core := { base.core with rCoeff := target } }
          active coefficient parked flag bit
  have hu : output.core.u = expected.core.u := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [arithmeticTargetWord_bit_castSucc, uValueWord_get] using
      htargetRead (Fin.castSucc bit)
  have hcompare : output.core.compare = expected.core.compare := by
    simpa only [arithmeticTargetWord_bit_last, compareBit_get] using
      htargetRead (Fin.last fieldTail.succ)
  have hv : output.core.v = expected.core.v := by
    have h := congrArg (fun core => core.v) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hsCoeff : output.core.sCoeff = expected.core.sCoeff := by
    have h := congrArg (fun core => core.sCoeff) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hscratchA : output.core.scratchA = expected.core.scratchA := by
    have h := congrArg (fun core => core.scratchA) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hscratchB : output.core.scratchB = expected.core.scratchB := by
    have h := congrArg (fun core => core.scratchB) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hhistory : output.core.history = expected.core.history := by
    have h := congrArg (fun core => core.history) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hactive : output.core.active = expected.core.active := by
    have h := congrArg (fun core => core.active) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hcounter : output.core.counter = expected.core.counter := by
    have h := congrArg (fun core => core.counter) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hcore : output.core = expected.core := by
    apply (MK.registerTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.registerTupleEquiv, hu, hv, hcompare, hsCoeff, hrCoeff,
      hscratchA, hscratchB, hhistory, hactive, hcounter]
  have houter : (output.shared, output.target) =
      (input.shared, input.target) := by
    have hpreserve := EncodedBit.Word.swapStep_preserves_projection
      (rCoeffValueWord fieldTail.succ counterWidth)
      (arithmeticTargetWord fieldTail counterWidth)
      (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
      (fun current => (current.shared, current.target))
      (fun _ _ => rfl)
      (fun bit current => by
        refine Fin.lastCases ?_ (fun low => ?_) bit
        · rw [arithmeticTargetWord_bit_last]
          rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
            scratchB, history, active, counter⟩, shared, publicTarget⟩
          rfl
        · rw [arithmeticTargetWord_bit_castSucc]
          rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
            scratchB, history, active, counter⟩, shared, publicTarget⟩
          rfl) input
    simpa only [output, doublingSwapStep, doublingSwapGates,
      EncodedBit.Word.swapStep] using hpreserve
  have hshared : output.shared = expected.shared := by
    have h := congrArg Prod.fst houter
    simpa [input, expected, doublingState, arithmeticState] using h
  have htarget : output.target = expected.target := by
    have h := congrArg Prod.snd houter
    simpa [input, expected, doublingState, arithmeticState] using h
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ counterWidth).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, htarget]

/-- When the widened target's top bit is zero, the adjacent cyclic sweep is
exactly a zero-filled fixed-width doubling and preserves the carrier frame. -/
lemma doublingShiftStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (hmsb : target.val.testBit (Fin.last fieldTail.succ).val = false) :
    doublingShiftStep fieldTail counterWidth
        (doublingState fieldTail counterWidth base coefficient active target
          parked flag) =
      doublingState fieldTail counterWidth base coefficient active
        (wordDouble (fieldTail.succ + 1) target) parked flag := by
  let input := doublingState fieldTail counterWidth base coefficient active
    target parked flag
  let output := doublingShiftStep fieldTail counterWidth input
  let expected := doublingState fieldTail counterWidth base coefficient active
    (wordDouble (fieldTail.succ + 1) target) parked flag
  let eraseCore : MK.Registers fieldTail.succ counterWidth ->
      MK.Registers fieldTail.succ counterWidth :=
    fun core => { core with u := 0, compare := false }
  have hpreserve {Projection : Type}
      (project : MK.Compact.Registers fieldTail.succ counterWidth -> Projection)
      (htarget : forall bit current,
        project (((arithmeticTargetWord fieldTail counterWidth).bit bit).flip
          current) = project current) :
      project output = project input := by
    unfold output doublingShiftStep doublingShiftGates
      EncodedBit.Word.adjacentShiftRightGates
    apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    intro gate hgate
    have hleft : gate ∈ EncodedBit.Word.adjacentShiftLeftGates
        (arithmeticTargetWord fieldTail counterWidth)
        (arithmeticTargetWord_pairwise_ne fieldTail counterWidth) := by
      simpa using List.mem_reverse.mp hgate
    rw [EncodedBit.Word.adjacentShiftLeftGates] at hleft
    rcases List.mem_flatMap.mp hleft with ⟨bit, _hbit, hgate⟩
    simp only [EncodedBit.Word.adjacentSwapGates, EncodedBit.swapGates,
      List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with hgate | hgate | hgate <;> subst gate
    · exact htarget _
    · exact htarget _
    · exact htarget _
  have htargetRead : forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).get output =
        ((arithmeticTargetWord fieldTail counterWidth).bit bit).get expected := by
    intro bit
    refine Fin.cases ?_ (fun low => ?_) bit
    · have hread := EncodedBit.Word.adjacentShiftRightStep_get_zero
        (arithmeticTargetWord fieldTail counterWidth)
        (arithmeticTargetWord_pairwise_ne fieldTail counterWidth) input
      calc
        ((arithmeticTargetWord fieldTail counterWidth).bit 0).get output =
            ((arithmeticTargetWord fieldTail counterWidth).bit
              (Fin.last fieldTail.succ)).get input := by
          simpa [output, doublingShiftStep, doublingShiftGates,
            EncodedBit.Word.adjacentShiftRightStep] using hread
        _ = target.val.testBit (Fin.last fieldTail.succ).val := by
          exact arithmeticState_target_get fieldTail counterWidth
            { base with core := { base.core with rCoeff := coefficient } }
            active target parked flag (Fin.last fieldTail.succ)
        _ = false := hmsb
        _ = (wordDouble (fieldTail.succ + 1) target).val.testBit 0 := by
          change false = (wordDouble (fieldTail.succ + 1) target).val.testBit
            (0 : Fin (fieldTail.succ + 1)).val
          rw [wordDouble_testBit]
          rfl
        _ = ((arithmeticTargetWord fieldTail counterWidth).bit 0).get
              expected := by
          convert
            (arithmeticState_target_get fieldTail counterWidth
              { base with core := { base.core with rCoeff := coefficient } }
              active (wordDouble (fieldTail.succ + 1) target) parked flag
              (0 : Fin (fieldTail.succ + 1))).symm using 1 <;>
            simp [expected, doublingState]
    · have hread := EncodedBit.Word.adjacentShiftRightStep_get_succ
        (arithmeticTargetWord fieldTail counterWidth)
        (arithmeticTargetWord_pairwise_ne fieldTail counterWidth) low input
      calc
        ((arithmeticTargetWord fieldTail counterWidth).bit low.succ).get
            output =
            ((arithmeticTargetWord fieldTail counterWidth).bit
              low.castSucc).get input := by
          simpa [output, doublingShiftStep, doublingShiftGates,
            EncodedBit.Word.adjacentShiftRightStep] using hread
        _ = target.val.testBit low.val := by
          exact arithmeticState_target_get fieldTail counterWidth
            { base with core := { base.core with rCoeff := coefficient } }
            active target parked flag low.castSucc
        _ = (wordDouble (fieldTail.succ + 1) target).val.testBit
              low.succ.val := by
          rw [wordDouble_testBit]
          simp
        _ = ((arithmeticTargetWord fieldTail counterWidth).bit low.succ).get
              expected := by
          simpa only [expected, doublingState] using
            (arithmeticState_target_get fieldTail counterWidth
              { base with core := { base.core with rCoeff := coefficient } }
              active (wordDouble (fieldTail.succ + 1) target) parked flag
              low.succ).symm
  have hcoreFrame : eraseCore output.core = eraseCore input.core := by
    exact hpreserve (fun current => eraseCore current.core) (fun bit current => by
      refine Fin.lastCases ?_ (fun low => ?_) bit
      · rw [arithmeticTargetWord_bit_last]
        rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
          scratchB, history, active, counter⟩, shared, publicTarget⟩
        rfl
      · rw [arithmeticTargetWord_bit_castSucc]
        rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
          scratchB, history, active, counter⟩, shared, publicTarget⟩
        rfl)
  have hu : output.core.u = expected.core.u := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [arithmeticTargetWord_bit_castSucc, uValueWord_get] using
      htargetRead (Fin.castSucc bit)
  have hcompare : output.core.compare = expected.core.compare := by
    simpa only [arithmeticTargetWord_bit_last, compareBit_get] using
      htargetRead (Fin.last fieldTail.succ)
  have hv : output.core.v = expected.core.v := by
    have h := congrArg (fun core => core.v) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hsCoeff : output.core.sCoeff = expected.core.sCoeff := by
    have h := congrArg (fun core => core.sCoeff) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hrCoeff : output.core.rCoeff = expected.core.rCoeff := by
    have h := congrArg (fun core => core.rCoeff) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hscratchA : output.core.scratchA = expected.core.scratchA := by
    have h := congrArg (fun core => core.scratchA) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hscratchB : output.core.scratchB = expected.core.scratchB := by
    have h := congrArg (fun core => core.scratchB) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hhistory : output.core.history = expected.core.history := by
    have h := congrArg (fun core => core.history) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hactive : output.core.active = expected.core.active := by
    have h := congrArg (fun core => core.active) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hcounter : output.core.counter = expected.core.counter := by
    have h := congrArg (fun core => core.counter) hcoreFrame
    simpa [eraseCore, input, expected, doublingState, arithmeticState] using h
  have hcore : output.core = expected.core := by
    apply (MK.registerTupleEquiv fieldTail.succ counterWidth).injective
    simp [MK.registerTupleEquiv, hu, hv, hcompare, hsCoeff, hrCoeff,
      hscratchA, hscratchB, hhistory, hactive, hcounter]
  have houter : (output.shared, output.target) =
      (input.shared, input.target) := by
    exact hpreserve (fun current => (current.shared, current.target))
      (fun bit current => by
        refine Fin.lastCases ?_ (fun low => ?_) bit
        · rw [arithmeticTargetWord_bit_last]
          rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
            scratchB, history, active, counter⟩, shared, publicTarget⟩
          rfl
        · rw [arithmeticTargetWord_bit_castSucc]
          rcases current with ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA,
            scratchB, history, active, counter⟩, shared, publicTarget⟩
          rfl)
  have hshared : output.shared = expected.shared := by
    have h := congrArg Prod.fst houter
    simpa [input, expected, doublingState, arithmeticState] using h
  have htarget : output.target = expected.target := by
    have h := congrArg Prod.snd houter
    simpa [input, expected, doublingState, arithmeticState] using h
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ counterWidth).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, htarget]

/-- For an odd modulus and a reduced input coefficient, the low bit of the
reduced double records exactly whether the conditional subtraction fired. -/
private lemma doublingResidueWord_lowBit
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (coefficient : Word (fieldTail.succ + 1))
    (hcoefficient : coefficient.val < p) :
    (doublingResidueWord fieldTail p hpPos hp coefficient).val.testBit 0 =
      decide (p ≤ 2 * coefficient.val) := by
  simp only [doublingResidueWord_val]
  have hraw : 2 * coefficient.val < 2 * p := by omega
  by_cases hreduce : p ≤ 2 * coefficient.val
  · have hsub : 2 * coefficient.val - p < p := by omega
    rw [Nat.mod_eq_sub_mod hreduce, Nat.mod_eq_of_lt hsub]
    rcases hpOdd with ⟨k, hk⟩
    have hform :
        2 * coefficient.val - p =
          2 * (coefficient.val - k - 1) + 1 := by
      omega
    simp [hreduce, hform, Nat.testBit_zero]
  · have hlt : 2 * coefficient.val < p := Nat.lt_of_not_ge hreduce
    rw [Nat.mod_eq_of_lt hlt]
    simp [hreduce, Nat.testBit_zero]

/-- The final coefficient-parity CNOT erases the retained reduction flag and
preserves the complete compact carrier. -/
lemma doublingCleanupStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (hbit : coefficient.val.testBit 0 = flag) :
    doublingCleanupStep fieldTail counterWidth
        (doublingState fieldTail counterWidth base coefficient active target
          parked flag) =
      doublingState fieldTail counterWidth base coefficient active target
        parked false := by
  let input := doublingState fieldTail counterWidth base coefficient active
    target parked flag
  have hcontrol :
      ((rCoeffValueWord fieldTail.succ counterWidth).bit
        (Fin.castSucc (coefficientLowBit fieldTail))).get input = flag := by
    simpa [input, doublingState, arithmeticState, rCoeffValueWord,
      coefficientLowBit] using hbit
  change EncodedBit.cnotStep
      ((rCoeffValueWord fieldTail.succ counterWidth).bit
        (Fin.castSucc (coefficientLowBit fieldTail)))
      (scratchABit fieldTail.succ counterWidth) input = _
  unfold EncodedBit.cnotStep
  rw [hcontrol]
  cases flag <;> rfl

/-- The literal compact gate ledger performs in-place modular doubling on a
reduced coefficient, restores the borrowed target and VBE bank to zero, and
cleans the retained reduction flag. -/
lemma doublingStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) :
    doublingStep fieldTail counterWidth p
        (doublingState fieldTail counterWidth base coefficient
          (widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false) =
      doublingState fieldTail counterWidth base
        (doublingResidueWord fieldTail p hpPos hp coefficient)
        (widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false := by
  let zeroWide : Word (fieldTail.succ + 1) :=
    widenFixedWord fieldTail.succ 0
  let modulus : Word fieldTail.succ := ⟨p, hp⟩
  let raw : Word (fieldTail.succ + 1) :=
    wordDouble (fieldTail.succ + 1) coefficient
  let reduced : Word (fieldTail.succ + 1) :=
    doublingResidueWord fieldTail p hpPos hp coefficient
  let reducedFlag : Bool := decide (p ≤ raw.val)
  let s0 := doublingState fieldTail counterWidth base coefficient zeroWide
    0 modulus false
  let s1 := doublingState fieldTail counterWidth base 0 zeroWide coefficient
    modulus false
  let s2 := doublingState fieldTail counterWidth base 0 zeroWide raw
    modulus false
  let s3 := doublingState fieldTail counterWidth base 0 zeroWide reduced
    modulus reducedFlag
  let s4 := doublingState fieldTail counterWidth base reduced zeroWide 0
    modulus reducedFlag
  let s5 := doublingState fieldTail counterWidth base reduced zeroWide 0
    modulus false
  have hmsb : coefficient.val.testBit (Fin.last fieldTail.succ).val = false := by
    simpa using Nat.testBit_lt_two_pow (hcoefficient.trans hp)
  have hdouble : 2 * coefficient.val < 2 ^ (fieldTail.succ + 1) := by
    calc
      2 * coefficient.val < 2 * 2 ^ fieldTail.succ := by omega
      _ = 2 ^ (fieldTail.succ + 1) := by simp [pow_succ, Nat.mul_comm]
  have hrawVal : raw.val = 2 * coefficient.val := by
    simpa only [raw] using
      wordDouble_val_of_no_overflow (fieldTail.succ + 1) coefficient hdouble
  have hraw : raw.val < 2 * p := by
    rw [hrawVal]
    omega
  have hreduced :
      reducedWord fieldTail p hpPos hp raw hraw = reduced := by
    apply Fin.ext
    change MAU.Addition.VBEArithmetic.reduceOnce p raw.val =
      (2 * coefficient.val) % p
    rw [MAU.Addition.VBEArithmetic.reduceOnce_eq_mod hpPos hraw, hrawVal]
  have hbit : reduced.val.testBit 0 = reducedFlag := by
    rw [show reducedFlag = decide (p ≤ 2 * coefficient.val) by
      simp [reducedFlag, hrawVal]]
    exact doublingResidueWord_lowBit fieldTail p hpPos hp hpOdd coefficient
      hcoefficient
  have hs1 : doublingSwapStep fieldTail counterWidth s0 = s1 := by
    simpa [s0, s1, zeroWide, modulus] using
      doublingSwapStep_state fieldTail counterWidth base coefficient zeroWide
        0 modulus false
  have hs2 : doublingShiftStep fieldTail counterWidth s1 = s2 := by
    simpa [s1, s2, raw] using
      doublingShiftStep_state fieldTail counterWidth base 0 zeroWide
        coefficient modulus false hmsb
  have hs3 : modularReduceStep fieldTail counterWidth p s2 = s3 := by
    simpa [s2, s3, doublingState, hreduced, reducedFlag] using
      modularReduceStep_state fieldTail counterWidth p
        { base with core :=
            { base.core with rCoeff := (0 : Word (fieldTail.succ + 1)) } }
        raw hpPos hp hraw
  have hs4 : doublingSwapStep fieldTail counterWidth s3 = s4 := by
    simpa [s3, s4] using
      doublingSwapStep_state fieldTail counterWidth base 0 zeroWide reduced
        modulus reducedFlag
  have hs5 : doublingCleanupStep fieldTail counterWidth s4 = s5 := by
    simpa [s4, s5] using
      doublingCleanupStep_state fieldTail counterWidth base reduced zeroWide 0
        modulus reducedFlag hbit
  change doublingStep fieldTail counterWidth p s0 = s5
  rw [doublingStep_eq_stages, hs1, hs2, hs3, hs4, hs5]

/-- The concrete compact modular-doubling circuit realizes its gate-list
action. -/
lemma doubling_realizes (fieldTail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (MK.Compact.encoding fieldTail.succ counterWidth)
      (doublingProgram fieldTail counterWidth p) environment
      (doublingStep fieldTail counterWidth p) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (doublingGates fieldTail counterWidth p)

/-! ## Reversible initial coefficient reduction -/

/-- Three-CNOT transfer of the retained reduction predicate from `scratchA`
to the otherwise clean `scratchB`. -/
def reductionFlagParkGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (MK.Compact.encoding n counterWidth)) :=
  EncodedBit.swapGates
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (scratchABit_scratchBBit_wire_ne n counterWidth)

/-- Folded action of the reduction-predicate transfer. -/
def reductionFlagParkStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (reductionFlagParkGates n counterWidth)

/-- On a clean `scratchB`, parking moves the reduction predicate out of the
VBE reduction flag and leaves all surrounding fields unchanged. -/
lemma reductionFlagParkStep_state
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient active target : Word (fieldTail.succ + 1))
    (parked : Word fieldTail.succ) (flag : Bool)
    (hclean : base.core.scratchB = false) :
    reductionFlagParkStep fieldTail.succ counterWidth
        (doublingState fieldTail counterWidth base coefficient active target
          parked flag) =
      doublingState fieldTail counterWidth
        { base with core := { base.core with scratchB := flag } }
        coefficient active target parked false := by
  rcases base with
    ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history,
      activeFlag, counter⟩, shared, publicTarget⟩
  simp only at hclean
  subst scratchB
  cases flag <;>
    simp [reductionFlagParkStep, reductionFlagParkGates,
      EncodedBit.swapGates,
      EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
      EncodedBit.cnotStep, doublingState, arithmeticState]

/-- Literal reversible reduction of the retained `(n+1)`-bit Kaliski
coefficient: swap it into the borrowed VBE target, reduce once, swap it back,
and park the one-bit reduction predicate in existing `scratchB`. -/
def coefficientReduceGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  doublingSwapGates fieldTail counterWidth ++
    modularReduceGates fieldTail counterWidth p ++
    doublingSwapGates fieldTail counterWidth ++
    reductionFlagParkGates fieldTail.succ counterWidth

/-- Circuit compiled from the literal reversible coefficient-reduction
ledger. -/
def coefficientReduceProgram (fieldTail counterWidth p : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coefficientReduceGates fieldTail counterWidth p)

/-- Folded action of the reversible coefficient-reduction ledger. -/
def coefficientReduceStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (coefficientReduceGates fieldTail counterWidth p)

/-- The flattened coefficient reduction executes swap, reduction, swap, and
flag parking in source order. -/
lemma coefficientReduceStep_eq_stages (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    coefficientReduceStep fieldTail counterWidth p x =
      reductionFlagParkStep fieldTail.succ counterWidth
        (doublingSwapStep fieldTail counterWidth
          (modularReduceStep fieldTail counterWidth p
            (doublingSwapStep fieldTail counterWidth x))) := by
  simp only [coefficientReduceStep, coefficientReduceGates,
    reductionFlagParkStep, doublingSwapStep, modularReduceStep,
    EncodedBit.GateSpec.stepList_append]

/-- One exact coefficient reduction produces a canonical residue, leaves the
borrowed arithmetic words clean, and retains only the reversible one-bit
predicate in existing `scratchB`. -/
lemma coefficientReduceStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (raw : Word (fieldTail.succ + 1))
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hraw : raw.val < 2 * p) (hclean : base.core.scratchB = false) :
    coefficientReduceStep fieldTail counterWidth p
        (doublingState fieldTail counterWidth base raw
          (widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false) =
      doublingState fieldTail counterWidth
        { base with core :=
            { base.core with scratchB := decide (p ≤ raw.val) } }
        (reducedWord fieldTail p hpPos hp raw hraw)
        (widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false := by
  let zeroWide : Word (fieldTail.succ + 1) :=
    widenFixedWord fieldTail.succ 0
  let modulus : Word fieldTail.succ := ⟨p, hp⟩
  let reduced := reducedWord fieldTail p hpPos hp raw hraw
  let reducedFlag : Bool := decide (p ≤ raw.val)
  let s0 := doublingState fieldTail counterWidth base raw zeroWide 0
    modulus false
  let s1 := doublingState fieldTail counterWidth base 0 zeroWide raw
    modulus false
  let s2 := doublingState fieldTail counterWidth base 0 zeroWide reduced
    modulus reducedFlag
  let s3 := doublingState fieldTail counterWidth base reduced zeroWide 0
    modulus reducedFlag
  let s4 := doublingState fieldTail counterWidth
    { base with core := { base.core with scratchB := reducedFlag } }
    reduced zeroWide 0 modulus false
  have hs1 : doublingSwapStep fieldTail counterWidth s0 = s1 := by
    simpa [s0, s1, zeroWide, modulus] using
      doublingSwapStep_state fieldTail counterWidth base raw zeroWide 0
        modulus false
  have hs2 : modularReduceStep fieldTail counterWidth p s1 = s2 := by
    simpa [s1, s2, doublingState, reduced, reducedFlag] using
      modularReduceStep_state fieldTail counterWidth p
        { base with core :=
            { base.core with rCoeff := (0 : Word (fieldTail.succ + 1)) } }
        raw hpPos hp hraw
  have hs3 : doublingSwapStep fieldTail counterWidth s2 = s3 := by
    simpa [s2, s3] using
      doublingSwapStep_state fieldTail counterWidth base 0 zeroWide reduced
        modulus reducedFlag
  have hs4 : reductionFlagParkStep fieldTail.succ counterWidth s3 = s4 := by
    simpa [s3, s4, reducedFlag] using
      reductionFlagParkStep_state fieldTail counterWidth base reduced zeroWide 0
        modulus reducedFlag hclean
  change coefficientReduceStep fieldTail counterWidth p s0 = s4
  rw [coefficientReduceStep_eq_stages, hs1, hs2, hs3, hs4]

/-- The native reversible coefficient reducer realizes its literal gate-list
action. -/
lemma coefficientReduce_realizes (fieldTail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (MK.Compact.encoding fieldTail.succ counterWidth)
      (coefficientReduceProgram fieldTail counterWidth p) environment
      (coefficientReduceStep fieldTail counterWidth p) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (coefficientReduceGates fieldTail counterWidth p)

/-! ## Clean-work control of modular doubling -/

private lemma bitSwapGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (left right observed : EncodedBit encoding)
    (hleftRight : left.wire ≠ right.wire)
    (hleftObserved : left.wire ≠ observed.wire)
    (hrightObserved : right.wire ≠ observed.wire) :
    forall gate, gate ∈ EncodedBit.swapGates left right hleftRight ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact ⟨hleftObserved, hrightObserved⟩
  · exact ⟨hrightObserved, hleftObserved⟩
  · exact ⟨hleftObserved, hrightObserved⟩

private lemma wordSwapGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (left right : EncodedBit.Word encoding width)
    (hleftRight : forall bit,
      (left.bit bit).wire ≠ (right.bit bit).wire)
    (observed : EncodedBit encoding)
    (hleftObserved : forall bit,
      (left.bit bit).wire ≠ observed.wire)
    (hrightObserved : forall bit,
      (right.bit bit).wire ≠ observed.wire) :
    forall gate,
      gate ∈ EncodedBit.Word.swapGates left right hleftRight ->
        EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  simp only [EncodedBit.Word.swapGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨bit, _hbit, hgate⟩
  exact bitSwapGates_bitDisjoint_observed
    (left.bit bit) (right.bit bit) observed (hleftRight bit)
    (hleftObserved bit) (hrightObserved bit) gate hgate

private lemma xorIntoGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (source target : EncodedBit.Word encoding width)
    (hsourceTarget : forall bit,
      (source.bit bit).wire ≠ (target.bit bit).wire)
    (observed : EncodedBit encoding)
    (hsourceObserved : forall bit,
      (source.bit bit).wire ≠ observed.wire)
    (htargetObserved : forall bit,
      (target.bit bit).wire ≠ observed.wire) :
    forall gate,
      gate ∈ EncodedBit.Word.xorIntoGates source target hsourceTarget ->
        EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [EncodedBit.Word.xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  exact ⟨hsourceObserved bit, htargetObserved bit⟩

private lemma adjacentShiftRightGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width)
    (hword : forall left right, left ≠ right ->
      (word.bit left).wire ≠ (word.bit right).wire)
    (observed : EncodedBit encoding)
    (hwordObserved : forall bit,
      (word.bit bit).wire ≠ observed.wire) :
    forall gate,
      gate ∈ EncodedBit.Word.adjacentShiftRightGates word hword ->
        EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  have hforward :
      gate ∈ EncodedBit.Word.adjacentShiftLeftGates word hword := by
    exact List.mem_reverse.mp (by
      simpa [EncodedBit.Word.adjacentShiftRightGates] using hgate)
  simp only [EncodedBit.Word.adjacentShiftLeftGates,
    List.mem_flatMap] at hforward
  rcases hforward with ⟨bit, _hbit, hgate⟩
  exact bitSwapGates_bitDisjoint_observed
    (word.bit (EncodedBit.Word.adjacentLeftIndex width bit))
    (word.bit (EncodedBit.Word.adjacentRightIndex width bit)) observed
    (hword _ _
      (EncodedBit.Word.adjacentLeftIndex_ne_adjacentRightIndex width bit))
    (hwordObserved _) (hwordObserved _) gate
    (by simpa [EncodedBit.Word.adjacentSwapGates] using hgate)

private lemma controlledXorConstantGates_bitDisjoint_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (control : EncodedBit encoding)
    (target : EncodedBit.Word encoding width)
    (constant : Fin (2 ^ width))
    (hcontrolTarget : forall bit,
      control.wire ≠ (target.bit bit).wire)
    (observed : EncodedBit encoding)
    (hcontrolObserved : control.wire ≠ observed.wire)
    (htargetObserved : forall bit,
      (target.bit bit).wire ≠ observed.wire) :
    forall gate,
      gate ∈ EncodedBit.Word.controlledXorConstantGates control target
        constant hcontrolTarget ->
        EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [EncodedBit.Word.controlledXorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  exact ⟨hcontrolObserved, htargetObserved bit⟩

private lemma activeSourceWord_observed_ne
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall bit,
      ((activeSourceWord fieldTail counterWidth).bit bit).wire ≠
        observed.wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [activeSourceWord, activeBit] using
      hcore (RegisterBits.activeBit fieldTail.succ counterWidth)
  · intro low
    simpa [activeSourceWord, vValueWord] using
      hcore (RegisterBits.vValueBit fieldTail.succ counterWidth low)

private lemma activeSourceLowWord_observed_ne
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall bit,
      ((activeSourceLowWord fieldTail counterWidth).bit bit).wire ≠
        observed.wire := by
  intro bit
  simpa [activeSourceLowWord, vValueWord] using
    hcore (RegisterBits.vValueBit fieldTail.succ counterWidth bit)

private lemma arithmeticTargetWord_observed_ne
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall bit,
      ((arithmeticTargetWord fieldTail counterWidth).bit bit).wire ≠
        observed.wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [arithmeticTargetWord, compareBit] using
      hcore (RegisterBits.compareBit fieldTail.succ counterWidth)
  · intro low
    simpa [arithmeticTargetWord, uValueWord] using
      hcore (RegisterBits.uValueBit fieldTail.succ counterWidth low)

private lemma parkedModulusWord_observed_ne
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall bit,
      ((parkedModulusWord fieldTail counterWidth).bit bit).wire ≠
        observed.wire := by
  intro bit
  simpa [parkedModulusWord, sCoeffValueWord] using
    hcore (RegisterBits.sCoeffValueBit fieldTail.succ counterWidth
      (Fin.castSucc bit))

private lemma rCoeffValueWord_observed_ne
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall bit,
      ((rCoeffValueWord fieldTail.succ counterWidth).bit bit).wire ≠
        observed.wire := by
  intro bit
  simpa [rCoeffValueWord] using
    hcore (RegisterBits.rCoeffValueBit fieldTail.succ counterWidth bit)

private lemma liftCoreBit_targetUpdatePath_wire_ne
    (fieldTail counterWidth : Nat)
    (coreBit : EncodedBit
      (registerEncoding fieldTail.succ counterWidth)) :
    (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
      (pathBit fieldTail.succ counterWidth).wire := by
  simpa [pathBit] using
    liftCoreBit_liftSharedBit_wire_ne fieldTail.succ counterWidth coreBit
      (sharedPathBit fieldTail.succ counterWidth)

private lemma targetValueWord_path_ne
    (fieldTail counterWidth : Nat) :
    forall bit,
      ((targetValueWord fieldTail.succ counterWidth).bit bit).wire ≠
        (pathBit fieldTail.succ counterWidth).wire := by
  intro bit
  exact Ne.symm (by
    simpa [pathBit, targetValueWord] using
      liftSharedBit_targetValueBit_wire_ne fieldTail.succ counterWidth
        (sharedPathBit fieldTail.succ counterWidth) bit)

private lemma targetSwapGates_bitDisjoint_path
    (fieldTail counterWidth : Nat) :
    forall gate, gate ∈ targetSwapGates fieldTail.succ counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (pathBit fieldTail.succ counterWidth) gate := by
  exact wordSwapGates_bitDisjoint_observed
    (targetValueWord fieldTail.succ counterWidth)
    (uValueWord fieldTail.succ counterWidth)
    (fun bit => publicTarget_arithmeticTargetLow_ne fieldTail.succ
      counterWidth bit bit)
    (pathBit fieldTail.succ counterWidth)
    (targetValueWord_path_ne fieldTail counterWidth)
    (fun bit => by
      simpa [uValueWord] using
        liftCoreBit_targetUpdatePath_wire_ne fieldTail counterWidth
          (RegisterBits.uValueBit fieldTail.succ counterWidth bit))

private lemma coefficientLoadGates_bitDisjoint_path
    (fieldTail counterWidth : Nat) :
    forall gate, gate ∈ coefficientLoadGates fieldTail.succ counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (pathBit fieldTail.succ counterWidth) gate := by
  exact xorIntoGates_bitDisjoint_observed
    (correctedValueWord fieldTail.succ counterWidth)
    (vValueWord fieldTail.succ counterWidth)
    (fun bit => correctedValue_activeSourceLow_ne fieldTail.succ
      counterWidth bit bit)
    (pathBit fieldTail.succ counterWidth)
    (fun bit => by
      simpa [correctedValueWord, rCoeffValueWord] using
        liftCoreBit_targetUpdatePath_wire_ne fieldTail counterWidth
          (RegisterBits.rCoeffValueBit fieldTail.succ counterWidth
            (Fin.castSucc bit)))
    (fun bit => by
      simpa [vValueWord] using
        liftCoreBit_targetUpdatePath_wire_ne fieldTail counterWidth
          (RegisterBits.vValueBit fieldTail.succ counterWidth bit))

private lemma sourceSwapGates_bitDisjoint_observed
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall gate, gate ∈ sourceSwapGates fieldTail counterWidth ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  exact wordSwapGates_bitDisjoint_observed
    (activeSourceLowWord fieldTail counterWidth)
    (parkedModulusWord fieldTail counterWidth)
    (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
    observed
    (activeSourceLowWord_observed_ne fieldTail counterWidth observed hcore)
    (parkedModulusWord_observed_ne fieldTail counterWidth observed hcore)

private lemma arithmeticAdderGates_bitDisjoint_observed
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire)
    (hcarryIn :
      (coefficientCarryInBit fieldTail.succ counterWidth).wire ≠
        observed.wire)
    (hwork : forall bit,
      (coefficientCarryWorkBit fieldTail.succ counterWidth bit).wire ≠
        observed.wire) :
    forall gate,
      gate ∈ arithmeticAdderGates fieldTail counterWidth ->
        EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  exact PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
      (arithmeticLayout fieldTail counterWidth) observed
      (activeSourceWord_observed_ne fieldTail counterWidth observed hcore)
      (arithmeticTargetWord_observed_ne fieldTail counterWidth observed hcore)
      hcarryIn
      (fun bit => by
        simpa [arithmeticLayout, coefficientCarryWorkWord] using hwork bit)
      gate
      (by simpa [arithmeticAdderGates] using hgate)

private lemma copyReductionFlagGates_bitDisjoint_observed
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall gate, gate ∈ copyReductionFlagGates fieldTail counterWidth ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [copyReductionFlagGates] at hgate
  rcases List.mem_cons.mp hgate with heq | hrest
  · rw [heq]
    simpa [EncodedBit.GateSpec.bitDisjoint, scratchABit] using
      hcore (RegisterBits.scratchABit fieldTail.succ counterWidth)
  · have heq : gate =
        EncodedBit.GateSpec.cnot
          (compareBit fieldTail.succ counterWidth)
          (scratchABit fieldTail.succ counterWidth)
          (compareBit_scratchABit_wire_ne fieldTail.succ counterWidth) :=
      List.mem_singleton.mp hrest
    rw [heq]
    exact ⟨
      by simpa [compareBit] using
        hcore (RegisterBits.compareBit fieldTail.succ counterWidth),
      by simpa [scratchABit] using
        hcore (RegisterBits.scratchABit fieldTail.succ counterWidth)⟩

private lemma cleanupReductionFlagGates_bitDisjoint_observed
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall gate, gate ∈ cleanupReductionFlagGates fieldTail counterWidth ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  have heq : gate =
      EncodedBit.GateSpec.cnot
        (compareBit fieldTail.succ counterWidth)
        (scratchABit fieldTail.succ counterWidth)
        (compareBit_scratchABit_wire_ne fieldTail.succ counterWidth) := by
    simpa only [cleanupReductionFlagGates, List.mem_singleton] using hgate
  rw [heq]
  exact ⟨
    by simpa [compareBit] using
      hcore (RegisterBits.compareBit fieldTail.succ counterWidth),
    by simpa [scratchABit] using
      hcore (RegisterBits.scratchABit fieldTail.succ counterWidth)⟩

private lemma modularReduceGates_bitDisjoint_observed
    (fieldTail counterWidth p : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire)
    (hcarryIn :
      (coefficientCarryInBit fieldTail.succ counterWidth).wire ≠
        observed.wire)
    (hwork : forall bit,
      (coefficientCarryWorkBit fieldTail.succ counterWidth bit).wire ≠
        observed.wire) :
    forall gate, gate ∈ modularReduceGates fieldTail counterWidth p ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  have hadder := arithmeticAdderGates_bitDisjoint_observed
    fieldTail counterWidth observed hcore hcarryIn hwork
  have hsource := sourceSwapGates_bitDisjoint_observed
    fieldTail counterWidth observed hcore
  have hclear : forall next,
      next ∈ clearActiveModulusGates fieldTail counterWidth p ->
        EncodedBit.GateSpec.bitDisjoint observed next := by
    intro next hnext
    exact controlledXorConstantGates_bitDisjoint_observed
      (scratchABit fieldTail.succ counterWidth)
      (activeSourceWord fieldTail counterWidth)
      (modulusWordLabel fieldTail p)
      (reductionFlag_activeSource_ne fieldTail counterWidth)
      observed
      (by
        simpa [scratchABit] using
          hcore (RegisterBits.scratchABit fieldTail.succ counterWidth))
      (activeSourceWord_observed_ne fieldTail counterWidth observed hcore)
      next
      (by simpa [clearActiveModulusGates] using hnext)
  rw [modularReduceGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | h11
  · rcases List.mem_append.mp hprefix with hprefix | h10
    · rcases List.mem_append.mp hprefix with hprefix | h9
      · rcases List.mem_append.mp hprefix with hprefix | h8
        · rcases List.mem_append.mp hprefix with hprefix | h7
          · rcases List.mem_append.mp hprefix with hprefix | h6
            · rcases List.mem_append.mp hprefix with hprefix | h5
              · rcases List.mem_append.mp hprefix with hprefix | h4
                · rcases List.mem_append.mp hprefix with hprefix | h3
                  · rcases List.mem_append.mp hprefix with h1 | h2
                    · exact hadder gate h1
                    · exact hsource gate h2
                  · exact hadder gate (List.mem_reverse.mp h3)
                · exact copyReductionFlagGates_bitDisjoint_observed
                    fieldTail counterWidth observed hcore gate h4
              · exact hclear gate h5
            · exact hadder gate h6
          · exact hclear gate (List.mem_reverse.mp (by
              simpa only [restoreActiveModulusGates] using h7))
        · exact hsource gate h8
      · exact hadder gate (List.mem_reverse.mp h9)
    · exact cleanupReductionFlagGates_bitDisjoint_observed
        fieldTail counterWidth observed hcore gate h10
  · exact hadder gate h11

private lemma modularSubtractGates_bitDisjoint_path
    (fieldTail counterWidth p : Nat) :
    forall gate, gate ∈ modularSubtractGates fieldTail counterWidth p ->
      EncodedBit.GateSpec.bitDisjoint
        (pathBit fieldTail.succ counterWidth) gate := by
  intro gate hgate
  exact modularReduceGates_bitDisjoint_observed fieldTail counterWidth p
    (pathBit fieldTail.succ counterWidth)
    (liftCoreBit_targetUpdatePath_wire_ne fieldTail counterWidth)
    (Ne.symm
      (pathBit_coefficientCarryInBit_wire_ne fieldTail.succ counterWidth))
    (fun bit => Ne.symm
      (pathBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth bit))
    gate
    (List.mem_reverse.mp (by
      simpa only [modularSubtractGates] using hgate))

/-- The raw public-target subtraction ledger never reads or writes the compact
path bit, so that bit remains available for an external clean-work control
lift. -/
lemma targetUpdateGates_bitDisjoint_path
    (fieldTail counterWidth p : Nat) :
    forall gate, gate ∈ targetUpdateGates fieldTail counterWidth p ->
      EncodedBit.GateSpec.bitDisjoint
        (pathBit fieldTail.succ counterWidth) gate := by
  intro gate hgate
  rw [targetUpdateGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | h5
  · rcases List.mem_append.mp hprefix with hprefix | h4
    · rcases List.mem_append.mp hprefix with hprefix | h3
      · rcases List.mem_append.mp hprefix with h1 | h2
        · exact targetSwapGates_bitDisjoint_path fieldTail counterWidth
            gate h1
        · exact coefficientLoadGates_bitDisjoint_path fieldTail counterWidth
            gate h2
      · exact modularSubtractGates_bitDisjoint_path
          fieldTail counterWidth p gate h3
    · exact coefficientLoadGates_bitDisjoint_path fieldTail counterWidth
        gate (List.mem_reverse.mp h4)
  · exact targetSwapGates_bitDisjoint_path fieldTail counterWidth
      gate (List.mem_reverse.mp h5)

/-- Reversing the public-target ledger preserves the same physical
disjointness from the compact path bit. -/
lemma targetUpdateReverseGates_bitDisjoint_path
    (fieldTail counterWidth p : Nat) :
    forall gate,
      gate ∈ (targetUpdateGates fieldTail counterWidth p).reverse ->
        EncodedBit.GateSpec.bitDisjoint
          (pathBit fieldTail.succ counterWidth) gate := by
  intro gate hgate
  exact targetUpdateGates_bitDisjoint_path fieldTail counterWidth p gate
    (List.mem_reverse.mp hgate)

private lemma doublingCleanupGates_bitDisjoint_observed
    (fieldTail counterWidth : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire) :
    forall gate, gate ∈ doublingCleanupGates fieldTail counterWidth ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  have heq : gate =
      EncodedBit.GateSpec.cnot
        ((rCoeffValueWord fieldTail.succ counterWidth).bit
          (Fin.castSucc (coefficientLowBit fieldTail)))
        (scratchABit fieldTail.succ counterWidth)
        (rCoeffLow_reductionFlag_ne fieldTail counterWidth) := by
    simpa only [doublingCleanupGates, List.mem_singleton] using hgate
  rw [heq]
  exact ⟨
    rCoeffValueWord_observed_ne fieldTail counterWidth observed hcore _,
    by simpa [scratchABit] using
      hcore (RegisterBits.scratchABit fieldTail.succ counterWidth)⟩

private lemma doublingGates_bitDisjoint_observed
    (fieldTail counterWidth p : Nat)
    (observed : EncodedBit
      (MK.Compact.encoding fieldTail.succ counterWidth))
    (hcore : forall coreBit,
      (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
        observed.wire)
    (hcarryIn :
      (coefficientCarryInBit fieldTail.succ counterWidth).wire ≠
        observed.wire)
    (hwork : forall bit,
      (coefficientCarryWorkBit fieldTail.succ counterWidth bit).wire ≠
        observed.wire) :
    forall gate, gate ∈ doublingGates fieldTail counterWidth p ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [doublingGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | h5
  · rcases List.mem_append.mp hprefix with hprefix | h4
    · rcases List.mem_append.mp hprefix with hprefix | h3
      · rcases List.mem_append.mp hprefix with h1 | h2
        · exact wordSwapGates_bitDisjoint_observed
            (rCoeffValueWord fieldTail.succ counterWidth)
            (arithmeticTargetWord fieldTail counterWidth)
            (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
            observed
            (rCoeffValueWord_observed_ne fieldTail counterWidth observed hcore)
            (arithmeticTargetWord_observed_ne fieldTail counterWidth observed hcore)
            gate h1
        · exact adjacentShiftRightGates_bitDisjoint_observed
            (arithmeticTargetWord fieldTail counterWidth)
            (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)
            observed
            (arithmeticTargetWord_observed_ne fieldTail counterWidth observed hcore)
            gate h2
      · exact modularReduceGates_bitDisjoint_observed fieldTail counterWidth p
          observed hcore hcarryIn hwork gate h3
    · exact wordSwapGates_bitDisjoint_observed
        (rCoeffValueWord fieldTail.succ counterWidth)
        (arithmeticTargetWord fieldTail counterWidth)
        (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
        observed
        (rCoeffValueWord_observed_ne fieldTail counterWidth observed hcore)
        (arithmeticTargetWord_observed_ne fieldTail counterWidth observed hcore)
        gate h4
  · exact doublingCleanupGates_bitDisjoint_observed
      fieldTail counterWidth observed hcore gate h5

private lemma liftCoreBit_path_wire_ne
    (fieldTail counterWidth : Nat)
    (coreBit : EncodedBit
      (registerEncoding fieldTail.succ counterWidth)) :
    (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
      (pathBit fieldTail.succ counterWidth).wire := by
  simpa [pathBit] using
    liftCoreBit_liftSharedBit_wire_ne fieldTail.succ counterWidth coreBit
      (sharedPathBit fieldTail.succ counterWidth)

private lemma liftCoreBit_control_wire_ne
    (fieldTail counterWidth : Nat)
    (coreBit : EncodedBit
      (registerEncoding fieldTail.succ counterWidth)) :
    (liftCoreBit fieldTail.succ counterWidth coreBit).wire ≠
      (controlBit fieldTail.succ counterWidth).wire := by
  simpa [controlBit] using
    liftCoreBit_liftSharedBit_wire_ne fieldTail.succ counterWidth coreBit
      (sharedControlBit fieldTail.succ counterWidth)

/-- The raw modular-doubling ledger never reads or writes the correction
selector path bit. -/
lemma doublingGates_bitDisjoint_path
    (fieldTail counterWidth p : Nat) :
    forall gate, gate ∈ doublingGates fieldTail counterWidth p ->
      EncodedBit.GateSpec.bitDisjoint
        (pathBit fieldTail.succ counterWidth) gate := by
  exact doublingGates_bitDisjoint_observed fieldTail counterWidth p
    (pathBit fieldTail.succ counterWidth)
    (liftCoreBit_path_wire_ne fieldTail counterWidth)
    (Ne.symm
      (pathBit_coefficientCarryInBit_wire_ne fieldTail.succ counterWidth))
    (fun bit => Ne.symm
      (pathBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth bit))

/-- The raw modular-doubling ledger never reads or writes the clean control
work bit used by its outer control lift. -/
lemma doublingGates_bitDisjoint_control
    (fieldTail counterWidth p : Nat) :
    forall gate, gate ∈ doublingGates fieldTail counterWidth p ->
      EncodedBit.GateSpec.bitDisjoint
        (controlBit fieldTail.succ counterWidth) gate := by
  exact doublingGates_bitDisjoint_observed fieldTail counterWidth p
    (controlBit fieldTail.succ counterWidth)
    (liftCoreBit_control_wire_ne fieldTail counterWidth)
    (Ne.symm
      (controlBit_coefficientCarryInBit_wire_ne fieldTail.succ counterWidth))
    (fun bit => Ne.symm
      (controlBit_coefficientCarryWorkBit_wire_ne fieldTail.succ counterWidth bit))

/-- Clean-work control lift of one compact modular doubling. -/
def controlledDoublingGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (pathBit fieldTail.succ counterWidth)
    (controlBit fieldTail.succ counterWidth)
    (doublingGates fieldTail counterWidth p)
    (doublingGates_bitDisjoint_path fieldTail counterWidth p)
    (doublingGates_bitDisjoint_control fieldTail counterWidth p)
    (pathBit_controlBit_wire_ne fieldTail.succ counterWidth)

/-- Actual circuit for path-controlled compact modular doubling. -/
def controlledDoublingProgram (fieldTail counterWidth p : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (controlledDoublingGates fieldTail counterWidth p)

/-- Folded action of path-controlled compact modular doubling. -/
def controlledDoublingStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (controlledDoublingGates fieldTail counterWidth p)

/-- The controlled doubling circuit realizes its literal native gate ledger. -/
lemma controlledDoubling_realizes (fieldTail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (MK.Compact.encoding fieldTail.succ counterWidth)
      (controlledDoublingProgram fieldTail counterWidth p) environment
      (controlledDoublingStep fieldTail counterWidth p) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (controlledDoublingGates fieldTail counterWidth p)

/-- Structured clean-work action of path-controlled modular doubling. -/
def controlledDoublingStructuredStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  fun x =>
    if (pathBit fieldTail.succ counterWidth).get x then
      doublingStep fieldTail counterWidth p x
    else x

/-- With clean control work, the exact controlled ledger is one raw modular
doubling on a true path and identity on a false path. -/
lemma controlledDoublingStep_eq_structured_of_clean
    (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth)
    (hwork : (controlBit fieldTail.succ counterWidth).get x = false) :
    controlledDoublingStep fieldTail counterWidth p x =
      controlledDoublingStructuredStep fieldTail counterWidth p x := by
  cases hpath : (pathBit fieldTail.succ counterWidth).get x with
  | false =>
      have hcontrolled :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
          (pathBit fieldTail.succ counterWidth)
          (controlBit fieldTail.succ counterWidth)
          (doublingGates fieldTail counterWidth p)
          (doublingGates_bitDisjoint_path fieldTail counterWidth p)
          (doublingGates_bitDisjoint_control fieldTail counterWidth p)
          (pathBit_controlBit_wire_ne fieldTail.succ counterWidth)
          x hpath
      have hpathFalse :
          ¬ ((pathBit fieldTail.succ counterWidth).get x = true) := by
        intro htrue
        rw [hpath] at htrue
        contradiction
      rw [controlledDoublingStructuredStep, if_neg hpathFalse]
      simpa [controlledDoublingStep, controlledDoublingGates,
        EncodedBit.GateSpec.controlledListWithWorkStep] using hcontrolled
  | true =>
      have hcontrolled :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
          (pathBit fieldTail.succ counterWidth)
          (controlBit fieldTail.succ counterWidth)
          (doublingGates fieldTail counterWidth p)
          (doublingGates_bitDisjoint_path fieldTail counterWidth p)
          (doublingGates_bitDisjoint_control fieldTail counterWidth p)
          (pathBit_controlBit_wire_ne fieldTail.succ counterWidth)
          x hpath hwork
      rw [controlledDoublingStructuredStep, if_pos hpath]
      simpa [controlledDoublingStep, controlledDoublingGates,
        EncodedBit.GateSpec.controlledListWithWorkStep,
        doublingStep] using hcontrolled

private lemma gateSpecStepList_get_of_bitDisjoint
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding))
    (observed : EncodedBit encoding)
    (h : forall gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint observed gate)
    (x : Data) :
    observed.get (EncodedBit.GateSpec.stepList gates x) = observed.get x := by
  induction gates generalizing x with
  | nil => rfl
  | cons gate rest ih =>
      change observed.get (EncodedBit.GateSpec.stepList rest
          (EncodedBit.GateSpec.step gate x)) = observed.get x
      rw [ih (fun next hnext => h next (by simp [hnext]))
        (EncodedBit.GateSpec.step gate x)]
      exact EncodedBit.GateSpec.step_get_of_bitDisjoint gate observed
        (h gate (by simp)) x

/-- Raw modular doubling preserves the external selector path. -/
lemma doublingStep_get_path (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (pathBit fieldTail.succ counterWidth).get
        (doublingStep fieldTail counterWidth p x) =
      (pathBit fieldTail.succ counterWidth).get x := by
  exact gateSpecStepList_get_of_bitDisjoint
    (doublingGates fieldTail counterWidth p)
    (pathBit fieldTail.succ counterWidth)
    (doublingGates_bitDisjoint_path fieldTail counterWidth p) x

/-- Raw modular doubling preserves the external clean control-work bit. -/
lemma doublingStep_get_control (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    (controlBit fieldTail.succ counterWidth).get
        (doublingStep fieldTail counterWidth p x) =
      (controlBit fieldTail.succ counterWidth).get x := by
  exact gateSpecStepList_get_of_bitDisjoint
    (doublingGates fieldTail counterWidth p)
    (controlBit fieldTail.succ counterWidth)
    (doublingGates_bitDisjoint_control fieldTail counterWidth p) x

/-- A clean controlled doubling returns its per-gate control work clean. -/
lemma controlledDoublingStep_get_control_of_clean
    (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth)
    (hwork : (controlBit fieldTail.succ counterWidth).get x = false) :
    (controlBit fieldTail.succ counterWidth).get
        (controlledDoublingStep fieldTail counterWidth p x) = false := by
  rw [controlledDoublingStep_eq_structured_of_clean
    fieldTail counterWidth p x hwork]
  rw [controlledDoublingStructuredStep]
  by_cases hpath : (pathBit fieldTail.succ counterWidth).get x = true
  · rw [if_pos hpath, doublingStep_get_control, hwork]
  · rw [if_neg hpath, hwork]

/-- A clean controlled doubling preserves its selector path. -/
lemma controlledDoublingStep_get_path_of_clean
    (fieldTail counterWidth p : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth)
    (hwork : (controlBit fieldTail.succ counterWidth).get x = false) :
    (pathBit fieldTail.succ counterWidth).get
        (controlledDoublingStep fieldTail counterWidth p x) =
      (pathBit fieldTail.succ counterWidth).get x := by
  rw [controlledDoublingStep_eq_structured_of_clean
    fieldTail counterWidth p x hwork]
  rw [controlledDoublingStructuredStep]
  by_cases hpath : (pathBit fieldTail.succ counterWidth).get x = true
  · rw [if_pos hpath, doublingStep_get_path]
  · rw [if_neg hpath]

/-! ## Fixed-loop correction selector -/

/-- The real correction count, retained at full logarithmic width in the
fixed-round MK core. -/
def correctionCountWord (n counterTail : Nat) :
    EncodedBit.Word (MK.Compact.encoding n (counterTail + 1))
      (counterTail + 1) :=
  paddingCounterValueWord n counterTail

/-- One low bit of the temporary fixed-loop index. -/
def correctionIndexLowBit (n counterTail : Nat) (bit : Fin counterTail) :
    EncodedBit (MK.Compact.encoding n (counterTail + 1)) :=
  correctionCounterValueBit n (counterTail + 1)
    ⟨bit.val, by omega⟩

/-- Widen the `(counterWidth-1)`-bit fixed-loop index with the clean shared
control bit.  For P-256 this is the 8-bit index `0..255` plus a zero ninth
bit, while the independent core counter can represent the value `256`. -/
def correctionIndexWord (n counterTail : Nat) :
    EncodedBit.Word (MK.Compact.encoding n (counterTail + 1))
      (counterTail + 1) where
  bit := fun bit =>
    Fin.lastCases (controlBit n (counterTail + 1))
      (correctionIndexLowBit n counterTail) bit

@[simp] lemma correctionIndexWord_bit_last (n counterTail : Nat) :
    (correctionIndexWord n counterTail).bit (Fin.last counterTail) =
      controlBit n (counterTail + 1) := by
  simp [correctionIndexWord]

@[simp] lemma correctionIndexWord_bit_castSucc
    (n counterTail : Nat) (bit : Fin counterTail) :
    (correctionIndexWord n counterTail).bit (Fin.castSucc bit) =
      correctionIndexLowBit n counterTail bit := by
  simp [correctionIndexWord]

@[simp] lemma correctionIndexLowBit_get
    (n counterTail : Nat) (bit : Fin counterTail)
    (x : MK.Compact.Registers n (counterTail + 1)) :
    (correctionIndexLowBit n counterTail bit).get x =
      x.shared.correctionCounter.val.testBit bit.val := by
  simp [correctionIndexLowBit]

/-- Embed the logarithmic comparator borrow word into the low prefix of the
sole coefficient carry bank. -/
def correctionBorrowWorkIndex (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) (bit : Fin (counterTail + 1)) : Fin n :=
  ⟨bit.val, lt_of_lt_of_le bit.isLt hwidth⟩

@[simp] lemma correctionBorrowWorkIndex_val
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (bit : Fin (counterTail + 1)) :
    (correctionBorrowWorkIndex n counterTail hwidth bit).val = bit.val :=
  rfl

/-- One comparator borrow bit in the shared VBE bank. -/
def correctionBorrowWorkBit (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) (bit : Fin (counterTail + 1)) :
    EncodedBit (MK.Compact.encoding n (counterTail + 1)) :=
  coefficientCarryWorkBit n (counterTail + 1)
    (correctionBorrowWorkIndex n counterTail hwidth bit)

/-- Logarithmic prefix of the VBE bank borrowed by the correction selector. -/
def correctionBorrowWorkWord (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    EncodedBit.Word (MK.Compact.encoding n (counterTail + 1))
      (counterTail + 1) where
  bit := correctionBorrowWorkBit n counterTail hwidth

private lemma correctionIndexWord_pairwise_ne
    (n counterTail : Nat) :
    forall left right, left ≠ right ->
      ((correctionIndexWord n counterTail).bit left).wire ≠
        ((correctionIndexWord n counterTail).bit right).wire := by
  intro left right hne
  revert hne
  revert right
  refine Fin.lastCases ?_ ?_ left
  · intro right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · exact fun h => (h rfl).elim
    · intro low _
      simpa [correctionIndexWord, correctionIndexLowBit,
        correctionCounterValueBit] using
        controlBit_correctionCounterBit_wire_ne n (counterTail + 1)
          (WireAddress.littleEndianWire ⟨low.val, by omega⟩)
  · intro low right hne
    revert hne
    refine Fin.lastCases ?_ ?_ right
    · intro _
      simpa [correctionIndexWord, correctionIndexLowBit,
        correctionCounterValueBit] using
        Ne.symm (controlBit_correctionCounterBit_wire_ne
          n (counterTail + 1)
          (WireAddress.littleEndianWire ⟨low.val, by omega⟩))
    · intro other hne
      have hlow : low ≠ other := by
        intro heq
        apply hne
        subst other
        rfl
      simpa [correctionIndexWord, correctionIndexLowBit,
        correctionCounterValueBit] using
        correctionCounterBit_wire_ne n (counterTail + 1)
          (littleEndianWire_ne (by
            intro heq
            apply hlow
            apply Fin.ext
            exact congrArg Fin.val heq))

private lemma correctionCountWord_pairwise_ne
    (n counterTail : Nat) :
    forall left right, left ≠ right ->
      ((correctionCountWord n counterTail).bit left).wire ≠
        ((correctionCountWord n counterTail).bit right).wire := by
  intro left right hne
  simpa [correctionCountWord, paddingCounterValueWord] using
    paddingCounterValueBit_wire_ne n counterTail hne

private lemma correctionIndex_count_ne (n counterTail : Nat) :
    forall indexBit countBit,
      ((correctionIndexWord n counterTail).bit indexBit).wire ≠
        ((correctionCountWord n counterTail).bit countBit).wire := by
  intro indexBit countBit
  refine Fin.lastCases ?_ ?_ indexBit
  · simpa [correctionIndexWord, correctionCountWord,
      paddingCounterValueWord, paddingCounterValueBit, controlBit] using
      Ne.symm (liftCoreBit_liftSharedBit_wire_ne n (counterTail + 1)
        (RegisterBits.counterBit n (counterTail + 1)
          (WireAddress.littleEndianWire countBit))
        (sharedControlBit n (counterTail + 1)))
  · intro low
    simpa [correctionIndexWord, correctionIndexLowBit,
      correctionCounterValueBit, correctionCounterBit,
      correctionCountWord, paddingCounterValueWord,
      paddingCounterValueBit] using
      Ne.symm (liftCoreBit_liftSharedBit_wire_ne n (counterTail + 1)
        (RegisterBits.counterBit n (counterTail + 1)
          (WireAddress.littleEndianWire countBit))
        (sharedCorrectionCounterBit n (counterTail + 1)
          (WireAddress.littleEndianWire ⟨low.val, by omega⟩)))

private lemma correctionIndex_scratchA_ne (n counterTail : Nat) :
    forall bit,
      ((correctionIndexWord n counterTail).bit bit).wire ≠
        (scratchABit n (counterTail + 1)).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [correctionIndexWord, scratchABit, controlBit] using
      Ne.symm (liftCoreBit_liftSharedBit_wire_ne n (counterTail + 1)
        (RegisterBits.scratchABit n (counterTail + 1))
        (sharedControlBit n (counterTail + 1)))
  · intro low
    simpa [correctionIndexWord, correctionIndexLowBit,
      correctionCounterValueBit, correctionCounterBit, scratchABit] using
      Ne.symm (liftCoreBit_liftSharedBit_wire_ne n (counterTail + 1)
        (RegisterBits.scratchABit n (counterTail + 1))
        (sharedCorrectionCounterBit n (counterTail + 1)
          (WireAddress.littleEndianWire ⟨low.val, by omega⟩)))

private lemma correctionCount_scratchA_ne (n counterTail : Nat) :
    forall bit,
      ((correctionCountWord n counterTail).bit bit).wire ≠
        (scratchABit n (counterTail + 1)).wire := by
  intro bit
  simpa [correctionCountWord, paddingCounterValueWord,
    paddingCounterValueBit, scratchABit] using
    liftCoreBit_wire_ne n (counterTail + 1)
      (Ne.symm (RegisterBits.scratchA_counter_wire_ne n (counterTail + 1)
        (WireAddress.littleEndianWire bit)))

private lemma correctionIndex_work_ne (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    forall indexBit workBit,
      ((correctionIndexWord n counterTail).bit indexBit).wire ≠
        ((correctionBorrowWorkWord n counterTail hwidth).bit workBit).wire := by
  intro indexBit workBit
  refine Fin.lastCases ?_ ?_ indexBit
  · simpa [correctionIndexWord, correctionBorrowWorkWord,
      correctionBorrowWorkBit] using
      controlBit_coefficientCarryWorkBit_wire_ne n (counterTail + 1)
        (correctionBorrowWorkIndex n counterTail hwidth workBit)
  · intro low
    simpa [correctionIndexWord, correctionIndexLowBit,
      correctionCounterValueBit, correctionBorrowWorkWord,
      correctionBorrowWorkBit] using
      correctionCounterBit_coefficientCarryWorkBit_wire_ne
        n (counterTail + 1)
        (WireAddress.littleEndianWire ⟨low.val, by omega⟩)
        (correctionBorrowWorkIndex n counterTail hwidth workBit)

private lemma correctionCount_work_ne (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    forall countBit workBit,
      ((correctionCountWord n counterTail).bit countBit).wire ≠
        ((correctionBorrowWorkWord n counterTail hwidth).bit workBit).wire := by
  intro countBit workBit
  simpa [correctionCountWord, paddingCounterValueWord,
    paddingCounterValueBit, correctionBorrowWorkWord,
    correctionBorrowWorkBit] using
    liftCoreBit_coefficientCarryWorkBit_wire_ne n (counterTail + 1)
      (RegisterBits.counterBit n (counterTail + 1)
        (WireAddress.littleEndianWire countBit))
      (correctionBorrowWorkIndex n counterTail hwidth workBit)

private lemma correctionScratchA_work_ne (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    forall workBit,
      (scratchABit n (counterTail + 1)).wire ≠
        ((correctionBorrowWorkWord n counterTail hwidth).bit workBit).wire := by
  intro workBit
  simpa [scratchABit, correctionBorrowWorkWord,
    correctionBorrowWorkBit] using
    liftCoreBit_coefficientCarryWorkBit_wire_ne n (counterTail + 1)
      (RegisterBits.scratchABit n (counterTail + 1))
      (correctionBorrowWorkIndex n counterTail hwidth workBit)

private lemma correctionBorrowWorkWord_pairwise_ne
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n) :
    forall left right, left ≠ right ->
      ((correctionBorrowWorkWord n counterTail hwidth).bit left).wire ≠
        ((correctionBorrowWorkWord n counterTail hwidth).bit right).wire := by
  intro left right hne
  apply coefficientCarryWorkBit_wire_ne n (counterTail + 1)
  intro heq
  apply hne
  apply Fin.ext
  simpa [correctionBorrowWorkIndex] using congrArg Fin.val heq

/-- Native subtract-borrow layout deciding whether a static fixed-loop index
is smaller than the real correction count. -/
def correctionLtBorrowLayout (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    QuantumAlg.Comparator.BorrowWorkLayout
      (encoding := MK.Compact.encoding n (counterTail + 1))
      (counterTail + 1) where
  minuend := correctionIndexWord n counterTail
  subtrahend := correctionCountWord n counterTail
  initialBorrow := scratchABit n (counterTail + 1)
  workBorrow := correctionBorrowWorkWord n counterTail hwidth
  minuendMinuend_ne := correctionIndexWord_pairwise_ne n counterTail
  subtrahendSubtrahend_ne := correctionCountWord_pairwise_ne n counterTail
  minuendSubtrahend_ne := correctionIndex_count_ne n counterTail
  minuendInitialBorrow_ne := correctionIndex_scratchA_ne n counterTail
  subtrahendInitialBorrow_ne := correctionCount_scratchA_ne n counterTail
  minuendWork_ne := correctionIndex_work_ne n counterTail hwidth
  subtrahendWork_ne := correctionCount_work_ne n counterTail hwidth
  initialBorrowWork_ne := correctionScratchA_work_ne n counterTail hwidth
  workWork_ne := correctionBorrowWorkWord_pairwise_ne n counterTail hwidth

/-- Forward native borrow ledger for one correction-count comparison. -/
def correctionLtBorrowGates (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding n (counterTail + 1))) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage
    (correctionLtBorrowLayout n counterTail hwidth)

/-- Folded action of the forward correction-count comparison. -/
def correctionLtBorrowStep (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    MK.Compact.Registers n (counterTail + 1) ->
      MK.Compact.Registers n (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionLtBorrowGates n counterTail hwidth)

/-- The forward comparison ledger is realized by its literal base gates. -/
lemma correctionLtBorrow_realizes (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    UnitaryCircuit.Realizes (MK.Compact.encoding n (counterTail + 1))
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (correctionLtBorrowGates n counterTail hwidth)) environment
      (correctionLtBorrowStep n counterTail hwidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (correctionLtBorrowGates n counterTail hwidth)

/-- The highest logarithmic borrow bit carries the full-word comparison. -/
def correctionLtFinalBorrowIndex (counterTail : Nat) :
    Fin (counterTail + 1) :=
  Fin.last counterTail

/-- The literal gate fold agrees with the generic ordered borrow recurrence. -/
lemma correctionLtBorrowStep_eq_indexStep (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n)
    (x : MK.Compact.Registers n (counterTail + 1)) :
    correctionLtBorrowStep n counterTail hwidth x =
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
        (correctionLtBorrowLayout n counterTail hwidth) x := by
  exact
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_stepList_eq_indexStep
      (correctionLtBorrowLayout n counterTail hwidth) x

/-- On a clean borrowed bank, the last borrow bit decides whether the
temporary fixed-loop index is smaller than the full-width correction count. -/
lemma correctionLtBorrowStep_get_final_work_of_clean
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (x : MK.Compact.Registers n (counterTail + 1))
    (hcontrol : (controlBit n (counterTail + 1)).get x = false)
    (hscratchA : (scratchABit n (counterTail + 1)).get x = false)
    (hwork : forall bit : Fin n,
      (coefficientCarryWorkBit n (counterTail + 1) bit).get x = false) :
    (correctionBorrowWorkBit n counterTail hwidth
        (correctionLtFinalBorrowIndex counterTail)).get
        (correctionLtBorrowStep n counterTail hwidth x) =
      decide (x.shared.correctionCounter.val < x.core.counter.val) := by
  rw [correctionLtBorrowStep_eq_indexStep]
  have hcontrolState : x.shared.control = false := by
    simpa only [controlBit_get] using hcontrol
  have hborrow :=
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_natBorrow
      (correctionLtBorrowLayout n counterTail hwidth)
      x.shared.correctionCounter.val x.core.counter.val
      (correctionLtFinalBorrowIndex counterTail) x
      (by
        intro bit
        simpa [correctionLtBorrowLayout, correctionBorrowWorkWord,
          correctionBorrowWorkBit] using
          hwork (correctionBorrowWorkIndex n counterTail hwidth bit))
      (by simpa [correctionLtBorrowLayout] using hscratchA)
      (by
        intro bit
        refine Fin.lastCases ?_ ?_ bit
        · have hbound :
              x.shared.correctionCounter.val < 2 ^ counterTail := by
            exact x.shared.correctionCounter.isLt
          simp [correctionLtBorrowLayout, correctionIndexWord, hcontrolState,
            Nat.testBit_lt_two_pow hbound]
        · intro low
          simp [correctionLtBorrowLayout, correctionIndexWord,
            correctionIndexLowBit])
      (by
        intro bit
        simp [correctionLtBorrowLayout, correctionCountWord,
          paddingCounterValueWord])
  rw [show
    (correctionBorrowWorkBit n counterTail hwidth
        (correctionLtFinalBorrowIndex counterTail)).get
        (QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
          (correctionLtBorrowLayout n counterTail hwidth) x) =
      QuantumAlg.Comparator.natBorrow
        x.shared.correctionCounter.val x.core.counter.val
        ((correctionLtFinalBorrowIndex counterTail).val + 1) by
    simpa [correctionLtBorrowLayout, correctionBorrowWorkWord] using hborrow]
  have hindex :
      x.shared.correctionCounter.val <
        2 ^ ((correctionLtFinalBorrowIndex counterTail).val + 1) := by
    have hbound := x.shared.correctionCounter.isLt
    change x.shared.correctionCounter.val < 2 ^ (counterTail + 1)
    exact lt_trans hbound
      (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
        (Nat.lt_succ_self counterTail))
  have hcount :
      x.core.counter.val <
        2 ^ ((correctionLtFinalBorrowIndex counterTail).val + 1) := by
    change x.core.counter.val < 2 ^ (counterTail + 1)
    exact x.core.counter.isLt
  simpa using
    QuantumAlg.Comparator.natBorrow_eq_decide_lt_of_lt_two_pow
      (a := x.shared.correctionCounter.val) (b := x.core.counter.val)
      (n := (correctionLtFinalBorrowIndex counterTail).val + 1)
      hindex hcount

private lemma correctionIndex_path_ne (n counterTail : Nat) :
    forall bit,
      ((correctionIndexWord n counterTail).bit bit).wire ≠
        (pathBit n (counterTail + 1)).wire := by
  intro bit
  refine Fin.lastCases ?_ ?_ bit
  · simpa [correctionIndexWord] using
      Ne.symm (pathBit_controlBit_wire_ne n (counterTail + 1))
  · intro low
    simpa [correctionIndexWord, correctionIndexLowBit,
      correctionCounterValueBit] using
      Ne.symm (pathBit_correctionCounterBit_wire_ne n (counterTail + 1)
        (WireAddress.littleEndianWire ⟨low.val, by omega⟩))

private lemma correctionCount_path_ne (n counterTail : Nat) :
    forall bit,
      ((correctionCountWord n counterTail).bit bit).wire ≠
        (pathBit n (counterTail + 1)).wire := by
  intro bit
  simpa [correctionCountWord, paddingCounterValueWord,
    paddingCounterValueBit, pathBit] using
    liftCoreBit_liftSharedBit_wire_ne n (counterTail + 1)
      (RegisterBits.counterBit n (counterTail + 1)
        (WireAddress.littleEndianWire bit))
      (sharedPathBit n (counterTail + 1))

private lemma correctionScratchA_path_ne (n counterTail : Nat) :
    (scratchABit n (counterTail + 1)).wire ≠
      (pathBit n (counterTail + 1)).wire := by
  simpa [scratchABit, pathBit] using
    liftCoreBit_liftSharedBit_wire_ne n (counterTail + 1)
      (RegisterBits.scratchABit n (counterTail + 1))
      (sharedPathBit n (counterTail + 1))

/-- The native borrow pass never touches its external comparison-output bit. -/
lemma correctionLtBorrowGates_bitDisjoint_path
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n) :
    forall gate, gate ∈ correctionLtBorrowGates n counterTail hwidth ->
      EncodedBit.GateSpec.bitDisjoint
        (pathBit n (counterTail + 1)) gate := by
  exact QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_bitDisjoint
    (correctionLtBorrowLayout n counterTail hwidth)
    (pathBit n (counterTail + 1))
    (correctionIndex_path_ne n counterTail)
    (correctionCount_path_ne n counterTail)
    (correctionScratchA_path_ne n counterTail)
    (fun bit => by
      simpa [correctionLtBorrowLayout, correctionBorrowWorkWord,
        correctionBorrowWorkBit] using
        Ne.symm (pathBit_coefficientCarryWorkBit_wire_ne n (counterTail + 1)
          (correctionBorrowWorkIndex n counterTail hwidth bit)))

/-- Copy the final borrow predicate into the reusable shared path bit. -/
def correctionLtCopyGate (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    EncodedBit.GateSpec (MK.Compact.encoding n (counterTail + 1)) :=
  .cnot
    (correctionBorrowWorkBit n counterTail hwidth
      (correctionLtFinalBorrowIndex counterTail))
    (pathBit n (counterTail + 1))
    (Ne.symm (by
      simpa [correctionBorrowWorkBit] using
        pathBit_coefficientCarryWorkBit_wire_ne n (counterTail + 1)
          (correctionBorrowWorkIndex n counterTail hwidth
            (correctionLtFinalBorrowIndex counterTail))))

/-- Compute-copy-uncompute comparison selector.  It leaves the predicate in
`path` and returns the borrowed coefficient carry prefix clean. -/
def correctionLtSelectorGates (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding n (counterTail + 1))) :=
  correctionLtBorrowGates n counterTail hwidth ++
    [correctionLtCopyGate n counterTail hwidth] ++
    (correctionLtBorrowGates n counterTail hwidth).reverse

/-- Circuit compiled from the native correction-selector ledger. -/
def correctionLtSelectorProgram (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding n (counterTail + 1)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (correctionLtSelectorGates n counterTail hwidth)

/-- Folded action of the correction-count selector. -/
def correctionLtSelectorStep (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    MK.Compact.Registers n (counterTail + 1) ->
      MK.Compact.Registers n (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionLtSelectorGates n counterTail hwidth)

/-- The correction selector realizes its literal compute-copy-uncompute
ledger. -/
lemma correctionLtSelector_realizes (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    UnitaryCircuit.Realizes (MK.Compact.encoding n (counterTail + 1))
      (correctionLtSelectorProgram n counterTail hwidth) environment
      (correctionLtSelectorStep n counterTail hwidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (correctionLtSelectorGates n counterTail hwidth)

/-- Reverse action of the logarithmic borrow ledger. -/
def correctionLtBorrowReverseStep (n counterTail : Nat)
    (hwidth : counterTail + 1 <= n) :
    MK.Compact.Registers n (counterTail + 1) ->
      MK.Compact.Registers n (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionLtBorrowGates n counterTail hwidth).reverse

/-- Forward then reverse borrow execution restores the whole carrier. -/
lemma correctionLtBorrowReverseStep_after_forward
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (x : MK.Compact.Registers n (counterTail + 1)) :
    correctionLtBorrowReverseStep n counterTail hwidth
        (correctionLtBorrowStep n counterTail hwidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (correctionLtBorrowGates n counterTail hwidth) x

/-- Reverse borrow cleanup commutes with flipping the untouched path bit. -/
lemma correctionLtBorrowReverseStep_flip_path_comm
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (x : MK.Compact.Registers n (counterTail + 1)) :
    correctionLtBorrowReverseStep n counterTail hwidth
        ((pathBit n (counterTail + 1)).flip x) =
      (pathBit n (counterTail + 1)).flip
        (correctionLtBorrowReverseStep n counterTail hwidth x) := by
  apply EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate hgate
  exact correctionLtBorrowGates_bitDisjoint_path n counterTail hwidth gate
    (by simpa [correctionLtBorrowReverseStep] using hgate)

/-- On a clean comparator boundary, the complete selector only conditionally
flips `path`; the real counter, temporary index, and the entire coefficient
adder bank are otherwise unchanged. -/
lemma correctionLtSelectorStep_eq_conditional_path_flip_of_clean
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (x : MK.Compact.Registers n (counterTail + 1))
    (hcontrol : (controlBit n (counterTail + 1)).get x = false)
    (hscratchA : (scratchABit n (counterTail + 1)).get x = false)
    (hwork : forall bit : Fin n,
      (coefficientCarryWorkBit n (counterTail + 1) bit).get x = false) :
    correctionLtSelectorStep n counterTail hwidth x =
      if x.shared.correctionCounter.val < x.core.counter.val then
        (pathBit n (counterTail + 1)).flip x
      else x := by
  let gates := correctionLtBorrowGates n counterTail hwidth
  let y := correctionLtBorrowStep n counterTail hwidth x
  have hpredicate :
      (correctionBorrowWorkBit n counterTail hwidth
        (correctionLtFinalBorrowIndex counterTail)).get y =
        decide (x.shared.correctionCounter.val < x.core.counter.val) := by
    exact correctionLtBorrowStep_get_final_work_of_clean
      n counterTail hwidth x hcontrol hscratchA hwork
  have hrestore :
      correctionLtBorrowReverseStep n counterTail hwidth y = x := by
    exact correctionLtBorrowReverseStep_after_forward
      n counterTail hwidth x
  have hcommute :
      correctionLtBorrowReverseStep n counterTail hwidth
          ((pathBit n (counterTail + 1)).flip y) =
        (pathBit n (counterTail + 1)).flip x := by
    rw [correctionLtBorrowReverseStep_flip_path_comm, hrestore]
  rw [correctionLtSelectorStep, correctionLtSelectorGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change correctionLtBorrowReverseStep n counterTail hwidth
      (EncodedBit.cnotStep
        (correctionBorrowWorkBit n counterTail hwidth
          (correctionLtFinalBorrowIndex counterTail))
        (pathBit n (counterTail + 1)) y) = _
  unfold EncodedBit.cnotStep
  rw [hpredicate]
  by_cases hlt : x.shared.correctionCounter.val < x.core.counter.val
  · simp [hlt, hcommute]
  · simp [hlt, hrestore]

/-- The selector xors the mathematical comparison into `path`. -/
lemma correctionLtSelectorStep_get_path_of_clean
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (x : MK.Compact.Registers n (counterTail + 1))
    (hcontrol : (controlBit n (counterTail + 1)).get x = false)
    (hscratchA : (scratchABit n (counterTail + 1)).get x = false)
    (hwork : forall bit : Fin n,
      (coefficientCarryWorkBit n (counterTail + 1) bit).get x = false) :
    (pathBit n (counterTail + 1)).get
        (correctionLtSelectorStep n counterTail hwidth x) =
      ((pathBit n (counterTail + 1)).get x ^^
        decide (x.shared.correctionCounter.val < x.core.counter.val)) := by
  rw [correctionLtSelectorStep_eq_conditional_path_flip_of_clean
    n counterTail hwidth x hcontrol hscratchA hwork]
  by_cases hlt : x.shared.correctionCounter.val < x.core.counter.val
  · rw [if_pos hlt, EncodedBit.get_flip_self]
    simp [hlt]
  · rw [if_neg hlt]
    simp [hlt]

/-- Every coefficient carry-work bit is restored by the clean selector. -/
lemma correctionLtSelectorStep_get_workCarry_of_clean
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (bit : Fin n) (x : MK.Compact.Registers n (counterTail + 1))
    (hcontrol : (controlBit n (counterTail + 1)).get x = false)
    (hscratchA : (scratchABit n (counterTail + 1)).get x = false)
    (hwork : forall workBit : Fin n,
      (coefficientCarryWorkBit n (counterTail + 1) workBit).get x = false) :
    (coefficientCarryWorkBit n (counterTail + 1) bit).get
        (correctionLtSelectorStep n counterTail hwidth x) = false := by
  rw [correctionLtSelectorStep_eq_conditional_path_flip_of_clean
    n counterTail hwidth x hcontrol hscratchA hwork]
  by_cases hlt : x.shared.correctionCounter.val < x.core.counter.val
  · rw [if_pos hlt]
    rw [EncodedBit.get_flip_of_wire_ne]
    · exact hwork bit
    · exact pathBit_coefficientCarryWorkBit_wire_ne n (counterTail + 1) bit
  · rw [if_neg hlt]
    exact hwork bit

/-- The clean selector preserves the VBE carry-in bit. -/
lemma correctionLtSelectorStep_get_carryIn_of_clean
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n)
    (x : MK.Compact.Registers n (counterTail + 1))
    (hcontrol : (controlBit n (counterTail + 1)).get x = false)
    (hscratchA : (scratchABit n (counterTail + 1)).get x = false)
    (hwork : forall workBit : Fin n,
      (coefficientCarryWorkBit n (counterTail + 1) workBit).get x = false) :
    (coefficientCarryInBit n (counterTail + 1)).get
        (correctionLtSelectorStep n counterTail hwidth x) =
      (coefficientCarryInBit n (counterTail + 1)).get x := by
  rw [correctionLtSelectorStep_eq_conditional_path_flip_of_clean
    n counterTail hwidth x hcontrol hscratchA hwork]
  by_cases hlt : x.shared.correctionCounter.val < x.core.counter.val
  · simp only [hlt, if_pos]
    exact EncodedBit.get_flip_of_wire_ne
      (pathBit n (counterTail + 1))
      (coefficientCarryInBit n (counterTail + 1))
      (pathBit_coefficientCarryInBit_wire_ne n (counterTail + 1)) x
  · simp [hlt]

/-! ## Static correction slots -/

/-- Embed one of the `n` static correction-slot indices into the reusable
`counterTail`-bit correction word. -/
def correctionSlotLabel (n counterTail : Nat)
    (hcapacity : n <= 2 ^ counterTail) (slot : Fin n) :
    Word counterTail :=
  ⟨slot.val, slot.isLt.trans_le hcapacity⟩

/-- Literal X-gate load of one static correction-slot index. -/
def correctionSlotLoadGates (n counterTail : Nat)
    (hcapacity : n <= 2 ^ counterTail) (slot : Fin n) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding n (counterTail + 1))) :=
  EncodedBit.Word.xorConstantGates
    (correctionCounterValueWord n (counterTail + 1))
    (correctionSlotLabel n counterTail hcapacity slot)

/-- Reverse X-gate unload of one static correction-slot index. -/
def correctionSlotUnloadGates (n counterTail : Nat)
    (hcapacity : n <= 2 ^ counterTail) (slot : Fin n) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding n (counterTail + 1))) :=
  (correctionSlotLoadGates n counterTail hcapacity slot).reverse

/-- Folded action of the literal correction-slot load. -/
def correctionSlotLoadStep (n counterTail : Nat)
    (hcapacity : n <= 2 ^ counterTail) (slot : Fin n) :
    MK.Compact.Registers n (counterTail + 1) ->
      MK.Compact.Registers n (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionSlotLoadGates n counterTail hcapacity slot)

/-- Folded action of the literal correction-slot unload. -/
def correctionSlotUnloadStep (n counterTail : Nat)
    (hcapacity : n <= 2 ^ counterTail) (slot : Fin n) :
    MK.Compact.Registers n (counterTail + 1) ->
      MK.Compact.Registers n (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionSlotUnloadGates n counterTail hcapacity slot)

/-- Loading and then unloading a static correction-slot index restores the
entire compact carrier. -/
lemma correctionSlotUnloadStep_after_load
    (n counterTail : Nat) (hcapacity : n <= 2 ^ counterTail)
    (slot : Fin n) (x : MK.Compact.Registers n (counterTail + 1)) :
    correctionSlotUnloadStep n counterTail hcapacity slot
        (correctionSlotLoadStep n counterTail hcapacity slot x) = x := by
  simpa [correctionSlotUnloadStep, correctionSlotUnloadGates,
    correctionSlotLoadStep] using
    EncodedBit.GateSpec.stepList_reverse_stepList
      (correctionSlotLoadGates n counterTail hcapacity slot) x

/-- Canonical boundary for one static correction slot.  The temporary index
and selector path are explicit; all arithmetic borrow wires are clean. -/
def correctionSlotState (fieldTail counterTail : Nat)
    (base : MK.Compact.Registers fieldTail.succ (counterTail + 1))
    (coefficient : Word (fieldTail.succ + 1))
    (modulus : Word fieldTail.succ) (index : Word counterTail)
    (path : Bool) :
    MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
  doublingState fieldTail (counterTail + 1)
    { base with
      shared :=
        { cleanSharedWork fieldTail.succ (counterTail + 1) with
          correctionCounter := index
          path := path } }
    coefficient (widenFixedWord fieldTail.succ 0) 0 modulus false

@[simp] private lemma pathBit_flip_state
    (n counterWidth : Nat) (x : MK.Compact.Registers n counterWidth) :
    (pathBit n counterWidth).flip x =
      { x with shared := { x.shared with path := !x.shared.path } } := by
  rcases x with
    ⟨core, ⟨coefficientAdder, correctionCounter, path, control⟩,
      target⟩
  rfl

/-- Carrier projection that forgets exactly the temporary correction index. -/
private def clearCorrectionIndex (n counterTail : Nat)
    (x : MK.Compact.Registers n (counterTail + 1)) :
    MK.Compact.Registers n (counterTail + 1) :=
  { x with shared := { x.shared with correctionCounter := 0 } }

/-- Loading a slot constant changes only the clean temporary correction
index. -/
private lemma correctionSlotLoadStep_state
    (fieldTail counterTail : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (slot : Fin fieldTail.succ)
    (base : MK.Compact.Registers fieldTail.succ (counterTail + 1))
    (coefficient : Word (fieldTail.succ + 1))
    (modulus : Word fieldTail.succ) :
    correctionSlotLoadStep fieldTail.succ counterTail hcapacity slot
        (correctionSlotState fieldTail counterTail base coefficient modulus
          0 false) =
      correctionSlotState fieldTail counterTail base coefficient modulus
        (correctionSlotLabel fieldTail.succ counterTail hcapacity slot)
        false := by
  let slotLabel := correctionSlotLabel fieldTail.succ counterTail hcapacity slot
  let input := correctionSlotState fieldTail counterTail base coefficient
    modulus 0 false
  let output := correctionSlotLoadStep fieldTail.succ counterTail hcapacity
    slot input
  let expected := correctionSlotState fieldTail counterTail base coefficient
    modulus slotLabel false
  have hframe :
      clearCorrectionIndex fieldTail.succ counterTail output =
        clearCorrectionIndex fieldTail.succ counterTail input := by
    change clearCorrectionIndex fieldTail.succ counterTail
        (EncodedBit.GateSpec.stepList
          (EncodedBit.Word.xorConstantGates
            (correctionCounterValueWord fieldTail.succ (counterTail + 1))
            slotLabel) input) = _
    apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    intro gate hgate
    rw [EncodedBit.Word.xorConstantGates] at hgate
    rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
    intro current
    rcases current with
      ⟨core, ⟨coefficientAdder, correctionCounter, path, control⟩,
        target⟩
    rfl
  have hcounter : output.shared.correctionCounter = slotLabel := by
    apply word_eq_of_testBit_eq
    intro bit
    rw [← correctionCounterValueBit_get fieldTail.succ
      (counterTail + 1) bit output]
    change
      ((correctionCounterValueWord fieldTail.succ
        (counterTail + 1)).bit bit).get output =
        slotLabel.val.testBit bit.val
    rw [show output = EncodedBit.Word.xorConstantStep
      (correctionCounterValueWord fieldTail.succ (counterTail + 1))
      slotLabel input by rfl]
    rw [EncodedBit.Word.xorConstantStep_get_target
      (correctionCounterValueWord fieldTail.succ (counterTail + 1))
      slotLabel bit
      (fun other hne => by
        simpa [correctionCounterValueWord,
          correctionCounterValueBit] using
          correctionCounterBit_wire_ne fieldTail.succ (counterTail + 1)
            (littleEndianWire_ne hne)) input]
    simp [input, correctionSlotState, doublingState, arithmeticState,
      cleanSharedWork, correctionCounterValueWord,
      correctionCounterValueBit]
  have hframeExpected :
      clearCorrectionIndex fieldTail.succ counterTail output =
        clearCorrectionIndex fieldTail.succ counterTail expected := by
    calc
      clearCorrectionIndex fieldTail.succ counterTail output =
          clearCorrectionIndex fieldTail.succ counterTail input := hframe
      _ = clearCorrectionIndex fieldTail.succ counterTail expected := by
        simp [clearCorrectionIndex, input, expected, correctionSlotState,
          slotLabel, doublingState, arithmeticState, cleanSharedWork]
  have hcore : output.core = expected.core := by
    have h := congrArg (fun x => x.core) hframeExpected
    simpa [clearCorrectionIndex] using h
  have hcoefficientAdder :
      output.shared.coefficientAdder = expected.shared.coefficientAdder := by
    have h := congrArg (fun x => x.shared.coefficientAdder) hframeExpected
    simpa [clearCorrectionIndex] using h
  have hpath : output.shared.path = expected.shared.path := by
    have h := congrArg (fun x => x.shared.path) hframeExpected
    simpa [clearCorrectionIndex] using h
  have hcontrol : output.shared.control = expected.shared.control := by
    have h := congrArg (fun x => x.shared.control) hframeExpected
    simpa [clearCorrectionIndex] using h
  have htarget : output.target = expected.target := by
    have h := congrArg (fun x => x.target) hframeExpected
    simpa [clearCorrectionIndex] using h
  have hexpectedCounter : expected.shared.correctionCounter = slotLabel := by
    simp [expected, correctionSlotState, doublingState, arithmeticState,
      cleanSharedWork]
  have hshared : output.shared = expected.shared := by
    apply (MK.Compact.sharedWorkTupleEquiv fieldTail.succ
      (counterTail + 1)).injective
    change (output.shared.coefficientAdder,
        (output.shared.correctionCounter,
          (output.shared.path, output.shared.control))) =
      (expected.shared.coefficientAdder,
        (expected.shared.correctionCounter,
          (expected.shared.path, expected.shared.control)))
    rw [hcoefficientAdder, hcounter, hpath, hcontrol, hexpectedCounter]
  change output = expected
  apply (MK.Compact.registerTupleEquiv fieldTail.succ
    (counterTail + 1)).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, htarget]

/-- One literal correction slot: load the static index, compute the
`index < count` selector, apply one controlled modular doubling, uncompute the
selector, and unload the index. -/
def correctionSlotGates (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (slot : Fin fieldTail.succ) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ (counterTail + 1))) :=
  correctionSlotLoadGates fieldTail.succ counterTail hcapacity slot ++
    correctionLtSelectorGates fieldTail.succ counterTail hwidth ++
    controlledDoublingGates fieldTail (counterTail + 1) p ++
    correctionLtSelectorGates fieldTail.succ counterTail hwidth ++
    correctionSlotUnloadGates fieldTail.succ counterTail hcapacity slot

/-- Circuit compiled from the five literal segments of one correction slot. -/
def correctionSlotProgram (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (slot : Fin fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ (counterTail + 1)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (correctionSlotGates fieldTail counterTail p hcapacity hwidth slot)

/-- Folded action of the five literal correction-slot segments. -/
def correctionSlotStep (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (slot : Fin fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 1) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionSlotGates fieldTail counterTail p hcapacity hwidth slot)

/-- The flattened correction slot executes load, select, controlled double,
unselect, and unload in source order. -/
lemma correctionSlotStep_eq_stages
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (slot : Fin fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 1)) :
    correctionSlotStep fieldTail counterTail p hcapacity hwidth slot x =
      correctionSlotUnloadStep fieldTail.succ counterTail hcapacity slot
        (correctionLtSelectorStep fieldTail.succ counterTail hwidth
          (controlledDoublingStep fieldTail (counterTail + 1) p
            (correctionLtSelectorStep fieldTail.succ counterTail hwidth
              (correctionSlotLoadStep fieldTail.succ counterTail hcapacity
                slot x)))) := by
  simp only [correctionSlotStep, correctionSlotGates,
    correctionSlotLoadStep, correctionSlotUnloadStep,
    correctionSlotUnloadGates, correctionLtSelectorStep,
    controlledDoublingStep, EncodedBit.GateSpec.stepList_append]

/-- One static slot doubles the reduced coefficient exactly when its public
index is below the runtime correction count.  Both selector invocations and
the constant unload restore the complete shared workspace. -/
lemma correctionSlotStep_state
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (slot : Fin fieldTail.succ)
    (base : MK.Compact.Registers fieldTail.succ (counterTail + 1))
    (coefficient : Word (fieldTail.succ + 1))
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) :
    correctionSlotStep fieldTail counterTail p hcapacity hwidth slot
        (correctionSlotState fieldTail counterTail base coefficient ⟨p, hp⟩
          0 false) =
      correctionSlotState fieldTail counterTail base
        (if slot.val < base.core.counter.val then
          doublingResidueWord fieldTail p hpPos hp coefficient
        else coefficient)
        ⟨p, hp⟩ 0 false := by
  let index := correctionSlotLabel fieldTail.succ counterTail hcapacity slot
  let reduced := doublingResidueWord fieldTail p hpPos hp coefficient
  let s0 := correctionSlotState fieldTail counterTail base coefficient ⟨p, hp⟩
    0 false
  let s1 := correctionSlotState fieldTail counterTail base coefficient ⟨p, hp⟩
    index false
  by_cases hselected : slot.val < base.core.counter.val
  · let s2 := correctionSlotState fieldTail counterTail base coefficient
      ⟨p, hp⟩ index true
    let s3 := correctionSlotState fieldTail counterTail base reduced ⟨p, hp⟩
      index true
    let s4 := correctionSlotState fieldTail counterTail base reduced ⟨p, hp⟩
      index false
    let s5 := correctionSlotState fieldTail counterTail base reduced ⟨p, hp⟩
      0 false
    have hs1 :
        correctionSlotLoadStep fieldTail.succ counterTail hcapacity slot s0 =
          s1 := by
      simpa [s0, s1, index] using
        correctionSlotLoadStep_state fieldTail counterTail hcapacity slot base
          coefficient ⟨p, hp⟩
    have hs2 :
        correctionLtSelectorStep fieldTail.succ counterTail hwidth s1 =
          s2 := by
      have hselector :=
        correctionLtSelectorStep_eq_conditional_path_flip_of_clean
          fieldTail.succ counterTail hwidth s1
          (by simp [s1, correctionSlotState, doublingState,
            arithmeticState, cleanSharedWork])
          (by simp [s1, correctionSlotState, doublingState,
            arithmeticState])
          (by
            intro bit
            simp [s1, correctionSlotState, doublingState,
              arithmeticState, cleanCoeffAdderWork,
              PlainAdder.Schedule.PowerOfTwo.cleanCarryWork])
      simpa [s1, s2, index, correctionSlotLabel, correctionSlotState,
        doublingState, arithmeticState, cleanSharedWork, hselected] using
        hselector
    have hs3 :
        controlledDoublingStep fieldTail (counterTail + 1) p s2 = s3 := by
      rw [controlledDoublingStep_eq_structured_of_clean]
      · rw [controlledDoublingStructuredStep, if_pos]
        · simpa [s2, s3, reduced, correctionSlotState] using
            doublingStep_state fieldTail (counterTail + 1) p
              { base with
                shared :=
                  { cleanSharedWork fieldTail.succ (counterTail + 1) with
                    correctionCounter := index
                    path := true } }
              coefficient hpPos hp hpOdd hcoefficient
        · simp [s2, correctionSlotState, doublingState, arithmeticState,
            cleanSharedWork]
      · simp [s2, correctionSlotState, doublingState, arithmeticState,
          cleanSharedWork]
    have hs4 :
        correctionLtSelectorStep fieldTail.succ counterTail hwidth s3 =
          s4 := by
      have hselector :=
        correctionLtSelectorStep_eq_conditional_path_flip_of_clean
          fieldTail.succ counterTail hwidth s3
          (by simp [s3, correctionSlotState, doublingState,
            arithmeticState, cleanSharedWork])
          (by simp [s3, correctionSlotState, doublingState,
            arithmeticState])
          (by
            intro bit
            simp [s3, correctionSlotState, doublingState,
              arithmeticState, cleanCoeffAdderWork,
              PlainAdder.Schedule.PowerOfTwo.cleanCarryWork])
      simpa [s3, s4, index, correctionSlotLabel, correctionSlotState,
        doublingState, arithmeticState, cleanSharedWork, hselected] using
        hselector
    have hs5 :
        correctionSlotUnloadStep fieldTail.succ counterTail hcapacity slot
            s4 = s5 := by
      have hcancel := correctionSlotUnloadStep_after_load fieldTail.succ
        counterTail hcapacity slot
        (correctionSlotState fieldTail counterTail base reduced ⟨p, hp⟩
          0 false)
      rw [correctionSlotLoadStep_state fieldTail counterTail hcapacity slot
        base reduced ⟨p, hp⟩] at hcancel
      simpa [s4, s5, index] using hcancel
    rw [correctionSlotStep_eq_stages, hs1, hs2, hs3, hs4, hs5]
    simp [s5, reduced, hselected]
  · let s2 := s1
    have hs1 :
        correctionSlotLoadStep fieldTail.succ counterTail hcapacity slot s0 =
          s1 := by
      simpa [s0, s1, index] using
        correctionSlotLoadStep_state fieldTail counterTail hcapacity slot base
          coefficient ⟨p, hp⟩
    have hs2 :
        correctionLtSelectorStep fieldTail.succ counterTail hwidth s1 =
          s2 := by
      have hselector :=
        correctionLtSelectorStep_eq_conditional_path_flip_of_clean
          fieldTail.succ counterTail hwidth s1
          (by simp [s1, correctionSlotState, doublingState,
            arithmeticState, cleanSharedWork])
          (by simp [s1, correctionSlotState, doublingState,
            arithmeticState])
          (by
            intro bit
            simp [s1, correctionSlotState, doublingState,
              arithmeticState, cleanCoeffAdderWork,
              PlainAdder.Schedule.PowerOfTwo.cleanCarryWork])
      simpa [s1, s2, index, correctionSlotLabel, correctionSlotState,
        doublingState, arithmeticState, cleanSharedWork, hselected] using
        hselector
    have hs3 :
        controlledDoublingStep fieldTail (counterTail + 1) p s2 = s2 := by
      rw [controlledDoublingStep_eq_structured_of_clean]
      · rw [controlledDoublingStructuredStep, if_neg]
        simp [s2, s1, correctionSlotState, doublingState, arithmeticState,
          cleanSharedWork]
      · simp [s2, s1, correctionSlotState, doublingState, arithmeticState,
          cleanSharedWork]
    have hs4 :
        correctionLtSelectorStep fieldTail.succ counterTail hwidth s2 =
          s2 := hs2
    have hs5 :
        correctionSlotUnloadStep fieldTail.succ counterTail hcapacity slot
            s2 = s0 := by
      have hcancel := correctionSlotUnloadStep_after_load fieldTail.succ
        counterTail hcapacity slot s0
      rw [hs1] at hcancel
      simpa [s2] using hcancel
    rw [correctionSlotStep_eq_stages, hs1, hs2, hs3, hs4, hs5]
    simp [s0, hselected]

/-- Every correction slot is realized directly by its flattened native gate
ledger. -/
lemma correctionSlot_realizes
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (slot : Fin fieldTail.succ) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ (counterTail + 1))
      (correctionSlotProgram fieldTail counterTail p hcapacity hwidth slot) environment
      (correctionSlotStep fieldTail counterTail p hcapacity hwidth slot) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (correctionSlotGates fieldTail counterTail p hcapacity hwidth slot)

/-! ## Complete fixed correction loop -/

/-- Flat native gate ledger for all `n` public correction slots. -/
def correctionLoopGates (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ (counterTail + 1))) :=
  (List.finRange fieldTail.succ).flatMap
    (correctionSlotGates fieldTail counterTail p hcapacity hwidth)

/-- Named semantic schedule corresponding pointwise to the static correction
slots. -/
def correctionLoopSteps (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    List (MK.Compact.Registers fieldTail.succ (counterTail + 1) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 1)) :=
  (List.finRange fieldTail.succ).map
    (correctionSlotStep fieldTail counterTail p hcapacity hwidth)

/-- Circuit compiled from the complete flat correction-loop ledger. -/
def correctionLoopProgram (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ (counterTail + 1)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (correctionLoopGates fieldTail counterTail p hcapacity hwidth)

/-- Folded action of the complete flat correction-loop ledger. -/
def correctionLoopStep (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 1) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionLoopGates fieldTail counterTail p hcapacity hwidth)

private lemma stepList_flatMap_correctionSlotGates
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    forall (slots : List (Fin fieldTail.succ))
      (x : MK.Compact.Registers fieldTail.succ (counterTail + 1)),
      EncodedBit.GateSpec.stepList
          (slots.flatMap
            (correctionSlotGates fieldTail counterTail p hcapacity hwidth)) x =
        UnitaryCircuit.Realizes.stepList
          (slots.map
            (correctionSlotStep fieldTail counterTail p hcapacity hwidth)) x
  | [], _ => rfl
  | slot :: rest, x => by
      change
        EncodedBit.GateSpec.stepList
            (correctionSlotGates fieldTail counterTail p hcapacity hwidth
                slot ++
              rest.flatMap
                (correctionSlotGates fieldTail counterTail p hcapacity
                  hwidth)) x =
          UnitaryCircuit.Realizes.stepList
            (rest.map
              (correctionSlotStep fieldTail counterTail p hcapacity hwidth))
            (correctionSlotStep fieldTail counterTail p hcapacity hwidth
              slot x)
      rw [EncodedBit.GateSpec.stepList_append]
      exact stepList_flatMap_correctionSlotGates fieldTail counterTail p
        hcapacity hwidth rest
        (correctionSlotStep fieldTail counterTail p hcapacity hwidth slot x)

/-- The flattened correction ledger and its named slot schedule have the same
state action. -/
lemma correctionLoopStep_eq_stepSchedule
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 1)) :
    correctionLoopStep fieldTail counterTail p hcapacity hwidth x =
      UnitaryCircuit.Realizes.stepList
        (correctionLoopSteps fieldTail counterTail p hcapacity hwidth) x := by
  exact stepList_flatMap_correctionSlotGates fieldTail counterTail p
    hcapacity hwidth (List.finRange fieldTail.succ) x

/-- The complete correction loop is realized directly by its flattened
native gate ledger. -/
lemma correctionLoop_realizes
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ (counterTail + 1))
      (correctionLoopProgram fieldTail counterTail p hcapacity hwidth) environment
      (correctionLoopStep fieldTail counterTail p hcapacity hwidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (correctionLoopGates fieldTail counterTail p hcapacity hwidth)

/-- Mathematical reduced coefficient after the first `rounds` static slots.
The runtime count is data, while `rounds` is the public schedule prefix. -/
def correctionResiduePrefix (fieldTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (count : Nat) : Nat -> Word (fieldTail.succ + 1) ->
      Word (fieldTail.succ + 1)
  | 0, coefficient => coefficient
  | rounds + 1, coefficient =>
      let prior := correctionResiduePrefix fieldTail p hpPos hp count
        rounds coefficient
      if rounds < count then
        doublingResidueWord fieldTail p hpPos hp prior
      else prior

/-- Every nonempty correction prefix remains reduced. -/
lemma correctionResiduePrefix_lt
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (count rounds : Nat)
    (coefficient : Word (fieldTail.succ + 1))
    (hcoefficient : coefficient.val < p) :
    (correctionResiduePrefix fieldTail p hpPos hp count rounds
      coefficient).val < p := by
  induction rounds with
  | zero => exact hcoefficient
  | succ rounds ih =>
      rw [correctionResiduePrefix]
      by_cases hselected : rounds < count
      · rw [if_pos hselected, doublingResidueWord_val]
        exact Nat.mod_lt _ hpPos
      · rw [if_neg hselected]
        exact ih

/-- The static prefix applies exactly the selected number of modular
doublings.  The `min` records that a public prefix shorter than the runtime
count can only execute the slots that physically exist. -/
lemma correctionResiduePrefix_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (count rounds : Nat)
    (coefficient : Word (fieldTail.succ + 1)) :
    ((correctionResiduePrefix fieldTail p hpPos hp count rounds
        coefficient).val : ZMod p) =
      (2 : ZMod p) ^ min count rounds * (coefficient.val : ZMod p) := by
  induction rounds with
  | zero => simp [correctionResiduePrefix]
  | succ rounds ih =>
      rw [correctionResiduePrefix]
      by_cases hselected : rounds < count
      · rw [if_pos hselected, doublingResidueWord_val,
          ZMod.natCast_mod, Nat.cast_mul, ih]
        have hmin : min count rounds = rounds := by omega
        have hminSucc : min count (rounds + 1) = rounds + 1 := by omega
        rw [hmin, hminSucc]
        have hpow : (2 : ZMod p) ^ (rounds + 1) =
            (2 : ZMod p) ^ rounds * 2 := by
          exact pow_succ 2 rounds
        rw [hpow]
        ring
      · rw [if_neg hselected, ih]
        have hmin : min count rounds = count := by omega
        have hminSucc : min count (rounds + 1) = count := by omega
        rw [hmin, hminSucc]

/-- Semantic action of a bounded prefix of the static correction schedule. -/
def correctionLoopPrefix (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) (rounds : Nat) :
    MK.Compact.Registers fieldTail.succ (counterTail + 1) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
  UnitaryCircuit.Realizes.stepList
    ((correctionLoopSteps fieldTail counterTail p hcapacity hwidth).take rounds)

private lemma correctionFinRange_take_succ
    {count : Nat} (slot : Fin count) :
    (List.finRange count).take (slot.val + 1) =
      (List.finRange count).take slot.val ++ [slot] := by
  have hindex : slot.val < (List.finRange count).length := by
    simpa only [List.length_finRange] using slot.isLt
  have hat : (List.finRange count)[slot.val]'hindex = slot := by
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  simpa only [hat] using
    (List.take_concat_get' (List.finRange count) slot.val hindex).symm

/-- Extending a correction prefix executes exactly the slot whose public
index is the old prefix length. -/
lemma correctionLoopPrefix_succ
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (rounds : Nat) (hrounds : rounds < fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 1)) :
    correctionLoopPrefix fieldTail counterTail p hcapacity hwidth
        (rounds + 1) x =
      correctionSlotStep fieldTail counterTail p hcapacity hwidth
        ⟨rounds, hrounds⟩
        (correctionLoopPrefix fieldTail counterTail p hcapacity hwidth
          rounds x) := by
  unfold correctionLoopPrefix correctionLoopSteps
  rw [← List.map_take, correctionFinRange_take_succ ⟨rounds, hrounds⟩,
    List.map_append, UnitaryCircuit.Realizes.stepList_append]
  rw [List.map_take]
  rfl

/-- Every bounded physical prefix implements the corresponding runtime-count
controlled modular-doubling recurrence and restores all borrowed wires. -/
lemma correctionLoopPrefix_state
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (base : MK.Compact.Registers fieldTail.succ (counterTail + 1))
    (coefficient : Word (fieldTail.succ + 1))
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p)
    (rounds : Nat) (hrounds : rounds <= fieldTail.succ) :
    correctionLoopPrefix fieldTail counterTail p hcapacity hwidth rounds
        (correctionSlotState fieldTail counterTail base coefficient ⟨p, hp⟩
          0 false) =
      correctionSlotState fieldTail counterTail base
        (correctionResiduePrefix fieldTail p hpPos hp
          base.core.counter.val rounds coefficient)
        ⟨p, hp⟩ 0 false := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      have hstrict : rounds < fieldTail.succ := by omega
      rw [correctionLoopPrefix_succ fieldTail counterTail p hcapacity hwidth
        rounds hstrict]
      rw [ih (by omega)]
      rw [correctionSlotStep_state fieldTail counterTail p hcapacity hwidth
        ⟨rounds, hstrict⟩ base
        (correctionResiduePrefix fieldTail p hpPos hp
          base.core.counter.val rounds coefficient)
        hpPos hp hpOdd]
      · rfl
      · exact correctionResiduePrefix_lt fieldTail p hpPos hp
          base.core.counter.val rounds coefficient hcoefficient

/-- Full-loop endpoint: the runtime correction count controls exactly the
public `n`-slot reduced-doubling recurrence, with the shared carrier clean. -/
lemma correctionLoopStep_state
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (base : MK.Compact.Registers fieldTail.succ (counterTail + 1))
    (coefficient : Word (fieldTail.succ + 1))
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) :
    correctionLoopStep fieldTail counterTail p hcapacity hwidth
        (correctionSlotState fieldTail counterTail base coefficient ⟨p, hp⟩
          0 false) =
      correctionSlotState fieldTail counterTail base
        (correctionResiduePrefix fieldTail p hpPos hp
          base.core.counter.val fieldTail.succ coefficient)
        ⟨p, hp⟩ 0 false := by
  rw [correctionLoopStep_eq_stepSchedule]
  have hprefix := correctionLoopPrefix_state fieldTail counterTail p
    hcapacity hwidth
    base coefficient hpPos hp hpOdd hcoefficient fieldTail.succ
    (Nat.le_refl _)
  have hall :
      (correctionLoopSteps fieldTail counterTail p hcapacity hwidth).take
          fieldTail.succ =
        correctionLoopSteps fieldTail counterTail p hcapacity hwidth := by
    apply (List.take_eq_self_iff _).mpr
    simp [correctionLoopSteps]
  rw [← hall]
  simpa [correctionLoopPrefix] using hprefix

/-! ## Reversible compact correction endpoint -/

/-- Canonical clean boundary for the post-fold correction phase.  It retains
only the fold history and padding counter from `base`; the public target is an
explicit caller-owned input. -/
def correctionBoundaryState (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (modulus target : Word fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ counterWidth :=
  doublingState fieldTail counterWidth
    { base with
      core := { base.core with scratchB := false }
      shared := cleanSharedWork fieldTail.succ counterWidth
      target := target }
    coefficient (widenFixedWord fieldTail.succ 0) 0 modulus false

@[simp] lemma correctionBoundaryState_update_base_target
    (fieldTail counterWidth : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (modulus target : Word fieldTail.succ) :
    correctionBoundaryState fieldTail counterWidth
        { base with target := target } coefficient modulus target =
      correctionBoundaryState fieldTail counterWidth base coefficient modulus
        target := by
  rfl

/-- Reverse action of the static correction loop. -/
def correctionLoopReverseStep
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 1) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (correctionLoopGates fieldTail counterTail p hcapacity hwidth).reverse

/-- Reverse action of the initial coefficient reduction. -/
def coefficientReduceReverseStep (fieldTail counterWidth p : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (coefficientReduceGates fieldTail counterWidth p).reverse

/-- Literal compact correction ledger.  The coefficient reduction and
runtime-count doubling loop are uncomputed after the public target update, so
the fold history and every borrowed work bit return to their input values. -/
def compactCorrectionGates
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ (counterTail + 1))) :=
  coefficientReduceGates fieldTail (counterTail + 1) p ++
    correctionLoopGates fieldTail counterTail p hcapacity hwidth ++
    targetUpdateGates fieldTail (counterTail + 1) p ++
    (correctionLoopGates fieldTail counterTail p hcapacity hwidth).reverse ++
    (coefficientReduceGates fieldTail (counterTail + 1) p).reverse

/-! ## Native-gate ledger -/

/-- Hamming weight of the widened public modulus label used by every
controlled modulus xor. -/
def modulusOneCount (fieldTail p : Nat) : Nat :=
  (EncodedBit.Word.constantOneIndices
    (modulusWordLabel fieldTail p)).length

/-- Hamming weight of one public correction-slot label. -/
def correctionSlotOneCount
    (n counterTail : Nat) (hcapacity : n <= 2 ^ counterTail)
    (slot : Fin n) : Nat :=
  (EncodedBit.Word.constantOneIndices
    (correctionSlotLabel n counterTail hcapacity slot)).length

/-- Total Hamming weight of the public correction-slot labels. -/
def correctionSlotOneCountSum
    (n counterTail : Nat) (hcapacity : n <= 2 ^ counterTail) : Nat :=
  ((List.finRange n).map fun slot =>
    correctionSlotOneCount n counterTail hcapacity slot).sum

private lemma arithmeticAdderGates_resource
    (fieldTail counterWidth : Nat) :
    ((arithmeticAdderGates fieldTail counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 ∧
      ((arithmeticAdderGates fieldTail counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (fieldTail.succ + 1) ∧
      ((arithmeticAdderGates fieldTail counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * fieldTail.succ ∧
      (arithmeticAdderGates fieldTail counterWidth).length =
        8 * fieldTail.succ + 2 := by
  constructor
  · simpa [arithmeticAdderGates] using
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
        (arithmeticLayout fieldTail counterWidth)
  constructor
  · simpa [arithmeticAdderGates] using
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
        (arithmeticLayout fieldTail counterWidth)
  constructor
  · simpa [arithmeticAdderGates] using
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
        (arithmeticLayout fieldTail counterWidth)
  · have h :=
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length
        (arithmeticLayout fieldTail counterWidth)
    change (arithmeticAdderGates fieldTail counterWidth).length = _ at h
    omega

private lemma sourceSwapGates_resource
    (fieldTail counterWidth : Nat) :
    ((sourceSwapGates fieldTail counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 ∧
      ((sourceSwapGates fieldTail counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * fieldTail.succ ∧
      ((sourceSwapGates fieldTail counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 ∧
      (sourceSwapGates fieldTail counterWidth).length = 3 * fieldTail.succ := by
  have hlength := EncodedBit.Word.swapGates_length
    (activeSourceLowWord fieldTail counterWidth)
    (parkedModulusWord fieldTail counterWidth)
    (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
  have hcnot := EncodedBit.Word.swapGates_cnotMultiplicity_sum
    (activeSourceLowWord fieldTail counterWidth)
    (parkedModulusWord fieldTail counterWidth)
    (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
  have htoffoli := EncodedBit.Word.swapGates_toffoliMultiplicity_sum
    (activeSourceLowWord fieldTail counterWidth)
    (parkedModulusWord fieldTail counterWidth)
    (fun bit => activeSourceLow_parked_ne fieldTail counterWidth bit bit)
  change (sourceSwapGates fieldTail counterWidth).length = _ at hlength
  change ((sourceSwapGates fieldTail counterWidth).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hcnot
  change ((sourceSwapGates fieldTail counterWidth).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at htoffoli
  have htotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (sourceSwapGates fieldTail counterWidth)
  omega

private lemma targetSwapGates_resource (n counterWidth : Nat) :
    ((targetSwapGates n counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 ∧
      ((targetSwapGates n counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * n ∧
      ((targetSwapGates n counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 ∧
      (targetSwapGates n counterWidth).length = 3 * n := by
  have hlength := EncodedBit.Word.swapGates_length
    (targetValueWord n counterWidth) (uValueWord n counterWidth)
    (fun bit => publicTarget_arithmeticTargetLow_ne n counterWidth bit bit)
  have hcnot := EncodedBit.Word.swapGates_cnotMultiplicity_sum
    (targetValueWord n counterWidth) (uValueWord n counterWidth)
    (fun bit => publicTarget_arithmeticTargetLow_ne n counterWidth bit bit)
  have htoffoli := EncodedBit.Word.swapGates_toffoliMultiplicity_sum
    (targetValueWord n counterWidth) (uValueWord n counterWidth)
    (fun bit => publicTarget_arithmeticTargetLow_ne n counterWidth bit bit)
  change (targetSwapGates n counterWidth).length = _ at hlength
  change ((targetSwapGates n counterWidth).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hcnot
  change ((targetSwapGates n counterWidth).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at htoffoli
  have htotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (targetSwapGates n counterWidth)
  omega

private lemma coefficientLoadGates_resource (n counterWidth : Nat) :
    ((coefficientLoadGates n counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 ∧
      ((coefficientLoadGates n counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = n ∧
      ((coefficientLoadGates n counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 ∧
      (coefficientLoadGates n counterWidth).length = n := by
  have hlength := EncodedBit.Word.xorIntoGates_length
    (correctedValueWord n counterWidth) (vValueWord n counterWidth)
    (fun bit => correctedValue_activeSourceLow_ne n counterWidth bit bit)
  have hcnot := EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    (correctedValueWord n counterWidth) (vValueWord n counterWidth)
    (fun bit => correctedValue_activeSourceLow_ne n counterWidth bit bit)
  have htoffoli := EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum
    (correctedValueWord n counterWidth) (vValueWord n counterWidth)
    (fun bit => correctedValue_activeSourceLow_ne n counterWidth bit bit)
  change (coefficientLoadGates n counterWidth).length = _ at hlength
  change ((coefficientLoadGates n counterWidth).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hcnot
  change ((coefficientLoadGates n counterWidth).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at htoffoli
  have htotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (coefficientLoadGates n counterWidth)
  omega

private lemma modularReduceGates_resource
    (fieldTail counterWidth p : Nat) :
    ((modularReduceGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 ∧
      ((modularReduceGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
          16 * fieldTail.succ + 12 + 2 * modulusOneCount fieldTail p ∧
      ((modularReduceGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          30 * fieldTail.succ ∧
      (modularReduceGates fieldTail counterWidth p).length =
        46 * fieldTail.succ + 13 + 2 * modulusOneCount fieldTail p := by
  rcases arithmeticAdderGates_resource fieldTail counterWidth with
    ⟨hax, hac, hat, hal⟩
  rcases sourceSwapGates_resource fieldTail counterWidth with
    ⟨hsx, hsc, hst, hsl⟩
  have hclearLength := EncodedBit.Word.controlledXorConstantGates_length
    (scratchABit fieldTail.succ counterWidth)
    (activeSourceWord fieldTail counterWidth)
    (modulusWordLabel fieldTail p)
    (reductionFlag_activeSource_ne fieldTail counterWidth)
  have hclearX := EncodedBit.Word.controlledXorConstantGates_xMultiplicity_sum
    (scratchABit fieldTail.succ counterWidth)
    (activeSourceWord fieldTail counterWidth)
    (modulusWordLabel fieldTail p)
    (reductionFlag_activeSource_ne fieldTail counterWidth)
  have hclearC := EncodedBit.Word.controlledXorConstantGates_cnotMultiplicity_sum
    (scratchABit fieldTail.succ counterWidth)
    (activeSourceWord fieldTail counterWidth)
    (modulusWordLabel fieldTail p)
    (reductionFlag_activeSource_ne fieldTail counterWidth)
  have hclearT := EncodedBit.Word.controlledXorConstantGates_toffoliMultiplicity_sum
    (scratchABit fieldTail.succ counterWidth)
    (activeSourceWord fieldTail counterWidth)
    (modulusWordLabel fieldTail p)
    (reductionFlag_activeSource_ne fieldTail counterWidth)
  change (clearActiveModulusGates fieldTail counterWidth p).length = _ at hclearLength
  change ((clearActiveModulusGates fieldTail counterWidth p).map
    EncodedBit.GateSpec.xMultiplicity).sum = _ at hclearX
  change ((clearActiveModulusGates fieldTail counterWidth p).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hclearC
  change ((clearActiveModulusGates fieldTail counterWidth p).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at hclearT
  simp only [modularReduceGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse, List.length_append,
    List.length_reverse, copyReductionFlagGates,
    cleanupReductionFlagGates, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil,
    EncodedBit.GateSpec.xMultiplicity_x,
    EncodedBit.GateSpec.xMultiplicity_cnot,
    EncodedBit.GateSpec.cnotMultiplicity_x,
    EncodedBit.GateSpec.cnotMultiplicity_cnot,
    EncodedBit.GateSpec.toffoliMultiplicity_x,
    EncodedBit.GateSpec.toffoliMultiplicity_cnot,
    restoreActiveModulusGates]
  simp only [hax, hac, hat, hal, hsx, hsc, hst, hsl,
    hclearX, hclearC, hclearT, hclearLength, modulusOneCount]
  constructor
  · simp
  constructor
  · omega
  constructor <;> omega

private lemma modularSubtractGates_resource
    (fieldTail counterWidth p : Nat) :
    ((modularSubtractGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 ∧
      ((modularSubtractGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
          16 * fieldTail.succ + 12 + 2 * modulusOneCount fieldTail p ∧
      ((modularSubtractGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          30 * fieldTail.succ ∧
      (modularSubtractGates fieldTail counterWidth p).length =
        46 * fieldTail.succ + 13 + 2 * modulusOneCount fieldTail p := by
  simpa only [modularSubtractGates, List.map_reverse, List.sum_reverse,
    List.length_reverse] using
    modularReduceGates_resource fieldTail counterWidth p

private lemma doublingGates_resource
    (fieldTail counterWidth p : Nat) :
    ((doublingGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 ∧
      ((doublingGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
          25 * fieldTail.succ + 19 + 2 * modulusOneCount fieldTail p ∧
      ((doublingGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          30 * fieldTail.succ ∧
      (doublingGates fieldTail counterWidth p).length =
        55 * fieldTail.succ + 20 + 2 * modulusOneCount fieldTail p := by
  rcases modularReduceGates_resource fieldTail counterWidth p with
    ⟨hrx, hrc, hrt, hrl⟩
  have hswapLength := EncodedBit.Word.swapGates_length
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
  have hswapC := EncodedBit.Word.swapGates_cnotMultiplicity_sum
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
  have hswapT := EncodedBit.Word.swapGates_toffoliMultiplicity_sum
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
  change (doublingSwapGates fieldTail counterWidth).length = _ at hswapLength
  change ((doublingSwapGates fieldTail counterWidth).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hswapC
  change ((doublingSwapGates fieldTail counterWidth).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at hswapT
  have hswapTotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (doublingSwapGates fieldTail counterWidth)
  have hswapX : ((doublingSwapGates fieldTail counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by omega
  have hshiftLength := EncodedBit.Word.adjacentShiftRightGates_length
    (arithmeticTargetWord fieldTail counterWidth)
    (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)
  have hshiftX := EncodedBit.Word.adjacentShiftRightGates_xMultiplicity_sum
    (arithmeticTargetWord fieldTail counterWidth)
    (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)
  have hshiftC := EncodedBit.Word.adjacentShiftRightGates_cnotMultiplicity_sum
    (arithmeticTargetWord fieldTail counterWidth)
    (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)
  have hshiftT := EncodedBit.Word.adjacentShiftRightGates_toffoliMultiplicity_sum
    (arithmeticTargetWord fieldTail counterWidth)
    (arithmeticTargetWord_pairwise_ne fieldTail counterWidth)
  change (doublingShiftGates fieldTail counterWidth).length = _ at hshiftLength
  change ((doublingShiftGates fieldTail counterWidth).map
    EncodedBit.GateSpec.xMultiplicity).sum = _ at hshiftX
  change ((doublingShiftGates fieldTail counterWidth).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hshiftC
  change ((doublingShiftGates fieldTail counterWidth).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at hshiftT
  simp only [doublingGates, List.map_append, List.sum_append,
    List.length_append, doublingCleanupGates, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    EncodedBit.GateSpec.xMultiplicity_cnot,
    EncodedBit.GateSpec.cnotMultiplicity_cnot,
    EncodedBit.GateSpec.toffoliMultiplicity_cnot]
  simp only [hrx, hrc, hrt, hrl, hswapLength, hswapX, hswapC, hswapT,
    hshiftLength, hshiftX, hshiftC, hshiftT]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- Exact primitive length of one reusable modular-doubling ledger. -/
lemma doublingGates_length
    (fieldTail counterWidth p : Nat) :
    (doublingGates fieldTail counterWidth p).length =
      55 * fieldTail.succ + 20 + 2 * modulusOneCount fieldTail p :=
  (doublingGates_resource fieldTail counterWidth p).2.2.2

/-- Public-constant-independent length bound for one modular doubling. -/
lemma doublingGates_length_le
    (fieldTail counterWidth p : Nat) :
    (doublingGates fieldTail counterWidth p).length ≤
      57 * fieldTail.succ + 22 := by
  rw [doublingGates_length]
  have h : modulusOneCount fieldTail p ≤ fieldTail.succ + 1 := by
    simpa [modulusOneCount] using
      EncodedBit.Word.constantOneIndices_length_le
        (modulusWordLabel fieldTail p)
  omega

private lemma controlledDoublingGates_resource
    (fieldTail counterWidth p : Nat) :
    ((controlledDoublingGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 ∧
      ((controlledDoublingGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 ∧
      ((controlledDoublingGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          115 * fieldTail.succ + 19 + 2 * modulusOneCount fieldTail p ∧
      (controlledDoublingGates fieldTail counterWidth p).length =
        115 * fieldTail.succ + 20 + 2 * modulusOneCount fieldTail p := by
  rcases doublingGates_resource fieldTail counterWidth p with
    ⟨hx, hc, ht, hl⟩
  have houtX := EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum
    (pathBit fieldTail.succ counterWidth)
    (controlBit fieldTail.succ counterWidth)
    (doublingGates fieldTail counterWidth p)
    (doublingGates_bitDisjoint_path fieldTail counterWidth p)
    (doublingGates_bitDisjoint_control fieldTail counterWidth p)
    (pathBit_controlBit_wire_ne fieldTail.succ counterWidth)
  have houtC := EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum
    (pathBit fieldTail.succ counterWidth)
    (controlBit fieldTail.succ counterWidth)
    (doublingGates fieldTail counterWidth p)
    (doublingGates_bitDisjoint_path fieldTail counterWidth p)
    (doublingGates_bitDisjoint_control fieldTail counterWidth p)
    (pathBit_controlBit_wire_ne fieldTail.succ counterWidth)
  have houtT := EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum
    (pathBit fieldTail.succ counterWidth)
    (controlBit fieldTail.succ counterWidth)
    (doublingGates fieldTail counterWidth p)
    (doublingGates_bitDisjoint_path fieldTail counterWidth p)
    (doublingGates_bitDisjoint_control fieldTail counterWidth p)
    (pathBit_controlBit_wire_ne fieldTail.succ counterWidth)
  have houtLength := EncodedBit.GateSpec.controlledListWithWorkGates_length_eq
    (pathBit fieldTail.succ counterWidth)
    (controlBit fieldTail.succ counterWidth)
    (doublingGates fieldTail counterWidth p)
    (doublingGates_bitDisjoint_path fieldTail counterWidth p)
    (doublingGates_bitDisjoint_control fieldTail counterWidth p)
    (pathBit_controlBit_wire_ne fieldTail.succ counterWidth)
  change ((controlledDoublingGates fieldTail counterWidth p).map
    EncodedBit.GateSpec.xMultiplicity).sum = _ at houtX
  change ((controlledDoublingGates fieldTail counterWidth p).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at houtC
  change ((controlledDoublingGates fieldTail counterWidth p).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at houtT
  change (controlledDoublingGates fieldTail counterWidth p).length = _ at houtLength
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

private lemma coefficientReduceGates_resource
    (fieldTail counterWidth p : Nat) :
    ((coefficientReduceGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 ∧
      ((coefficientReduceGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
          22 * fieldTail.succ + 21 + 2 * modulusOneCount fieldTail p ∧
      ((coefficientReduceGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          30 * fieldTail.succ ∧
      (coefficientReduceGates fieldTail counterWidth p).length =
        52 * fieldTail.succ + 22 + 2 * modulusOneCount fieldTail p := by
  rcases modularReduceGates_resource fieldTail counterWidth p with
    ⟨hrx, hrc, hrt, hrl⟩
  have hswapLength := EncodedBit.Word.swapGates_length
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
  have hswapC := EncodedBit.Word.swapGates_cnotMultiplicity_sum
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
  have hswapT := EncodedBit.Word.swapGates_toffoliMultiplicity_sum
    (rCoeffValueWord fieldTail.succ counterWidth)
    (arithmeticTargetWord fieldTail counterWidth)
    (fun bit => rCoeff_target_ne fieldTail counterWidth bit bit)
  change (doublingSwapGates fieldTail counterWidth).length = _ at hswapLength
  change ((doublingSwapGates fieldTail counterWidth).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hswapC
  change ((doublingSwapGates fieldTail counterWidth).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at hswapT
  have hswapTotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (doublingSwapGates fieldTail counterWidth)
  have hswapX : ((doublingSwapGates fieldTail counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by omega
  have hparkLength : (reductionFlagParkGates fieldTail.succ counterWidth).length =
      3 := by simp [reductionFlagParkGates, EncodedBit.swapGates]
  have hparkX : ((reductionFlagParkGates fieldTail.succ counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
    simp [reductionFlagParkGates, EncodedBit.swapGates]
  have hparkC : ((reductionFlagParkGates fieldTail.succ counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 := by
    simp [reductionFlagParkGates, EncodedBit.swapGates]
  have hparkT : ((reductionFlagParkGates fieldTail.succ counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
    simp [reductionFlagParkGates, EncodedBit.swapGates]
  simp only [coefficientReduceGates, List.map_append, List.sum_append,
    List.length_append, hrx, hrc, hrt, hrl, hswapLength, hswapX, hswapC,
    hswapT, hparkLength, hparkX, hparkC, hparkT]
  constructor
  · simp
  constructor
  · omega
  constructor <;> omega

private lemma targetUpdateGates_resource
    (fieldTail counterWidth p : Nat) :
    ((targetUpdateGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 ∧
      ((targetUpdateGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
          24 * fieldTail.succ + 12 + 2 * modulusOneCount fieldTail p ∧
      ((targetUpdateGates fieldTail counterWidth p).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          30 * fieldTail.succ ∧
      (targetUpdateGates fieldTail counterWidth p).length =
        54 * fieldTail.succ + 13 + 2 * modulusOneCount fieldTail p := by
  rcases targetSwapGates_resource fieldTail.succ counterWidth with
    ⟨hsx, hsc, hst, hsl⟩
  rcases coefficientLoadGates_resource fieldTail.succ counterWidth with
    ⟨hlx, hlc, hlt, hll⟩
  rcases modularSubtractGates_resource fieldTail counterWidth p with
    ⟨hrx, hrc, hrt, hrl⟩
  simp only [targetUpdateGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse, List.length_append,
    List.length_reverse, hsx, hsc, hst, hsl, hlx, hlc, hlt, hll,
    hrx, hrc, hrt, hrl]
  constructor
  · simp
  constructor
  · omega
  constructor <;> omega

/-- Exact primitive length of the reusable public-target update ledger. -/
lemma targetUpdateGates_length
    (fieldTail counterWidth p : Nat) :
    (targetUpdateGates fieldTail counterWidth p).length =
      54 * fieldTail.succ + 13 + 2 * modulusOneCount fieldTail p :=
  (targetUpdateGates_resource fieldTail counterWidth p).2.2.2

/-- Public-constant-independent length bound for one target update. -/
lemma targetUpdateGates_length_le
    (fieldTail counterWidth p : Nat) :
    (targetUpdateGates fieldTail counterWidth p).length ≤
      56 * fieldTail.succ + 15 := by
  rw [targetUpdateGates_length]
  have h : modulusOneCount fieldTail p ≤ fieldTail.succ + 1 := by
    simpa [modulusOneCount] using
      EncodedBit.Word.constantOneIndices_length_le
        (modulusWordLabel fieldTail p)
  omega

private lemma correctionLtSelectorGates_resource
    (n counterTail : Nat) (hwidth : counterTail + 1 <= n) :
    ((correctionLtSelectorGates n counterTail hwidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 4 * (counterTail + 1) ∧
      ((correctionLtSelectorGates n counterTail hwidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 ∧
      ((correctionLtSelectorGates n counterTail hwidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          6 * (counterTail + 1) ∧
      (correctionLtSelectorGates n counterTail hwidth).length =
        10 * (counterTail + 1) + 1 := by
  have hborrowX :=
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_xMultiplicity_sum
      (correctionLtBorrowLayout n counterTail hwidth)
  have hborrowC :=
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_cnotMultiplicity_sum
      (correctionLtBorrowLayout n counterTail hwidth)
  have hborrowT :=
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_toffoliMultiplicity_sum
      (correctionLtBorrowLayout n counterTail hwidth)
  have hborrowLength :=
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_length
      (correctionLtBorrowLayout n counterTail hwidth)
  change ((correctionLtBorrowGates n counterTail hwidth).map
    EncodedBit.GateSpec.xMultiplicity).sum = _ at hborrowX
  change ((correctionLtBorrowGates n counterTail hwidth).map
    EncodedBit.GateSpec.cnotMultiplicity).sum = _ at hborrowC
  change ((correctionLtBorrowGates n counterTail hwidth).map
    EncodedBit.GateSpec.toffoliMultiplicity).sum = _ at hborrowT
  change (correctionLtBorrowGates n counterTail hwidth).length = _ at hborrowLength
  simp only [correctionLtSelectorGates, correctionLtCopyGate,
    List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse, List.length_append,
    List.length_reverse, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil,
    EncodedBit.GateSpec.xMultiplicity_cnot,
    EncodedBit.GateSpec.cnotMultiplicity_cnot,
    EncodedBit.GateSpec.toffoliMultiplicity_cnot,
    hborrowX, hborrowC, hborrowT, hborrowLength]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

private lemma correctionSlotLoadGates_resource
    (n counterTail : Nat) (hcapacity : n <= 2 ^ counterTail)
    (slot : Fin n) :
    ((correctionSlotLoadGates n counterTail hcapacity slot).map
        EncodedBit.GateSpec.xMultiplicity).sum =
          correctionSlotOneCount n counterTail hcapacity slot ∧
      ((correctionSlotLoadGates n counterTail hcapacity slot).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 0 ∧
      ((correctionSlotLoadGates n counterTail hcapacity slot).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 ∧
      (correctionSlotLoadGates n counterTail hcapacity slot).length =
        correctionSlotOneCount n counterTail hcapacity slot := by
  constructor
  · simpa [correctionSlotLoadGates, correctionSlotOneCount] using
      EncodedBit.Word.xorConstantGates_xMultiplicity_sum
        (correctionCounterValueWord n (counterTail + 1))
        (correctionSlotLabel n counterTail hcapacity slot)
  constructor
  · simpa [correctionSlotLoadGates] using
      EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum
        (correctionCounterValueWord n (counterTail + 1))
        (correctionSlotLabel n counterTail hcapacity slot)
  constructor
  · simpa [correctionSlotLoadGates] using
      EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum
        (correctionCounterValueWord n (counterTail + 1))
        (correctionSlotLabel n counterTail hcapacity slot)
  · simpa [correctionSlotLoadGates, correctionSlotOneCount] using
      EncodedBit.Word.xorConstantGates_length
        (correctionCounterValueWord n (counterTail + 1))
        (correctionSlotLabel n counterTail hcapacity slot)

private lemma correctionSlotGates_resource
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (slot : Fin fieldTail.succ) :
    ((correctionSlotGates fieldTail counterTail p hcapacity hwidth slot).map
        EncodedBit.GateSpec.xMultiplicity).sum =
          2 * correctionSlotOneCount fieldTail.succ counterTail hcapacity slot +
            8 * (counterTail + 1) ∧
      ((correctionSlotGates fieldTail counterTail p hcapacity hwidth slot).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 ∧
      ((correctionSlotGates fieldTail counterTail p hcapacity hwidth slot).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          115 * fieldTail.succ + 12 * (counterTail + 1) + 19 +
            2 * modulusOneCount fieldTail p ∧
      (correctionSlotGates fieldTail counterTail p hcapacity hwidth slot).length =
        2 * correctionSlotOneCount fieldTail.succ counterTail hcapacity slot +
          20 * (counterTail + 1) + 115 * fieldTail.succ + 22 +
            2 * modulusOneCount fieldTail p := by
  rcases correctionSlotLoadGates_resource fieldTail.succ counterTail
      hcapacity slot with ⟨hlx, hlc, hlt, hll⟩
  rcases correctionLtSelectorGates_resource fieldTail.succ counterTail
      hwidth with ⟨hsx, hsc, hst, hsl⟩
  rcases controlledDoublingGates_resource fieldTail (counterTail + 1) p with
    ⟨hdx, hdc, hdt, hdl⟩
  simp only [correctionSlotGates, correctionSlotUnloadGates,
    List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse, List.length_append,
    List.length_reverse, hlx, hlc, hlt, hll, hsx, hsc, hst, hsl,
    hdx, hdc, hdt, hdl]
  constructor
  · ring
  constructor
  · simp
  constructor <;> ring

private lemma flatMap_correctionSlotGates_resource
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    ∀ slots : List (Fin fieldTail.succ),
      (((slots.flatMap
          (correctionSlotGates fieldTail counterTail p hcapacity hwidth)).map
          EncodedBit.GateSpec.xMultiplicity).sum =
        2 * (slots.map fun slot =>
          correctionSlotOneCount fieldTail.succ counterTail hcapacity slot).sum +
          8 * slots.length * (counterTail + 1)) ∧
      (((slots.flatMap
          (correctionSlotGates fieldTail counterTail p hcapacity hwidth)).map
          EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * slots.length) ∧
      (((slots.flatMap
          (correctionSlotGates fieldTail counterTail p hcapacity hwidth)).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum =
        slots.length * (115 * fieldTail.succ + 12 * (counterTail + 1) + 19 +
          2 * modulusOneCount fieldTail p)) ∧
      ((slots.flatMap
          (correctionSlotGates fieldTail counterTail p hcapacity hwidth)).length =
        2 * (slots.map fun slot =>
          correctionSlotOneCount fieldTail.succ counterTail hcapacity slot).sum +
          slots.length * (20 * (counterTail + 1) + 115 * fieldTail.succ + 22 +
            2 * modulusOneCount fieldTail p)) := by
  intro slots
  induction slots with
  | nil => simp
  | cons slot rest ih =>
      rcases correctionSlotGates_resource fieldTail counterTail p hcapacity
        hwidth slot with ⟨hx, hc, ht, hl⟩
      rcases ih with ⟨ihx, ihc, iht, ihl⟩
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, List.length_cons, List.length_append,
        hx, hc, ht, hl, ihx, ihc, iht, ihl]
      constructor
      · ring
      constructor
      · omega
      constructor <;> ring

private lemma correctionLoopGates_resource
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    ((correctionLoopGates fieldTail counterTail p hcapacity hwidth).map
        EncodedBit.GateSpec.xMultiplicity).sum =
          2 * correctionSlotOneCountSum fieldTail.succ counterTail hcapacity +
            8 * fieldTail.succ * (counterTail + 1) ∧
      ((correctionLoopGates fieldTail counterTail p hcapacity hwidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * fieldTail.succ ∧
      ((correctionLoopGates fieldTail counterTail p hcapacity hwidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          fieldTail.succ * (115 * fieldTail.succ +
            12 * (counterTail + 1) + 19 + 2 * modulusOneCount fieldTail p) ∧
      (correctionLoopGates fieldTail counterTail p hcapacity hwidth).length =
        2 * correctionSlotOneCountSum fieldTail.succ counterTail hcapacity +
          fieldTail.succ * (20 * (counterTail + 1) +
            115 * fieldTail.succ + 22 + 2 * modulusOneCount fieldTail p) := by
  simpa only [correctionLoopGates, correctionSlotOneCountSum,
    List.length_finRange] using
    flatMap_correctionSlotGates_resource fieldTail counterTail p hcapacity
      hwidth (List.finRange fieldTail.succ)

/-- Exact native-gate ledger for the complete reversible correction.  The
two Hamming-weight terms retain the real public constants rather than hiding
them behind unconnected resource metadata. -/
lemma compactCorrectionGates_resource
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    ((compactCorrectionGates fieldTail counterTail p hcapacity hwidth).map
        EncodedBit.GateSpec.xMultiplicity).sum =
          4 * correctionSlotOneCountSum fieldTail.succ counterTail hcapacity +
            16 * fieldTail.succ * (counterTail + 1) + 3 ∧
      ((compactCorrectionGates fieldTail counterTail p hcapacity hwidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
          74 * fieldTail.succ + 54 + 6 * modulusOneCount fieldTail p ∧
      ((compactCorrectionGates fieldTail counterTail p hcapacity hwidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          2 * fieldTail.succ * (115 * fieldTail.succ +
            12 * (counterTail + 1) + 19 + 2 * modulusOneCount fieldTail p) +
            90 * fieldTail.succ ∧
      (compactCorrectionGates fieldTail counterTail p hcapacity hwidth).length =
        4 * correctionSlotOneCountSum fieldTail.succ counterTail hcapacity +
          230 * fieldTail.succ * fieldTail.succ +
          40 * fieldTail.succ * (counterTail + 1) +
          202 * fieldTail.succ +
          4 * fieldTail.succ * modulusOneCount fieldTail p +
          6 * modulusOneCount fieldTail p + 57 := by
  rcases coefficientReduceGates_resource fieldTail (counterTail + 1) p with
    ⟨hrx, hrc, hrt, hrl⟩
  rcases correctionLoopGates_resource fieldTail counterTail p hcapacity
      hwidth with ⟨hlx, hlc, hlt, hll⟩
  rcases targetUpdateGates_resource fieldTail (counterTail + 1) p with
    ⟨htx, htc, htt, htl⟩
  simp only [compactCorrectionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse, List.length_append,
    List.length_reverse, hrx, hrc, hrt, hrl, hlx, hlc, hlt, hll,
    htx, htc, htt, htl]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The widened modulus label has at most one selected position per physical
bit. -/
lemma modulusOneCount_le (fieldTail p : Nat) :
    modulusOneCount fieldTail p <= fieldTail.succ + 1 := by
  simpa [modulusOneCount] using
    EncodedBit.Word.constantOneIndices_length_le
      (modulusWordLabel fieldTail p)

/-- One static correction-slot label has at most `counterTail` selected
positions. -/
lemma correctionSlotOneCount_le
    (n counterTail : Nat) (hcapacity : n <= 2 ^ counterTail)
    (slot : Fin n) :
    correctionSlotOneCount n counterTail hcapacity slot <= counterTail := by
  simpa [correctionSlotOneCount] using
    EncodedBit.Word.constantOneIndices_length_le
      (correctionSlotLabel n counterTail hcapacity slot)

private lemma correctionSlotOneCount_sum_le_aux
    (n counterTail : Nat) (hcapacity : n <= 2 ^ counterTail) :
    forall slots : List (Fin n),
      (slots.map fun slot =>
        correctionSlotOneCount n counterTail hcapacity slot).sum <=
          slots.length * counterTail
  | [] => by simp
  | slot :: rest => by
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      have hslot := correctionSlotOneCount_le n counterTail hcapacity slot
      have hrest := correctionSlotOneCount_sum_le_aux n counterTail
        hcapacity rest
      omega

/-- Across all `n` public correction slots, the total loaded Hamming weight is
bounded by `n * counterTail`. -/
lemma correctionSlotOneCountSum_le
    (n counterTail : Nat) (hcapacity : n <= 2 ^ counterTail) :
    correctionSlotOneCountSum n counterTail hcapacity <= n * counterTail := by
  simpa [correctionSlotOneCountSum] using
    correctionSlotOneCount_sum_le_aux n counterTail hcapacity
      (List.finRange n)

/-- Public-constant-independent Toffoli bound derived from the exact native
correction ledger. -/
lemma compactCorrectionGates_toffoliMultiplicity_sum_le
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    ((compactCorrectionGates fieldTail counterTail p hcapacity hwidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum <=
      234 * fieldTail.succ * fieldTail.succ +
        24 * fieldTail.succ * counterTail + 156 * fieldTail.succ := by
  rcases compactCorrectionGates_resource fieldTail counterTail p hcapacity
      hwidth with ⟨_, _, htoffoli, _⟩
  rw [htoffoli]
  have hmodulus := modulusOneCount_le fieldTail p
  have hinner :
      115 * fieldTail.succ + 12 * (counterTail + 1) + 19 +
          2 * modulusOneCount fieldTail p <=
        117 * fieldTail.succ + 12 * counterTail + 33 := by
    omega
  have hscaled := Nat.mul_le_mul_left (2 * fieldTail.succ) hinner
  nlinarith

/-- Public-constant-independent primitive length bound for the reversible
correction ledger. -/
lemma compactCorrectionGates_length_le
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    (compactCorrectionGates fieldTail counterTail p hcapacity hwidth).length <=
      234 * fieldTail.succ * fieldTail.succ +
        44 * fieldTail.succ * counterTail + 252 * fieldTail.succ + 63 := by
  rcases compactCorrectionGates_resource fieldTail counterTail p hcapacity
      hwidth with ⟨_, _, _, hlength⟩
  rw [hlength]
  have hslots := correctionSlotOneCountSum_le fieldTail.succ counterTail
    hcapacity
  have hmodulus := modulusOneCount_le fieldTail p
  have hslotsScaled := Nat.mul_le_mul_left 4 hslots
  have hmodulusScaled := Nat.mul_le_mul_left (4 * fieldTail.succ) hmodulus
  have hmodulusConstantScaled := Nat.mul_le_mul_left 6 hmodulus
  nlinarith

/-- Circuit compiled from the literal reversible compact correction ledger. -/
def compactCorrectionProgram
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ (counterTail + 1)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compactCorrectionGates fieldTail counterTail p hcapacity hwidth)

/-- Folded action of the literal reversible compact correction ledger. -/
def compactCorrectionStep
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 1) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
  EncodedBit.GateSpec.stepList
    (compactCorrectionGates fieldTail counterTail p hcapacity hwidth)

/-- The compact correction ledger executes its five named stages in order. -/
lemma compactCorrectionStep_eq_stages
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 1)) :
    compactCorrectionStep fieldTail counterTail p hcapacity hwidth x =
      coefficientReduceReverseStep fieldTail (counterTail + 1) p
        (correctionLoopReverseStep fieldTail counterTail p hcapacity hwidth
          (targetUpdateStep fieldTail (counterTail + 1) p
            (correctionLoopStep fieldTail counterTail p hcapacity hwidth
              (coefficientReduceStep fieldTail (counterTail + 1) p x)))) := by
  simp only [compactCorrectionStep, compactCorrectionGates,
    coefficientReduceStep, correctionLoopStep, targetUpdateStep,
    correctionLoopReverseStep, coefficientReduceReverseStep,
    EncodedBit.GateSpec.stepList_append]

/-- The compact correction circuit realizes its literal gate-list action. -/
lemma compactCorrection_realizes
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ (counterTail + 1))
      (compactCorrectionProgram fieldTail counterTail p hcapacity hwidth) environment
      (compactCorrectionStep fieldTail counterTail p hcapacity hwidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (compactCorrectionGates fieldTail counterTail p hcapacity hwidth)

set_option maxHeartbeats 1200000 in
-- The proof composes two image-form inverse arguments around the sole
-- persistent public-target update.
/-- Compact correction applies the runtime-count power-of-two correction to
the reduced Kaliski coefficient, subtracts that residue from the public
target, and exactly restores the raw coefficient, fold history, counter, and
all borrowed work. -/
lemma compactCorrectionStep_state
    (fieldTail counterTail p : Nat)
    (hcapacity : fieldTail.succ <= 2 ^ counterTail)
    (hwidth : counterTail + 1 <= fieldTail.succ)
    (base : MK.Compact.Registers fieldTail.succ (counterTail + 1))
    (raw : Word (fieldTail.succ + 1)) (target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hraw : raw.val < 2 * p) (htarget : target.val < p) :
    let reduced := reducedWord fieldTail p hpPos hp raw hraw
    let corrected := correctionResiduePrefix fieldTail p hpPos hp
      base.core.counter.val fieldTail.succ reduced
    let correctedLow := truncateFixedWord fieldTail.succ corrected
    compactCorrectionStep fieldTail counterTail p hcapacity hwidth
        (correctionBoundaryState fieldTail (counterTail + 1)
          base raw ⟨p, hp⟩ target) =
      correctionBoundaryState fieldTail (counterTail + 1) base raw ⟨p, hp⟩
        (modularDifferenceWord fieldTail p hpPos hp target correctedLow) := by
  let modulus : Word fieldTail.succ := ⟨p, hp⟩
  let zeroWide : Word (fieldTail.succ + 1) :=
    widenFixedWord fieldTail.succ 0
  let normalizedBase : MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
    { base with
      core := { base.core with scratchB := false }
      shared := cleanSharedWork fieldTail.succ (counterTail + 1)
      target := target }
  let reduced := reducedWord fieldTail p hpPos hp raw hraw
  let reducedFlag : Bool := decide (p <= raw.val)
  let reducedBase : MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
    { normalizedBase with
      core := { normalizedBase.core with scratchB := reducedFlag } }
  let corrected := correctionResiduePrefix fieldTail p hpPos hp
    base.core.counter.val fieldTail.succ reduced
  let correctedLow := truncateFixedWord fieldTail.succ corrected
  let updated := modularDifferenceWord fieldTail p hpPos hp target correctedLow
  let updatedNormalizedBase :
      MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
    { normalizedBase with target := updated }
  let updatedReducedBase :
      MK.Compact.Registers fieldTail.succ (counterTail + 1) :=
    { reducedBase with target := updated }
  let s0 := correctionBoundaryState fieldTail (counterTail + 1)
    base raw modulus target
  let s1 := correctionSlotState fieldTail counterTail reducedBase reduced
    modulus 0 false
  let s2 := correctionSlotState fieldTail counterTail reducedBase corrected
    modulus 0 false
  let s3 := correctionSlotState fieldTail counterTail updatedReducedBase
    corrected modulus 0 false
  let s4 := correctionSlotState fieldTail counterTail updatedReducedBase
    reduced modulus 0 false
  let s5 := correctionBoundaryState fieldTail (counterTail + 1)
    base raw modulus updated
  have hcorrected : corrected.val < p :=
    correctionResiduePrefix_lt fieldTail p hpPos hp base.core.counter.val
      fieldTail.succ reduced (by
        rw [reducedWord_val_eq_mod]
        exact Nat.mod_lt _ hpPos)
  have hcorrectedWidth : corrected.val < 2 ^ fieldTail.succ :=
    hcorrected.trans hp
  have hwidenCorrected :
      widenFixedWord fieldTail.succ correctedLow = corrected := by
    exact widenFixedWord_truncateFixedWord_of_lt fieldTail.succ corrected
      hcorrectedWidth
  have hreduce :
      coefficientReduceStep fieldTail (counterTail + 1) p s0 = s1 := by
    have h := coefficientReduceStep_state fieldTail (counterTail + 1) p
      normalizedBase raw hpPos hp hraw (by rfl)
    simpa [s0, s1, correctionBoundaryState, correctionSlotState,
      normalizedBase, reducedBase, reducedFlag, reduced, modulus, zeroWide,
      cleanSharedWork] using h
  have hloop :
      correctionLoopStep fieldTail counterTail p hcapacity hwidth s1 = s2 := by
    have h := correctionLoopStep_state fieldTail counterTail p hcapacity
      hwidth reducedBase reduced hpPos hp hpOdd (by
        rw [reducedWord_val_eq_mod]
        exact Nat.mod_lt _ hpPos)
    simpa [s1, s2, corrected, normalizedBase, reducedBase] using h
  have htarget :
      targetUpdateStep fieldTail (counterTail + 1) p s2 = s3 := by
    have h := targetUpdateStep_state fieldTail (counterTail + 1) p
      reducedBase correctedLow target hpPos hp (by
        simpa [correctedLow, truncateFixedWord, Nat.mod_eq_of_lt
          hcorrectedWidth] using hcorrected) htarget
    simpa [s2, s3, correctionSlotState, targetUpdateState, doublingState,
      reducedBase, updatedReducedBase, normalizedBase, correctedLow, updated,
      modulus, zeroWide, widenFixedWord_zero, hwidenCorrected,
      cleanSharedWork] using h
  have hloopUpdated :
      correctionLoopStep fieldTail counterTail p hcapacity hwidth s4 = s3 := by
    have h := correctionLoopStep_state fieldTail counterTail p hcapacity
      hwidth updatedReducedBase reduced hpPos hp hpOdd (by
        rw [reducedWord_val_eq_mod]
        exact Nat.mod_lt _ hpPos)
    simpa [s4, s3, corrected, updatedReducedBase, reducedBase,
      normalizedBase] using h
  have hloopReverse :
      correctionLoopReverseStep fieldTail counterTail p hcapacity hwidth
        s3 = s4 := by
    have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
      (correctionLoopGates fieldTail counterTail p hcapacity hwidth) s4
    change correctionLoopReverseStep fieldTail counterTail p hcapacity hwidth
      (correctionLoopStep fieldTail counterTail p hcapacity hwidth s4) = s4
      at hcancel
    rw [hloopUpdated] at hcancel
    exact hcancel
  have hreduceUpdated :
      coefficientReduceStep fieldTail (counterTail + 1) p s5 = s4 := by
    have h := coefficientReduceStep_state fieldTail (counterTail + 1) p
      updatedNormalizedBase raw hpPos hp hraw (by rfl)
    simpa [s5, s4, correctionBoundaryState, correctionSlotState,
      updatedNormalizedBase, updatedReducedBase, normalizedBase, reducedBase,
      reducedFlag, reduced, modulus, zeroWide, cleanSharedWork] using h
  have hreduceReverse :
      coefficientReduceReverseStep fieldTail (counterTail + 1) p s4 = s5 := by
    have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
      (coefficientReduceGates fieldTail (counterTail + 1) p) s5
    change coefficientReduceReverseStep fieldTail (counterTail + 1) p
      (coefficientReduceStep fieldTail (counterTail + 1) p s5) = s5 at hcancel
    rw [hreduceUpdated] at hcancel
    exact hcancel
  change compactCorrectionStep fieldTail counterTail p hcapacity hwidth s0 = s5
  rw [compactCorrectionStep_eq_stages, hreduce, hloop, htarget,
    hloopReverse, hreduceReverse]

/-! ## Width-neutral sign correction and public copy -/

private lemma sCoeffValueWord_pairwise_ne (n counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((sCoeffValueWord n counterWidth).bit left).wire ≠
        ((sCoeffValueWord n counterWidth).bit right).wire := by
  intro left right hne
  simpa [sCoeffValueWord, RegisterBits.sCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (sCoeff_sCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire left)
        (WireAddress.littleEndianWire right)
        (littleEndianWire_ne hne))

private lemma rCoeffValueWord_pairwise_ne (n counterWidth : Nat) :
    forall left right, left ≠ right ->
      ((rCoeffValueWord n counterWidth).bit left).wire ≠
        ((rCoeffValueWord n counterWidth).bit right).wire := by
  intro left right hne
  simpa [rCoeffValueWord, RegisterBits.rCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (rCoeff_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire left)
        (WireAddress.littleEndianWire right)
        (littleEndianWire_ne hne))

private lemma sCoeff_rCoeff_ne (n counterWidth : Nat) :
    forall source target,
      ((sCoeffValueWord n counterWidth).bit source).wire ≠
        ((rCoeffValueWord n counterWidth).bit target).wire := by
  intro source target
  simpa [sCoeffValueWord, rCoeffValueWord, RegisterBits.sCoeffValueBit,
    RegisterBits.rCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire source)
        (WireAddress.littleEndianWire target))

private lemma sCoeff_carry_ne (n counterWidth : Nat) :
    forall bit,
      ((sCoeffValueWord n counterWidth).bit bit).wire ≠
        (coefficientCarryInBit n counterWidth).wire := by
  intro bit
  exact liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
    (RegisterBits.sCoeffValueBit n counterWidth bit)

private lemma rCoeff_carry_ne (n counterWidth : Nat) :
    forall bit,
      ((rCoeffValueWord n counterWidth).bit bit).wire ≠
        (coefficientCarryInBit n counterWidth).wire := by
  intro bit
  exact liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
    (RegisterBits.rCoeffValueBit n counterWidth bit)

private lemma sCoeff_work_ne (n counterWidth : Nat) :
    forall source work,
      ((sCoeffValueWord n counterWidth).bit source).wire ≠
        ((coefficientCarryWorkWord n counterWidth).bit work).wire := by
  intro source work
  exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
    (RegisterBits.sCoeffValueBit n counterWidth source) work

private lemma rCoeff_work_ne (n counterWidth : Nat) :
    forall target work,
      ((rCoeffValueWord n counterWidth).bit target).wire ≠
        ((coefficientCarryWorkWord n counterWidth).bit work).wire := by
  intro target work
  exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
    (RegisterBits.rCoeffValueBit n counterWidth target) work

/-- VBE subtraction layout used after exchanging `s` and `r`.  At the
fixed-round endpoint `s=p`, so the reversed adder maps the right word from `p`
to `p-r` without an incrementer or another arithmetic bank. -/
def signAdderLayout (n counterWidth : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := MK.Compact.encoding n counterWidth) (n + 1) where
  left := sCoeffValueWord n counterWidth
  right := rCoeffValueWord n counterWidth
  carryIn := coefficientCarryInBit n counterWidth
  workCarry := coefficientCarryWorkWord n counterWidth
  leftLeft_ne := sCoeffValueWord_pairwise_ne n counterWidth
  rightRight_ne := rCoeffValueWord_pairwise_ne n counterWidth
  leftRight_ne := sCoeff_rCoeff_ne n counterWidth
  leftCarryIn_ne := sCoeff_carry_ne n counterWidth
  rightCarryIn_ne := rCoeff_carry_ne n counterWidth
  leftWork_ne := sCoeff_work_ne n counterWidth
  rightWork_ne := rCoeff_work_ne n counterWidth
  carryInWork_ne := coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
    n counterWidth
  workWork_ne := by
    intro left right hne
    simpa [coefficientCarryWorkWord] using
      coefficientCarryWorkBit_wire_ne n counterWidth hne

/-- On clean VBE work, the forward sign-layout adder adds `s` into `r` and
restores the sole carry bank.  This word endpoint is later inverted to obtain
`p-r`. -/
lemma signAdderForward_rCoeff
    (n counterWidth : Nat) (x : MK.Compact.Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : forall k,
      (coefficientCarryWorkBit n counterWidth k).get x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
        (signAdderLayout n counterWidth) x).core.rCoeff =
      x.core.rCoeff + x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [← rCoeffValueWord_get n counterWidth bit]
  simpa only [signAdderLayout] using
    (cleanCarrySumStep_get_right_add_of_clean
      (signAdderLayout n counterWidth) x.core.sCoeff x.core.rCoeff bit x
      (by
        intro source
        simpa only [signAdderLayout] using
          sCoeffValueWord_get n counterWidth source x)
      (by
        intro target
        simpa only [signAdderLayout] using
          rCoeffValueWord_get n counterWidth target x)
      (by simpa [signAdderLayout] using hcarry)
      (by
        intro work
        simpa [signAdderLayout, coefficientCarryWorkWord] using hwork work))

/-- Exchange the modulus and residue coefficient words before subtraction. -/
def signSwapGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (MK.Compact.encoding n counterWidth)) :=
  EncodedBit.Word.swapGates
    (sCoeffValueWord n counterWidth)
    (rCoeffValueWord n counterWidth)
    (fun bit => sCoeff_rCoeff_ne n counterWidth bit bit)

/-- Folded exchange of the modulus and residue coefficient words. -/
def signSwapStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.Word.swapStep
    (sCoeffValueWord n counterWidth)
    (rCoeffValueWord n counterWidth)
    (fun bit => sCoeff_rCoeff_ne n counterWidth bit bit)

/-- The sign swap moves the old residue into the left coefficient word. -/
lemma signSwapStep_sCoeff (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth) :
    (signSwapStep n counterWidth x).core.sCoeff = x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := congrFun
    (EncodedBit.Word.swapStep_get_left_word
      (sCoeffValueWord n counterWidth)
      (rCoeffValueWord n counterWidth)
      (fun i => sCoeff_rCoeff_ne n counterWidth i i)
      (sCoeffValueWord_pairwise_ne n counterWidth)
      (rCoeffValueWord_pairwise_ne n counterWidth)
      (sCoeff_rCoeff_ne n counterWidth) x) bit
  simpa [signSwapStep] using h

/-- The sign swap moves the old modulus into the right coefficient word. -/
lemma signSwapStep_rCoeff (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth) :
    (signSwapStep n counterWidth x).core.rCoeff = x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := congrFun
    (EncodedBit.Word.swapStep_get_right_word
      (sCoeffValueWord n counterWidth)
      (rCoeffValueWord n counterWidth)
      (fun i => sCoeff_rCoeff_ne n counterWidth i i)
      (sCoeffValueWord_pairwise_ne n counterWidth)
      (rCoeffValueWord_pairwise_ne n counterWidth)
      (sCoeff_rCoeff_ne n counterWidth) x) bit
  simpa [signSwapStep] using h

/-- The coefficient-word exchange preserves the VBE carry-in. -/
lemma signSwapStep_carryIn (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (signSwapStep n counterWidth x) =
      (coefficientCarryInBit n counterWidth).get x := by
  simpa [signSwapStep] using
    (EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (sCoeffValueWord n counterWidth)
      (rCoeffValueWord n counterWidth)
      (fun i => sCoeff_rCoeff_ne n counterWidth i i)
      (coefficientCarryInBit n counterWidth)
      (sCoeff_carry_ne n counterWidth)
      (rCoeff_carry_ne n counterWidth) x)

/-- The coefficient-word exchange preserves every VBE work carry. -/
lemma signSwapStep_workCarry (n counterWidth : Nat) (bit : Fin n)
    (x : MK.Compact.Registers n counterWidth) :
    (coefficientCarryWorkBit n counterWidth bit).get
        (signSwapStep n counterWidth x) =
      (coefficientCarryWorkBit n counterWidth bit).get x := by
  simpa [signSwapStep, coefficientCarryWorkWord] using
    (EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (sCoeffValueWord n counterWidth)
      (rCoeffValueWord n counterWidth)
      (fun i => sCoeff_rCoeff_ne n counterWidth i i)
      (coefficientCarryWorkBit n counterWidth bit)
      (fun source => sCoeff_work_ne n counterWidth source bit)
      (fun target => rCoeff_work_ne n counterWidth target bit) x)

/-- Reverse action of the sole VBE coefficient adder. -/
def signSubStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
      (signAdderLayout n counterWidth)).reverse

/-- Native width-neutral sign correction `r ↦ p-r`: exchange `s=p` with `r`,
then run the sole VBE coefficient adder backwards. -/
def signCorrectionGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (MK.Compact.encoding n counterWidth)) :=
  signSwapGates n counterWidth ++
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
      (signAdderLayout n counterWidth)).reverse

/-- Circuit compiled from the native compact sign-correction ledger. -/
def signCorrectionProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (signCorrectionGates n counterWidth)

/-- Folded action of the native compact sign-correction ledger. -/
def signCorrectionStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (signCorrectionGates n counterWidth)

/-- The sign ledger is exactly the coefficient exchange followed by one
reverse use of the shared VBE adder. -/
lemma signCorrectionStep_eq (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth) :
    signCorrectionStep n counterWidth x =
      signSubStep n counterWidth (signSwapStep n counterWidth x) := by
  simp [signCorrectionStep, signCorrectionGates, signSwapGates,
    signSwapStep, signSubStep, EncodedBit.Word.swapStep,
    EncodedBit.GateSpec.stepList_append]

private lemma signSubStep_sCoeff (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth) :
    (signSubStep n counterWidth x).core.sCoeff = x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  let layout := signAdderLayout n counterWidth
  let z := signSubStep n counterWidth x
  have hadd :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      layout bit z
  have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x
  calc
    z.core.sCoeff.val.testBit bit.val =
        (layout.left.bit bit).get z := by
      simp [layout, signAdderLayout]
    _ = (layout.left.bit bit).get
          (EncodedBit.GateSpec.stepList
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout) z) :=
        hadd.symm
    _ = x.core.sCoeff.val.testBit bit.val := by
      have hz :
          EncodedBit.GateSpec.stepList
              (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout) z =
            x := by
        simpa [layout, z, signSubStep] using hcancel
      rw [hz]
      simp [layout, signAdderLayout]

private lemma signSubStep_carryIn (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (signSubStep n counterWidth x) =
      (coefficientCarryInBit n counterWidth).get x := by
  let layout := signAdderLayout n counterWidth
  let z := signSubStep n counterWidth x
  have hadd :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      layout z
  have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout).reverse x
  calc
    (coefficientCarryInBit n counterWidth).get z =
        layout.carryIn.get z := by rfl
    _ = layout.carryIn.get
          (EncodedBit.GateSpec.stepList
            (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout) z) :=
        hadd.symm
    _ = (coefficientCarryInBit n counterWidth).get x := by
      have hz :
          EncodedBit.GateSpec.stepList
              (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates layout) z =
            x := by
        simpa [layout, z, signSubStep] using hcancel
      rw [hz]
      rfl

private lemma signSubStep_workCarry_clean (n counterWidth : Nat)
    (bit : Fin n) (x : MK.Compact.Registers n counterWidth)
    (hclean : forall workBit,
      (coefficientCarryWorkBit n counterWidth workBit).get x = false) :
    (coefficientCarryWorkBit n counterWidth bit).get
        (signSubStep n counterWidth x) = false := by
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_reverse_get_workCarry_clean
      (signAdderLayout n counterWidth) bit x (by
        intro workBit
        simpa only [signAdderLayout, coefficientCarryWorkWord] using
          hclean workBit)

/-- A clean reverse use of the sign adder subtracts its preserved left word
from its right word. -/
lemma signSubStep_rCoeff_sub (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : forall bit,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (signSubStep n counterWidth x).core.rCoeff =
      x.core.rCoeff - x.core.sCoeff := by
  let z := signSubStep n counterWidth x
  have hcarryZ :
      (coefficientCarryInBit n counterWidth).get z = false := by
    rw [signSubStep_carryIn]
    exact hcarry
  have hworkZ : forall bit,
      (coefficientCarryWorkBit n counterWidth bit).get z = false := by
    intro bit
    exact signSubStep_workCarry_clean n counterWidth bit x hwork
  have hadd := signAdderForward_rCoeff n counterWidth z hcarryZ hworkZ
  have hcancel := EncodedBit.GateSpec.stepList_reverse_stepList
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
      (signAdderLayout n counterWidth)).reverse x
  have hright : x.core.rCoeff = z.core.rCoeff + z.core.sCoeff := by
    calc
      x.core.rCoeff =
          (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
            (signAdderLayout n counterWidth) z).core.rCoeff := by
        simpa [z, signSubStep,
          PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using
            congrArg (fun state => state.core.rCoeff) hcancel.symm
      _ = z.core.rCoeff + z.core.sCoeff := hadd
  change z.core.rCoeff = x.core.rCoeff - x.core.sCoeff
  rw [eq_sub_iff_add_eq]
  rw [← signSubStep_sCoeff n counterWidth x]
  exact hright.symm

/-- The native sign-correction ledger computes width-preserving `s-r` while
returning the sole VBE carry bank clean. -/
lemma signCorrectionStep_rCoeff_sub (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : forall bit,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (signCorrectionStep n counterWidth x).core.rCoeff =
      x.core.sCoeff - x.core.rCoeff := by
  rw [signCorrectionStep_eq]
  rw [signSubStep_rCoeff_sub]
  · rw [signSwapStep_rCoeff, signSwapStep_sCoeff]
  · rw [signSwapStep_carryIn]
    exact hcarry
  · intro bit
    rw [signSwapStep_workCarry]
    exact hwork bit

/-- Under the fixed-round endpoint ordering, sign correction is the ordinary
natural-number difference rather than a wrapped word subtraction. -/
lemma signCorrectionStep_rCoeff_val (n counterWidth : Nat)
    (x : MK.Compact.Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : forall bit,
      (coefficientCarryWorkBit n counterWidth bit).get x = false)
    (hle : x.core.rCoeff.val <= x.core.sCoeff.val) :
    (signCorrectionStep n counterWidth x).core.rCoeff.val =
      x.core.sCoeff.val - x.core.rCoeff.val := by
  rw [signCorrectionStep_rCoeff_sub n counterWidth x hcarry hwork]
  exact Fin.sub_val_of_le hle

/-- The physical sign-correction circuit realizes its literal gate-list
action. -/
lemma signCorrection_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (MK.Compact.encoding n counterWidth)
      (signCorrectionProgram n counterWidth) environment
      (signCorrectionStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (signCorrectionGates n counterWidth)

private lemma correctedValue_target_ne (n counterWidth : Nat) :
    forall source target,
      ((correctedValueWord n counterWidth).bit source).wire ≠
        ((targetValueWord n counterWidth).bit target).wire := by
  intro source target
  exact liftCoreBit_targetBit_wire_ne n counterWidth
    (RegisterBits.rCoeffValueBit n counterWidth (Fin.castSucc source))
    (WireAddress.littleEndianWire target)

/-- Native CNOT copy of the corrected low word into the public target. -/
def outputCopyGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (MK.Compact.encoding n counterWidth)) :=
  EncodedBit.Word.xorIntoGates
    (correctedValueWord n counterWidth)
    (targetValueWord n counterWidth)
    (fun bit => correctedValue_target_ne n counterWidth bit bit)

/-- Circuit compiled from the literal public-output CNOT copy. -/
def outputCopyProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (outputCopyGates n counterWidth)

/-- Folded action of the literal public-output CNOT copy. -/
def outputCopyStep (n counterWidth : Nat) :
    MK.Compact.Registers n counterWidth ->
      MK.Compact.Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (outputCopyGates n counterWidth)

/-- The physical output-copy circuit realizes its literal gate-list action. -/
lemma outputCopy_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (MK.Compact.encoding n counterWidth)
      (outputCopyProgram n counterWidth) environment
      (outputCopyStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (outputCopyGates n counterWidth)

end

end CompactCorrection
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
