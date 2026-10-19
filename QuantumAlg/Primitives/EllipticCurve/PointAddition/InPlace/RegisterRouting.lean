/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Layout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.BlockBank
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Correction

/-!
# Register routing for in-place affine point addition

This leaf exposes the compact inversion fields reused between arithmetic
calls.  In particular, the one existing `2f` branch-history word is split
into two temporary `f`-bit views.  The views allocate no wires: they only let
the point schedule save `x1` and `t0` while the same compact carrier performs
a Montgomery multiplication, then erase both saves before the next
inversion.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace RegisterRouting

noncomputable section

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-! ## Reused compact words -/

/-- Compact `u`, lifted to the complete point carrier. -/
def uWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (Layout.encoding fieldWidth counterWidth) fieldWidth :=
  Layout.liftArithmeticWord fieldWidth counterWidth fieldWidth
    (MK.Compact.uValueWord fieldWidth counterWidth)

/-- Low `fieldWidth` bits of compact `s`.  Its extra top bit is known zero at
every point-operation boundary. -/
def sCoefficientWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (Layout.encoding fieldWidth counterWidth) fieldWidth :=
  Layout.liftArithmeticWord fieldWidth counterWidth fieldWidth
    { bit := fun bit =>
        (MK.Compact.sCoeffValueWord fieldWidth counterWidth).bit
          (Fin.castSucc bit) }

/-- Low `fieldWidth` bits of compact `r`, used for canonical field residues. -/
def rCoefficientWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (Layout.encoding fieldWidth counterWidth) fieldWidth :=
  Layout.liftArithmeticWord fieldWidth counterWidth fieldWidth
    (CompactCorrection.correctedValueWord fieldWidth counterWidth)

/-- A little-endian value bit of the sole compact branch-history word. -/
def historyValueBit (fieldWidth counterWidth : Nat)
    (bit : Fin (2 * fieldWidth)) :
    EncodedBit (Layout.encoding fieldWidth counterWidth) :=
  Layout.liftArithmeticBit fieldWidth counterWidth
    (MK.Compact.liftCoreBit fieldWidth counterWidth
      (MK.RegisterBits.historyBit fieldWidth counterWidth
        (WireAddress.littleEndianWire bit)))

/-- Low half of the existing `2f` history word. -/
def historyLowWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (Layout.encoding fieldWidth counterWidth) fieldWidth where
  bit := fun bit =>
    historyValueBit fieldWidth counterWidth
      ⟨bit.val, by omega⟩

/-- High half of the existing `2f` history word. -/
def historyHighWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (Layout.encoding fieldWidth counterWidth) fieldWidth where
  bit := fun bit =>
    historyValueBit fieldWidth counterWidth
      ⟨fieldWidth + bit.val, by omega⟩

/-- Compact active flag, lifted to the complete point carrier. -/
def activeBit (fieldWidth counterWidth : Nat) :
    EncodedBit (Layout.encoding fieldWidth counterWidth) :=
  Layout.liftArithmeticBit fieldWidth counterWidth
    (MK.Compact.activeBit fieldWidth counterWidth)

@[simp] lemma uWord_get (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) (registers : Layout.Registers fieldWidth counterWidth) :
    ((uWord fieldWidth counterWidth).bit bit).get registers =
      registers.arithmetic.core.u.val.testBit bit.val := by
  change ((MK.Compact.uValueWord fieldWidth counterWidth).bit bit).get
      registers.arithmetic = _
  exact MK.Compact.uValueWord_get fieldWidth counterWidth bit
    registers.arithmetic

@[simp] lemma sCoefficientWord_get (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) (registers : Layout.Registers fieldWidth counterWidth) :
    ((sCoefficientWord fieldWidth counterWidth).bit bit).get registers =
      registers.arithmetic.core.sCoeff.val.testBit bit.val := by
  change
    (MK.RegisterBits.sCoeffValueBit fieldWidth counterWidth
      (Fin.castSucc bit)).get registers.arithmetic.core = _
  exact MK.RegisterBits.sCoeffValueBit_get fieldWidth counterWidth
    (Fin.castSucc bit) registers.arithmetic.core

@[simp] lemma rCoefficientWord_get (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) (registers : Layout.Registers fieldWidth counterWidth) :
    ((rCoefficientWord fieldWidth counterWidth).bit bit).get registers =
      registers.arithmetic.core.rCoeff.val.testBit bit.val := by
  change
    (MK.RegisterBits.rCoeffValueBit fieldWidth counterWidth
      (Fin.castSucc bit)).get registers.arithmetic.core = _
  exact MK.RegisterBits.rCoeffValueBit_get fieldWidth counterWidth
    (Fin.castSucc bit) registers.arithmetic.core

@[simp] lemma historyValueBit_get (fieldWidth counterWidth : Nat)
    (bit : Fin (2 * fieldWidth))
    (registers : Layout.Registers fieldWidth counterWidth) :
    (historyValueBit fieldWidth counterWidth bit).get registers =
      registers.arithmetic.core.history.val.testBit bit.val := by
  change
    (MK.RegisterBits.historyBit fieldWidth counterWidth
      (WireAddress.littleEndianWire bit)).get registers.arithmetic.core = _
  rw [MK.RegisterBits.historyBit_get]
  simp

@[simp] lemma historyLowWord_get (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) (registers : Layout.Registers fieldWidth counterWidth) :
    ((historyLowWord fieldWidth counterWidth).bit bit).get registers =
      registers.arithmetic.core.history.val.testBit bit.val := by
  simp [historyLowWord]

@[simp] lemma historyHighWord_get (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) (registers : Layout.Registers fieldWidth counterWidth) :
    ((historyHighWord fieldWidth counterWidth).bit bit).get registers =
      registers.arithmetic.core.history.val.testBit (fieldWidth + bit.val) := by
  simp [historyHighWord]

@[simp] lemma activeBit_get (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth) :
    (activeBit fieldWidth counterWidth).get registers =
      registers.arithmetic.core.active := by
  change (MK.Compact.activeBit fieldWidth counterWidth).get
    registers.arithmetic = _
  exact MK.Compact.activeBit_get fieldWidth counterWidth registers.arithmetic

@[simp] lemma activeBit_flip (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth) :
    (activeBit fieldWidth counterWidth).flip registers =
      { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with
            active := !registers.arithmetic.core.active } } } := by
  rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
  rcases arithmetic with ⟨core, shared, target⟩
  rcases core with
    ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history, active,
      counter⟩
  rfl

/-! ## Complete field-word ports -/

/-- Structural port for the mutable affine `y1` coordinate. -/
def mutableYPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := Layout.mutableYWord fieldWidth counterWidth
  read := fun registers => registers.mutableY
  set := fun registers value => { registers with mutableY := value }
  set_read := by
    intro registers
    cases registers
    rfl
  read_set := by
    intro registers value
    cases registers
    rfl
  set_set := by
    intro registers first second
    cases registers
    rfl
  get_bit := Layout.mutableYBit_get fieldWidth counterWidth
  pairwise_ne := Layout.mutableYBit_wire_ne fieldWidth counterWidth
  clear_flip := by
    intro bit registers
    rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
    rfl

/-- Structural port for the persistent slope temporary `lambda`. -/
def lambdaPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := Layout.lambdaWord fieldWidth counterWidth
  read := fun registers => registers.«λ»
  set := fun registers value => { registers with «λ» := value }
  set_read := by
    intro registers
    cases registers
    rfl
  read_set := by
    intro registers value
    cases registers
    rfl
  set_set := by
    intro registers first second
    cases registers
    rfl
  get_bit := Layout.lambdaBit_get fieldWidth counterWidth
  pairwise_ne := Layout.lambdaBit_wire_ne fieldWidth counterWidth
  clear_flip := by
    intro bit registers
    rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
    rfl

/-- Structural port for mutable `x1`, the compact core's `v` word. -/
def mutableXPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := Layout.mutableXWord fieldWidth counterWidth
  read := fun registers => registers.arithmetic.core.v
  set := fun registers value =>
    { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with v := value } } }
  set_read := by
    intro registers
    cases registers
    rfl
  read_set := by
    intro registers value
    cases registers
    rfl
  set_set := by
    intro registers first second
    cases registers
    rfl
  get_bit := by
    intro bit registers
    change ((MK.Compact.vValueWord fieldWidth counterWidth).bit bit).get
        registers.arithmetic = _
    exact MK.Compact.vValueWord_get fieldWidth counterWidth bit
      registers.arithmetic
  pairwise_ne := by
    intro left right hne
    apply Layout.liftArithmeticBit_wire_ne
    simpa [Layout.mutableXWord, Layout.liftArithmeticWord,
      MK.Compact.vValueWord, MK.RegisterBits.vValueBit] using
      MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
        (MK.v_v_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire left)
          (WireAddress.littleEndianWire right) (littleEndianWire_ne hne))
  clear_flip := by
    intro bit registers
    rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
    rcases arithmetic with ⟨core, shared, target⟩
    rcases core with
      ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history, active, counter⟩
    rfl

/-- Structural port for temporary `t0`, the compact arithmetic target. -/
def t0Port (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := Layout.t0Word fieldWidth counterWidth
  read := fun registers => registers.arithmetic.target
  set := fun registers value =>
    { registers with arithmetic := { registers.arithmetic with target := value } }
  set_read := by
    intro registers
    cases registers
    rfl
  read_set := by
    intro registers value
    cases registers
    rfl
  set_set := by
    intro registers first second
    cases registers
    rfl
  get_bit := by
    intro bit registers
    change (MK.Compact.targetValueBit fieldWidth counterWidth bit).get
        registers.arithmetic = _
    exact MK.Compact.targetValueBit_get fieldWidth counterWidth bit
      registers.arithmetic
  pairwise_ne := by
    intro left right hne
    apply Layout.liftArithmeticBit_wire_ne
    simpa [Layout.t0Word, Layout.liftArithmeticWord,
      MK.Compact.targetValueWord] using
      MK.Compact.targetValueBit_wire_ne fieldWidth counterWidth hne
  clear_flip := by
    intro bit registers
    rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
    rcases arithmetic with ⟨core, shared, target⟩
    rfl

/-- Structural port for compact `u`. -/
def uPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := uWord fieldWidth counterWidth
  read := fun registers => registers.arithmetic.core.u
  set := fun registers value =>
    { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with u := value } } }
  set_read := by intro registers; cases registers; rfl
  read_set := by intro registers value; cases registers; rfl
  set_set := by intro registers first second; cases registers; rfl
  get_bit := uWord_get fieldWidth counterWidth
  pairwise_ne := by
    intro left right hne
    apply Layout.liftArithmeticBit_wire_ne
    simpa [uWord, MK.Compact.uValueWord, MK.RegisterBits.uValueBit] using
      MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
        (MK.u_u_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire left)
          (WireAddress.littleEndianWire right) (littleEndianWire_ne hne))
  clear_flip := by
    intro bit registers
    rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
    rcases arithmetic with ⟨core, shared, target⟩
    rcases core with
      ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history, active,
        counter⟩
    rfl

/-! ### Low coefficient port -/

/-- Low `fieldWidth` bits of an `(fieldWidth + 1)`-bit coefficient. -/
private def coefficientLowValue (fieldWidth : Nat)
    (coefficient : Nat.FixedWidth.Word (fieldWidth + 1)) :
    Nat.FixedWidth.Word fieldWidth :=
  CompactCorrection.truncateFixedWord fieldWidth coefficient

@[simp] lemma coefficientLowValue_zero (fieldWidth : Nat) :
    coefficientLowValue fieldWidth 0 = 0 := by
  apply Fin.ext
  simp [coefficientLowValue, CompactCorrection.truncateFixedWord]

@[simp] lemma coefficientLowValue_one (fieldWidth : Nat) :
    coefficientLowValue fieldWidth 1 = 1 := by
  apply Fin.ext
  simp [coefficientLowValue, CompactCorrection.truncateFixedWord]

/-- The single high bit of an `(fieldWidth + 1)`-bit coefficient. -/
private def coefficientTopValue (fieldWidth : Nat)
    (coefficient : Nat.FixedWidth.Word (fieldWidth + 1)) :
    Nat.FixedWidth.Word 1 :=
  ⟨coefficient.val / 2 ^ fieldWidth, by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos fieldWidth)]
    simpa [pow_succ, Nat.mul_comm] using coefficient.isLt⟩

@[simp] lemma coefficientTopValue_zero (fieldWidth : Nat) :
    coefficientTopValue fieldWidth 0 = 0 := by
  apply Fin.ext
  simp [coefficientTopValue]

@[simp] lemma coefficientTopValue_one_succ (fieldTail : Nat) :
    coefficientTopValue fieldTail.succ 1 = 0 := by
  apply Fin.ext
  simp [coefficientTopValue]

/-- Reassemble an `(fieldWidth + 1)`-bit coefficient from its low word and
single high bit. -/
private def coefficientJoin (fieldWidth : Nat)
    (low : Nat.FixedWidth.Word fieldWidth)
    (top : Nat.FixedWidth.Word 1) :
    Nat.FixedWidth.Word (fieldWidth + 1) :=
  ⟨low.val + 2 ^ fieldWidth * top.val, by
    have hbound : low.val + 2 ^ fieldWidth * top.val <
        2 ^ fieldWidth * 2 := by
      calc
      low.val + 2 ^ fieldWidth * top.val <
          2 ^ fieldWidth + 2 ^ fieldWidth * top.val :=
        Nat.add_lt_add_right low.isLt _
      _ = 2 ^ fieldWidth * (top.val + 1) := by
        simp [Nat.mul_succ, Nat.add_comm]
      _ ≤ 2 ^ fieldWidth * 2 :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt top.isLt)
    simpa [pow_succ] using hbound⟩

private lemma coefficientLowValue_join (fieldWidth : Nat)
    (low : Nat.FixedWidth.Word fieldWidth)
    (top : Nat.FixedWidth.Word 1) :
    coefficientLowValue fieldWidth (coefficientJoin fieldWidth low top) =
      low := by
  apply Fin.ext
  change (low.val + 2 ^ fieldWidth * top.val) % 2 ^ fieldWidth = low.val
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low.isLt]

private lemma coefficientTopValue_join (fieldWidth : Nat)
    (low : Nat.FixedWidth.Word fieldWidth)
    (top : Nat.FixedWidth.Word 1) :
    coefficientTopValue fieldWidth (coefficientJoin fieldWidth low top) =
      top := by
  apply Fin.ext
  change (low.val + 2 ^ fieldWidth * top.val) / 2 ^ fieldWidth = top.val
  calc
    (low.val + 2 ^ fieldWidth * top.val) / 2 ^ fieldWidth =
        low.val / 2 ^ fieldWidth + top.val :=
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos fieldWidth)
    _ = 0 + top.val := by rw [Nat.div_eq_of_lt low.isLt]
    _ = top.val := Nat.zero_add _

@[simp] lemma coefficientJoin_zero_top (fieldWidth : Nat)
    (low : Nat.FixedWidth.Word fieldWidth) :
    coefficientJoin fieldWidth low 0 =
      CompactCorrection.widenFixedWord fieldWidth low := by
  apply Fin.ext
  simp [coefficientJoin, CompactCorrection.widenFixedWord]

private lemma coefficientJoin_split (fieldWidth : Nat)
    (coefficient : Nat.FixedWidth.Word (fieldWidth + 1)) :
    coefficientJoin fieldWidth (coefficientLowValue fieldWidth coefficient)
      (coefficientTopValue fieldWidth coefficient) = coefficient := by
  apply Fin.ext
  exact Nat.mod_add_div coefficient.val (2 ^ fieldWidth)

/-- Replace the low `s` coefficient word while preserving its high bit. -/
private def setSCoefficientLow (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    Layout.Registers fieldWidth counterWidth :=
  { registers with arithmetic :=
      { registers.arithmetic with core :=
        { registers.arithmetic.core with
          sCoeff := coefficientJoin fieldWidth value
            (coefficientTopValue fieldWidth
              registers.arithmetic.core.sCoeff) } } }

/-- Flipping a routed low `s` bit changes only that coefficient field. -/
private lemma sCoefficientWord_flip (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth)
    (registers : Layout.Registers fieldWidth counterWidth) :
    ((sCoefficientWord fieldWidth counterWidth).bit bit).flip registers =
      { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with
            sCoeff := WireAddress.flipBit
              (WireAddress.littleEndianWire (Fin.castSucc bit))
              registers.arithmetic.core.sCoeff } } } := by
  rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
  rcases arithmetic with ⟨core, shared, target⟩
  rcases core with
    ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history, active,
      counter⟩
  simp [sCoefficientWord, MK.Compact.sCoeffValueWord,
    MK.Compact.sCoeffValueBit,
    Layout.liftArithmeticWord,
    Layout.liftArithmeticBit, Layout.rawArithmeticBit,
    Layout.registerTupleEquiv, MK.Compact.liftCoreBit,
    MK.Compact.rawCoreBit, MK.Compact.registerTupleEquiv,
    MK.RegisterBits.sCoeffValueBit, MK.RegisterBits.sCoeffBit,
    MK.RegisterBits.tupleSCoeffBit, MK.registerTupleEquiv, MK.wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]

private lemma coefficientTopValue_flipSLow
    (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth)
    (registers : Layout.Registers fieldWidth counterWidth) :
    coefficientTopValue fieldWidth
        (((sCoefficientWord fieldWidth counterWidth).bit bit).flip
          registers).arithmetic.core.sCoeff =
      coefficientTopValue fieldWidth registers.arithmetic.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro top
  have hpreserve := EncodedBit.get_flip_of_wire_ne
    ((sCoefficientWord fieldWidth counterWidth).bit bit)
    (Layout.liftArithmeticBit fieldWidth counterWidth
      (MK.Compact.liftCoreBit fieldWidth counterWidth
        (MK.RegisterBits.sCoeffValueBit fieldWidth counterWidth
          (Fin.last fieldWidth))))
    (by
      apply Layout.liftArithmeticBit_wire_ne
      apply MK.Compact.liftCoreBit_wire_ne
      simpa [sCoefficientWord, MK.RegisterBits.sCoeffValueBit] using
        MK.sCoeff_sCoeff_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire (Fin.castSucc bit))
          (WireAddress.littleEndianWire (Fin.last fieldWidth))
          (littleEndianWire_ne (Fin.castSucc_ne_last bit))) registers
  have htop : top = 0 := Fin.eq_zero top
  subst top
  change
    ((((sCoefficientWord fieldWidth counterWidth).bit bit).flip
        registers).arithmetic.core.sCoeff.val / 2 ^ fieldWidth).testBit 0 =
      (registers.arithmetic.core.sCoeff.val / 2 ^ fieldWidth).testBit 0
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  simpa [MK.RegisterBits.sCoeffValueBit_get] using hpreserve

/-- Structural port for the low `fieldWidth` bits of compact `s`; its one
high bit is retained by every port update. -/
def sCoefficientPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := sCoefficientWord fieldWidth counterWidth
  read := fun registers =>
    coefficientLowValue fieldWidth registers.arithmetic.core.sCoeff
  set := setSCoefficientLow fieldWidth counterWidth
  set_read := by
    intro registers
    unfold setSCoefficientLow
    rw [coefficientJoin_split]
  read_set := by
    intro registers value
    unfold setSCoefficientLow
    exact coefficientLowValue_join fieldWidth value _
  set_set := by
    intro registers first second
    unfold setSCoefficientLow
    rw [coefficientTopValue_join]
  get_bit := by
    intro bit registers
    rw [sCoefficientWord_get]
    simp [coefficientLowValue, CompactCorrection.truncateFixedWord,
      Nat.testBit_mod_two_pow, bit.isLt]
  pairwise_ne := by
    intro left right hne
    apply Layout.liftArithmeticBit_wire_ne
    simpa [sCoefficientWord, Layout.liftArithmeticWord,
      MK.Compact.sCoeffValueWord, MK.Compact.sCoeffValueBit,
      MK.RegisterBits.sCoeffValueBit] using
      MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
        (MK.sCoeff_sCoeff_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire (Fin.castSucc left))
          (WireAddress.littleEndianWire (Fin.castSucc right))
          (littleEndianWire_ne
            (fun heq => hne ((Fin.castSucc_injective _) heq))))
  clear_flip := by
    intro bit registers
    have htop := coefficientTopValue_flipSLow fieldWidth counterWidth bit
      registers
    change setSCoefficientLow fieldWidth counterWidth
        (((sCoefficientWord fieldWidth counterWidth).bit bit).flip registers)
        0 = setSCoefficientLow fieldWidth counterWidth registers 0
    rw [sCoefficientWord_flip] at htop ⊢
    unfold setSCoefficientLow
    rw [htop]

@[simp] lemma sCoefficientPort_set (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    (sCoefficientPort fieldWidth counterWidth).set registers value =
      { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with
            sCoeff := coefficientJoin fieldWidth value
              (coefficientTopValue fieldWidth
                registers.arithmetic.core.sCoeff) } } } :=
  rfl

/-- Replace the low `r` coefficient word while preserving its high bit. -/
private def setRCoefficientLow (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    Layout.Registers fieldWidth counterWidth :=
  { registers with arithmetic :=
      { registers.arithmetic with core :=
        { registers.arithmetic.core with
          rCoeff := coefficientJoin fieldWidth value
            (coefficientTopValue fieldWidth
              registers.arithmetic.core.rCoeff) } } }

/-- Flipping a routed low `r` bit changes only that coefficient field. -/
private lemma rCoefficientWord_flip (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth)
    (registers : Layout.Registers fieldWidth counterWidth) :
    ((rCoefficientWord fieldWidth counterWidth).bit bit).flip registers =
      { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with
            rCoeff := WireAddress.flipBit
              (WireAddress.littleEndianWire (Fin.castSucc bit))
              registers.arithmetic.core.rCoeff } } } := by
  rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
  rcases arithmetic with ⟨core, shared, target⟩
  rcases core with
    ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history, active,
      counter⟩
  simp [rCoefficientWord, CompactCorrection.correctedValueWord,
    CompactCorrection.rCoeffValueWord, Layout.liftArithmeticWord,
    Layout.liftArithmeticBit, Layout.rawArithmeticBit,
    Layout.registerTupleEquiv, MK.Compact.liftCoreBit,
    MK.Compact.rawCoreBit, MK.Compact.registerTupleEquiv,
    MK.RegisterBits.rCoeffValueBit, MK.RegisterBits.rCoeffBit,
    MK.RegisterBits.tupleRCoeffBit, MK.registerTupleEquiv, MK.wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]

private lemma coefficientTopValue_flipRLow
    (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth)
    (registers : Layout.Registers fieldWidth counterWidth) :
    coefficientTopValue fieldWidth
        (((rCoefficientWord fieldWidth counterWidth).bit bit).flip
          registers).arithmetic.core.rCoeff =
      coefficientTopValue fieldWidth registers.arithmetic.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro top
  have hpreserve := EncodedBit.get_flip_of_wire_ne
    ((rCoefficientWord fieldWidth counterWidth).bit bit)
    (Layout.liftArithmeticBit fieldWidth counterWidth
      (MK.Compact.liftCoreBit fieldWidth counterWidth
        (MK.RegisterBits.rCoeffValueBit fieldWidth counterWidth
          (Fin.last fieldWidth))))
    (by
      apply Layout.liftArithmeticBit_wire_ne
      apply MK.Compact.liftCoreBit_wire_ne
      simpa [rCoefficientWord, CompactCorrection.correctedValueWord,
        CompactCorrection.rCoeffValueWord,
        MK.RegisterBits.rCoeffValueBit] using
          MK.rCoeff_rCoeff_wire_ne fieldWidth counterWidth
            (WireAddress.littleEndianWire (Fin.castSucc bit))
            (WireAddress.littleEndianWire (Fin.last fieldWidth))
            (littleEndianWire_ne (Fin.castSucc_ne_last bit))) registers
  have htop : top = 0 := Fin.eq_zero top
  subst top
  change
    ((((rCoefficientWord fieldWidth counterWidth).bit bit).flip
        registers).arithmetic.core.rCoeff.val / 2 ^ fieldWidth).testBit 0 =
      (registers.arithmetic.core.rCoeff.val / 2 ^ fieldWidth).testBit 0
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  simpa [MK.RegisterBits.rCoeffValueBit_get] using hpreserve

/-- Structural port for the low `fieldWidth` bits of compact `r`; its one
high bit is retained by every port update. -/
def rCoefficientPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := rCoefficientWord fieldWidth counterWidth
  read := fun registers =>
    coefficientLowValue fieldWidth registers.arithmetic.core.rCoeff
  set := setRCoefficientLow fieldWidth counterWidth
  set_read := by
    intro registers
    unfold setRCoefficientLow
    rw [coefficientJoin_split]
  read_set := by
    intro registers value
    unfold setRCoefficientLow
    exact coefficientLowValue_join fieldWidth value _
  set_set := by
    intro registers first second
    unfold setRCoefficientLow
    rw [coefficientTopValue_join]
  get_bit := by
    intro bit registers
    rw [rCoefficientWord_get]
    simp [coefficientLowValue, CompactCorrection.truncateFixedWord,
      Nat.testBit_mod_two_pow, bit.isLt]
  pairwise_ne := by
    intro left right hne
    apply Layout.liftArithmeticBit_wire_ne
    simpa [rCoefficientWord, CompactCorrection.correctedValueWord,
      CompactCorrection.rCoeffValueWord, MK.RegisterBits.rCoeffValueBit] using
        MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
          (MK.rCoeff_rCoeff_wire_ne fieldWidth counterWidth
            (WireAddress.littleEndianWire (Fin.castSucc left))
            (WireAddress.littleEndianWire (Fin.castSucc right))
            (littleEndianWire_ne
              (fun heq => hne ((Fin.castSucc_injective _) heq))))
  clear_flip := by
    intro bit registers
    have htop := coefficientTopValue_flipRLow fieldWidth counterWidth bit
      registers
    change setRCoefficientLow fieldWidth counterWidth
        (((rCoefficientWord fieldWidth counterWidth).bit bit).flip registers)
        0 = setRCoefficientLow fieldWidth counterWidth registers 0
    rw [rCoefficientWord_flip] at htop ⊢
    unfold setRCoefficientLow
    rw [htop]

@[simp] lemma rCoefficientPort_set (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    (rCoefficientPort fieldWidth counterWidth).set registers value =
      { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with
            rCoeff := coefficientJoin fieldWidth value
              (coefficientTopValue fieldWidth
                registers.arithmetic.core.rCoeff) } } } :=
  rfl

/-! ## Physical separation -/

lemma historyValueBit_wire_ne (fieldWidth counterWidth : Nat)
    {left right : Fin (2 * fieldWidth)} (hne : left ≠ right) :
    (historyValueBit fieldWidth counterWidth left).wire ≠
      (historyValueBit fieldWidth counterWidth right).wire := by
  apply Layout.liftArithmeticBit_wire_ne
  apply MK.Compact.liftCoreBit_wire_ne
  exact MK.RegisterBits.history_history_wire_ne fieldWidth counterWidth
    (littleEndianWire_ne hne)

lemma historyLowWord_pairwise_ne (fieldWidth counterWidth : Nat) :
    ∀ left right, left ≠ right →
      ((historyLowWord fieldWidth counterWidth).bit left).wire ≠
        ((historyLowWord fieldWidth counterWidth).bit right).wire := by
  intro left right hne
  apply historyValueBit_wire_ne
  intro heq
  apply hne
  apply Fin.ext
  exact congrArg (fun index : Fin (2 * fieldWidth) => index.val) heq

lemma historyHighWord_pairwise_ne (fieldWidth counterWidth : Nat) :
    ∀ left right, left ≠ right →
      ((historyHighWord fieldWidth counterWidth).bit left).wire ≠
        ((historyHighWord fieldWidth counterWidth).bit right).wire := by
  intro left right hne
  apply historyValueBit_wire_ne
  intro heq
  apply hne
  apply Fin.ext
  have hval : fieldWidth + left.val = fieldWidth + right.val :=
    congrArg (fun index : Fin (2 * fieldWidth) => index.val) heq
  exact Nat.add_left_cancel hval

lemma historyLow_high_ne (fieldWidth counterWidth : Nat) :
    ∀ low high,
      ((historyLowWord fieldWidth counterWidth).bit low).wire ≠
        ((historyHighWord fieldWidth counterWidth).bit high).wire := by
  intro low high
  apply historyValueBit_wire_ne
  intro heq
  have hval : low.val = fieldWidth + high.val :=
    congrArg (fun index : Fin (2 * fieldWidth) => index.val) heq
  omega

/-! ## Compact history-half ports -/

/-- The low `f` bits of a compact `2f`-bit history value. -/
private def historyLowValue (fieldWidth : Nat)
    (history : Nat.FixedWidth.Word (2 * fieldWidth)) :
    Nat.FixedWidth.Word fieldWidth :=
  ⟨history.val % 2 ^ fieldWidth,
    Nat.mod_lt _ (Nat.two_pow_pos fieldWidth)⟩

@[simp] lemma historyLowValue_zero (fieldWidth : Nat) :
    historyLowValue fieldWidth 0 = 0 := by
  apply Fin.ext
  simp [historyLowValue]

/-- The high `f` bits of a compact `2f`-bit history value. -/
private def historyHighValue (fieldWidth : Nat)
    (history : Nat.FixedWidth.Word (2 * fieldWidth)) :
    Nat.FixedWidth.Word fieldWidth :=
  ⟨history.val / 2 ^ fieldWidth, by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos fieldWidth)).2
    calc
      history.val < 2 ^ (2 * fieldWidth) := history.isLt
      _ = 2 ^ fieldWidth * 2 ^ fieldWidth := by
        rw [two_mul, pow_add]⟩

@[simp] lemma historyHighValue_zero (fieldWidth : Nat) :
    historyHighValue fieldWidth 0 = 0 := by
  apply Fin.ext
  simp [historyHighValue]

/-- Reassemble a compact history word from its low and high halves. -/
private def historyJoin (fieldWidth : Nat)
    (low high : Nat.FixedWidth.Word fieldWidth) :
    Nat.FixedWidth.Word (2 * fieldWidth) :=
  ⟨low.val + 2 ^ fieldWidth * high.val, by
    rw [two_mul, pow_add]
    calc
      low.val + 2 ^ fieldWidth * high.val <
          2 ^ fieldWidth + 2 ^ fieldWidth * high.val :=
        Nat.add_lt_add_right low.isLt _
      _ = 2 ^ fieldWidth * (high.val + 1) := by
        simp [Nat.mul_succ, Nat.add_comm]
      _ ≤ 2 ^ fieldWidth * 2 ^ fieldWidth :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt high.isLt)⟩

private lemma historyLowValue_join (fieldWidth : Nat)
    (low high : Nat.FixedWidth.Word fieldWidth) :
    historyLowValue fieldWidth (historyJoin fieldWidth low high) = low := by
  apply Fin.ext
  change (low.val + 2 ^ fieldWidth * high.val) % 2 ^ fieldWidth = low.val
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low.isLt]

private lemma historyHighValue_join (fieldWidth : Nat)
    (low high : Nat.FixedWidth.Word fieldWidth) :
    historyHighValue fieldWidth (historyJoin fieldWidth low high) = high := by
  apply Fin.ext
  change (low.val + 2 ^ fieldWidth * high.val) / 2 ^ fieldWidth = high.val
  calc
    (low.val + 2 ^ fieldWidth * high.val) / 2 ^ fieldWidth =
        low.val / 2 ^ fieldWidth + high.val :=
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos fieldWidth)
    _ = 0 + high.val := by rw [Nat.div_eq_of_lt low.isLt]
    _ = high.val := Nat.zero_add _

/-- Replacing the low history half discards its previous low value while
retaining the same high half. -/
@[simp] lemma historyJoin_overwriteLow (fieldWidth : Nat)
    (previous next high : Nat.FixedWidth.Word fieldWidth) :
    historyJoin fieldWidth next
        (historyHighValue fieldWidth
          (historyJoin fieldWidth previous high)) =
      historyJoin fieldWidth next high := by
  rw [historyHighValue_join]

private lemma historyJoin_split (fieldWidth : Nat)
    (history : Nat.FixedWidth.Word (2 * fieldWidth)) :
    historyJoin fieldWidth (historyLowValue fieldWidth history)
      (historyHighValue fieldWidth history) = history := by
  apply Fin.ext
  exact Nat.mod_add_div history.val (2 ^ fieldWidth)

/-- Replace the low compact-history half and preserve the high half. -/
private def setHistoryLow (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    Layout.Registers fieldWidth counterWidth :=
  { registers with arithmetic :=
      { registers.arithmetic with core :=
        { registers.arithmetic.core with
          history := historyJoin fieldWidth value
            (historyHighValue fieldWidth registers.arithmetic.core.history) } } }

/-- Replace the high compact-history half and preserve the low half. -/
private def setHistoryHigh (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    Layout.Registers fieldWidth counterWidth :=
  { registers with arithmetic :=
      { registers.arithmetic with core :=
        { registers.arithmetic.core with
          history := historyJoin fieldWidth
            (historyLowValue fieldWidth registers.arithmetic.core.history) value } } }

/-- Flipping a routed history bit changes only the corresponding compact
history carrier field. -/
private lemma historyValueBit_flip (fieldWidth counterWidth : Nat)
    (bit : Fin (2 * fieldWidth))
    (registers : Layout.Registers fieldWidth counterWidth) :
    (historyValueBit fieldWidth counterWidth bit).flip registers =
      { registers with arithmetic :=
        { registers.arithmetic with
          core :=
            { registers.arithmetic.core with
              history := WireAddress.flipBit
                (WireAddress.littleEndianWire bit)
                registers.arithmetic.core.history } } } := by
  rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
  rcases arithmetic with ⟨core, shared, target⟩
  rcases core with
    ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history, active,
      counter⟩
  simp [historyValueBit, Layout.liftArithmeticBit,
    Layout.rawArithmeticBit, Layout.registerTupleEquiv,
    MK.Compact.liftCoreBit, MK.Compact.rawCoreBit,
    MK.Compact.registerTupleEquiv, MK.RegisterBits.historyBit,
    MK.RegisterBits.tupleHistoryBit, MK.registerTupleEquiv, MK.wordEncoding,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel]

private lemma historyHighValue_flipLow (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth)
    (registers : Layout.Registers fieldWidth counterWidth) :
    historyHighValue fieldWidth
        (((historyLowWord fieldWidth counterWidth).bit bit).flip
          registers).arithmetic.core.history =
      historyHighValue fieldWidth registers.arithmetic.core.history := by
  apply word_eq_of_testBit_eq
  intro high
  simpa [historyHighValue, Nat.testBit_div_two_pow, Nat.add_comm] using
    EncodedBit.get_flip_of_wire_ne
      ((historyLowWord fieldWidth counterWidth).bit bit)
      ((historyHighWord fieldWidth counterWidth).bit high)
      (historyLow_high_ne fieldWidth counterWidth bit high) registers

private lemma historyLowValue_flipHigh (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth)
    (registers : Layout.Registers fieldWidth counterWidth) :
    historyLowValue fieldWidth
        (((historyHighWord fieldWidth counterWidth).bit bit).flip
          registers).arithmetic.core.history =
      historyLowValue fieldWidth registers.arithmetic.core.history := by
  apply word_eq_of_testBit_eq
  intro low
  simpa [historyLowValue, Nat.testBit_mod_two_pow, low.isLt] using
    EncodedBit.get_flip_of_wire_ne
      ((historyHighWord fieldWidth counterWidth).bit bit)
      ((historyLowWord fieldWidth counterWidth).bit low)
      (Ne.symm (historyLow_high_ne fieldWidth counterWidth low bit)) registers

/-- Structural port for the low half of the sole compact history word. -/
def historyLowPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := historyLowWord fieldWidth counterWidth
  read := fun registers =>
    historyLowValue fieldWidth registers.arithmetic.core.history
  set := setHistoryLow fieldWidth counterWidth
  set_read := by
    intro registers
    unfold setHistoryLow
    rw [historyJoin_split]
  read_set := by
    intro registers value
    unfold setHistoryLow
    change historyLowValue fieldWidth
      (historyJoin fieldWidth value
        (historyHighValue fieldWidth registers.arithmetic.core.history)) = value
    exact historyLowValue_join fieldWidth value _
  set_set := by
    intro registers first second
    unfold setHistoryLow
    rw [historyHighValue_join]
  get_bit := by
    intro bit registers
    rw [historyLowWord_get]
    simp [historyLowValue, Nat.testBit_mod_two_pow, bit.isLt]
  pairwise_ne := historyLowWord_pairwise_ne fieldWidth counterWidth
  clear_flip := by
    intro bit registers
    have hhigh := historyHighValue_flipLow fieldWidth counterWidth bit registers
    change historyHighValue fieldWidth
        (((historyValueBit fieldWidth counterWidth
          ⟨bit.val, by omega⟩).flip registers).arithmetic.core.history) =
      historyHighValue fieldWidth registers.arithmetic.core.history at hhigh
    change setHistoryLow fieldWidth counterWidth
        ((historyValueBit fieldWidth counterWidth
          ⟨bit.val, by omega⟩).flip registers) 0 =
      setHistoryLow fieldWidth counterWidth registers 0
    rw [historyValueBit_flip] at hhigh ⊢
    unfold setHistoryLow
    simp [hhigh]

@[simp] lemma historyLowPort_set (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    (historyLowPort fieldWidth counterWidth).set registers value =
      { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with
            history := historyJoin fieldWidth value
              (historyHighValue fieldWidth
                registers.arithmetic.core.history) } } } :=
  rfl

/-- Structural port for the high half of the sole compact history word. -/
def historyHighPort (fieldWidth counterWidth : Nat) :
    Arithmetic.BlockBank.WordPort (Layout.encoding fieldWidth counterWidth)
      fieldWidth where
  word := historyHighWord fieldWidth counterWidth
  read := fun registers =>
    historyHighValue fieldWidth registers.arithmetic.core.history
  set := setHistoryHigh fieldWidth counterWidth
  set_read := by
    intro registers
    unfold setHistoryHigh
    rw [historyJoin_split]
  read_set := by
    intro registers value
    unfold setHistoryHigh
    change historyHighValue fieldWidth
      (historyJoin fieldWidth
        (historyLowValue fieldWidth registers.arithmetic.core.history) value) = value
    exact historyHighValue_join fieldWidth _ value
  set_set := by
    intro registers first second
    unfold setHistoryHigh
    rw [historyLowValue_join]
  get_bit := by
    intro bit registers
    rw [historyHighWord_get]
    simpa [historyHighValue, Nat.add_comm] using
      (Nat.testBit_div_two_pow (n := fieldWidth)
        registers.arithmetic.core.history.val bit.val).symm
  pairwise_ne := historyHighWord_pairwise_ne fieldWidth counterWidth
  clear_flip := by
    intro bit registers
    have hlow := historyLowValue_flipHigh fieldWidth counterWidth bit registers
    change historyLowValue fieldWidth
        (((historyValueBit fieldWidth counterWidth
          ⟨fieldWidth + bit.val, by omega⟩).flip registers).arithmetic.core.history) =
      historyLowValue fieldWidth registers.arithmetic.core.history at hlow
    change setHistoryHigh fieldWidth counterWidth
        ((historyValueBit fieldWidth counterWidth
          ⟨fieldWidth + bit.val, by omega⟩).flip registers) 0 =
      setHistoryHigh fieldWidth counterWidth registers 0
    rw [historyValueBit_flip] at hlow ⊢
    unfold setHistoryHigh
    simp [hlow]

@[simp] lemma historyHighPort_set (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    (historyHighPort fieldWidth counterWidth).set registers value =
      { registers with arithmetic :=
        { registers.arithmetic with core :=
          { registers.arithmetic.core with
            history := historyJoin fieldWidth
              (historyLowValue fieldWidth registers.arithmetic.core.history)
              value } } } :=
  rfl

lemma historyLowPort_read_historyHighPort_set
    (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    (historyLowPort fieldWidth counterWidth).read
        ((historyHighPort fieldWidth counterWidth).set registers value) =
      (historyLowPort fieldWidth counterWidth).read registers := by
  exact historyLowValue_join fieldWidth
    ((historyLowPort fieldWidth counterWidth).read registers) value

lemma historyHighPort_read_historyLowPort_set
    (fieldWidth counterWidth : Nat)
    (registers : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth) :
    (historyHighPort fieldWidth counterWidth).read
        ((historyLowPort fieldWidth counterWidth).set registers value) =
      (historyHighPort fieldWidth counterWidth).read registers := by
  change historyHighValue fieldWidth
      (historyJoin fieldWidth value
        (historyHighValue fieldWidth registers.arithmetic.core.history)) =
    historyHighValue fieldWidth registers.arithmetic.core.history
  exact historyHighValue_join fieldWidth value _

lemma rCoefficientWord_pairwise_ne (fieldWidth counterWidth : Nat) :
    ∀ left right, left ≠ right →
      ((rCoefficientWord fieldWidth counterWidth).bit left).wire ≠
        ((rCoefficientWord fieldWidth counterWidth).bit right).wire := by
  intro left right hne
  apply Layout.liftArithmeticBit_wire_ne
  simpa [rCoefficientWord, CompactCorrection.correctedValueWord,
    CompactCorrection.rCoeffValueWord, MK.RegisterBits.rCoeffValueBit] using
      MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
        (MK.rCoeff_rCoeff_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire (Fin.castSucc left))
          (WireAddress.littleEndianWire (Fin.castSucc right))
          (littleEndianWire_ne
            (fun heq => hne ((Fin.castSucc_injective _) heq))))

lemma mutableX_rCoefficient_ne (fieldWidth counterWidth : Nat) :
    ∀ source target,
      ((Layout.mutableXWord fieldWidth counterWidth).bit source).wire ≠
        ((rCoefficientWord fieldWidth counterWidth).bit target).wire := by
  intro source target
  apply Layout.liftArithmeticBit_wire_ne
  simpa [Layout.mutableXWord, Layout.liftArithmeticWord,
    rCoefficientWord, CompactCorrection.correctedValueWord,
    MK.Compact.vValueWord, CompactCorrection.rCoeffValueWord,
    MK.RegisterBits.vValueBit, MK.RegisterBits.rCoeffValueBit] using
      MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
        (MK.RegisterBits.v_rCoeff_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire source)
          (WireAddress.littleEndianWire (Fin.castSucc target)))

lemma t0_rCoefficient_ne (fieldWidth counterWidth : Nat) :
    ∀ source target,
      ((Layout.t0Word fieldWidth counterWidth).bit source).wire ≠
        ((rCoefficientWord fieldWidth counterWidth).bit target).wire := by
  intro source target
  exact Ne.symm (by
    apply Layout.liftArithmeticBit_wire_ne
    simpa [rCoefficientWord, CompactCorrection.correctedValueWord,
      CompactCorrection.rCoeffValueWord, MK.RegisterBits.rCoeffValueBit,
      Layout.t0Word, Layout.liftArithmeticWord,
      MK.Compact.targetValueWord] using
        MK.Compact.liftCoreBit_targetValueBit_wire_ne fieldWidth counterWidth
          (MK.RegisterBits.rCoeffValueBit fieldWidth counterWidth
            (Fin.castSucc target)) source)

lemma mutableX_t0_ne (fieldWidth counterWidth : Nat) :
    ∀ source target,
      ((Layout.mutableXWord fieldWidth counterWidth).bit source).wire ≠
        ((Layout.t0Word fieldWidth counterWidth).bit target).wire := by
  exact Layout.mutableXWord_wire_ne_t0Word fieldWidth counterWidth

lemma history_rCoefficient_ne (fieldWidth counterWidth : Nat) :
    ∀ historyBit coefficientBit,
      (historyValueBit fieldWidth counterWidth historyBit).wire ≠
        ((rCoefficientWord fieldWidth counterWidth).bit coefficientBit).wire := by
  intro historyBit coefficientBit
  apply Layout.liftArithmeticBit_wire_ne
  simpa [historyValueBit, rCoefficientWord,
    CompactCorrection.correctedValueWord, CompactCorrection.rCoeffValueWord,
    MK.RegisterBits.rCoeffValueBit] using
      MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
        (Ne.symm (MK.RegisterBits.rCoeff_history_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire (Fin.castSucc coefficientBit))
          (WireAddress.littleEndianWire historyBit)))

lemma t0_history_ne (fieldWidth counterWidth : Nat) :
    ∀ targetBit historyBit,
      ((Layout.t0Word fieldWidth counterWidth).bit targetBit).wire ≠
        (historyValueBit fieldWidth counterWidth historyBit).wire := by
  intro targetBit historyBit
  exact Ne.symm (by
    apply Layout.liftArithmeticBit_wire_ne
    simpa [historyValueBit, Layout.t0Word, Layout.liftArithmeticWord,
      MK.Compact.targetValueWord] using
        MK.Compact.liftCoreBit_targetValueBit_wire_ne fieldWidth counterWidth
          (MK.RegisterBits.historyBit fieldWidth counterWidth
            (WireAddress.littleEndianWire historyBit)) targetBit)

lemma mutableX_history_ne (fieldWidth counterWidth : Nat) :
    ∀ source historyBit,
      ((Layout.mutableXWord fieldWidth counterWidth).bit source).wire ≠
        (historyValueBit fieldWidth counterWidth historyBit).wire := by
  intro source historyBit
  apply Layout.liftArithmeticBit_wire_ne
  simpa [Layout.mutableXWord, Layout.liftArithmeticWord,
    MK.Compact.vValueWord, MK.RegisterBits.vValueBit, historyValueBit] using
      MK.Compact.liftCoreBit_wire_ne fieldWidth counterWidth
        (MK.RegisterBits.v_history_wire_ne fieldWidth counterWidth
          (WireAddress.littleEndianWire source)
          (WireAddress.littleEndianWire historyBit))

lemma mutableY_rCoefficient_ne (fieldWidth counterWidth : Nat) :
    ∀ source target,
      ((Layout.mutableYWord fieldWidth counterWidth).bit source).wire ≠
        ((rCoefficientWord fieldWidth counterWidth).bit target).wire := by
  intro source target
  exact Layout.mutableYBit_wire_ne_liftArithmeticBit fieldWidth counterWidth
    source _

lemma lambda_rCoefficient_ne (fieldWidth counterWidth : Nat) :
    ∀ source target,
      ((Layout.lambdaWord fieldWidth counterWidth).bit source).wire ≠
        ((rCoefficientWord fieldWidth counterWidth).bit target).wire := by
  intro source target
  exact Layout.lambdaBit_wire_ne_liftArithmeticBit fieldWidth counterWidth
    source _

lemma mutableY_t0_ne (fieldWidth counterWidth : Nat) :
    ∀ source target,
      ((Layout.mutableYWord fieldWidth counterWidth).bit source).wire ≠
        ((Layout.t0Word fieldWidth counterWidth).bit target).wire := by
  intro source target
  exact Layout.mutableYBit_wire_ne_liftArithmeticBit fieldWidth counterWidth
    source _

lemma lambda_t0_ne (fieldWidth counterWidth : Nat) :
    ∀ source target,
      ((Layout.lambdaWord fieldWidth counterWidth).bit source).wire ≠
        ((Layout.t0Word fieldWidth counterWidth).bit target).wire := by
  intro source target
  exact Layout.lambdaBit_wire_ne_liftArithmeticBit fieldWidth counterWidth
    source _

/-! ## Native routing ledgers -/

/-- Copy a word bitwise on the shared in-place encoding. -/
def copyGates (fieldWidth counterWidth : Nat)
    (source target : EncodedBit.Word
      (Layout.encoding fieldWidth counterWidth) fieldWidth)
    (hsourceTarget : ∀ bit,
      (source.bit bit).wire ≠ (target.bit bit).wire) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  EncodedBit.Word.xorIntoGates source target hsourceTarget

/-- Swap two words bitwise on the shared in-place encoding. -/
def swapGates (fieldWidth counterWidth : Nat)
    (left right : EncodedBit.Word
      (Layout.encoding fieldWidth counterWidth) fieldWidth)
    (hleftRight : ∀ bit,
      (left.bit bit).wire ≠ (right.bit bit).wire) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  EncodedBit.Word.swapGates left right hleftRight

/-- A named routing ledger installs a source port in a clean target port. -/
lemma copyGates_stepList_eq_set_of_clean
    (fieldWidth counterWidth : Nat)
    (source target : Arithmetic.BlockBank.WordPort
      (Layout.encoding fieldWidth counterWidth) fieldWidth)
    (hsourceTarget : ∀ bit,
      (source.word.bit bit).wire ≠ (target.word.bit bit).wire)
    (hcross : ∀ sourceBit targetBit,
      (target.word.bit targetBit).wire ≠
        (source.word.bit sourceBit).wire)
    (state : Layout.Registers fieldWidth counterWidth)
    (value : Nat.FixedWidth.Word fieldWidth)
    (hsource : source.read state = value)
    (htarget : target.read state = 0) :
    EncodedBit.GateSpec.stepList
        (copyGates fieldWidth counterWidth source.word target.word
          hsourceTarget) state =
      target.set state value := by
  exact Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_of_clean
    source target hsourceTarget hcross state value hsource htarget

/-- A named routing ledger clears its target when both ports contain the same
word. -/
lemma copyGates_stepList_eq_set_zero_of_equal
    (fieldWidth counterWidth : Nat)
    (source target : Arithmetic.BlockBank.WordPort
      (Layout.encoding fieldWidth counterWidth) fieldWidth)
    (hsourceTarget : ∀ bit,
      (source.word.bit bit).wire ≠ (target.word.bit bit).wire)
    (hcross : ∀ sourceBit targetBit,
      (target.word.bit targetBit).wire ≠
        (source.word.bit sourceBit).wire)
    (state : Layout.Registers fieldWidth counterWidth)
    (hequal : source.read state = target.read state) :
    EncodedBit.GateSpec.stepList
        (copyGates fieldWidth counterWidth source.word target.word
          hsourceTarget) state =
      target.set state 0 := by
  exact Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_zero_of_equal
    source target hsourceTarget hcross state hequal

@[simp] lemma copyGates_length (fieldWidth counterWidth : Nat)
    (source target : EncodedBit.Word
      (Layout.encoding fieldWidth counterWidth) fieldWidth)
    (hsourceTarget : ∀ bit,
      (source.bit bit).wire ≠ (target.bit bit).wire) :
    (copyGates fieldWidth counterWidth source target hsourceTarget).length =
      fieldWidth := by
  exact EncodedBit.Word.xorIntoGates_length source target hsourceTarget

@[simp] lemma swapGates_length (fieldWidth counterWidth : Nat)
    (left right : EncodedBit.Word
      (Layout.encoding fieldWidth counterWidth) fieldWidth)
    (hleftRight : ∀ bit,
      (left.bit bit).wire ≠ (right.bit bit).wire) :
    (swapGates fieldWidth counterWidth left right hleftRight).length =
      3 * fieldWidth := by
  exact EncodedBit.Word.swapGates_length left right hleftRight

/-- Save `t0` in the low half of the already-present history word. -/
def saveT0LowGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (t0Port fieldWidth counterWidth).word
    (historyLowPort fieldWidth counterWidth).word
    (fun bit => t0_history_ne fieldWidth counterWidth bit
      ⟨bit.val, by omega⟩)

/-- Save mutable `x1` in the high half of the existing history word. -/
def saveXHighGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (mutableXPort fieldWidth counterWidth).word
    (historyHighPort fieldWidth counterWidth).word
    (fun bit => mutableX_history_ne fieldWidth counterWidth bit
      ⟨fieldWidth + bit.val, by omega⟩)

/-- XOR the low saved-history word back into `t0`.  After `saveT0LowGates`,
this clears `t0`; when `t0` is clean, it restores the saved value. -/
def historyLowToT0Gates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (historyLowPort fieldWidth counterWidth).word
    (t0Port fieldWidth counterWidth).word
    (fun bit => Ne.symm (t0_history_ne fieldWidth counterWidth bit
      ⟨bit.val, by omega⟩))

/-- XOR the high saved-history word back into mutable `x1`. -/
def historyHighToXGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (historyHighPort fieldWidth counterWidth).word
    (mutableXPort fieldWidth counterWidth).word
    (fun bit => Ne.symm (mutableX_history_ne fieldWidth counterWidth bit
      ⟨fieldWidth + bit.val, by omega⟩))

/-- Load the low history half into the clean low coefficient word. -/
def historyLowToCoefficientGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (historyLowPort fieldWidth counterWidth).word
    (rCoefficientPort fieldWidth counterWidth).word
    (fun bit => history_rCoefficient_ne fieldWidth counterWidth
      ⟨bit.val, by omega⟩ bit)

/-- Load mutable `x1` into the clean low coefficient word. -/
def xToCoefficientGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (mutableXPort fieldWidth counterWidth).word
    (rCoefficientPort fieldWidth counterWidth).word
    (fun bit => mutableX_rCoefficient_ne fieldWidth counterWidth bit bit)

/-- XOR the low coefficient word into mutable `x1`. -/
def coefficientToXGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (rCoefficientPort fieldWidth counterWidth).word
    (mutableXPort fieldWidth counterWidth).word
    (fun bit => Ne.symm
      (mutableX_rCoefficient_ne fieldWidth counterWidth bit bit))

/-- Load mutable `y1` into the clean low coefficient word. -/
def yToCoefficientGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (mutableYPort fieldWidth counterWidth).word
    (rCoefficientPort fieldWidth counterWidth).word
    (fun bit => mutableY_rCoefficient_ne fieldWidth counterWidth bit bit)

/-- Load temporary `t0` into the clean low coefficient word. -/
def t0ToCoefficientGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (t0Port fieldWidth counterWidth).word
    (rCoefficientPort fieldWidth counterWidth).word
    (fun bit => t0_rCoefficient_ne fieldWidth counterWidth bit bit)

/-- XOR the Montgomery scratch result `t0` into mutable `y1`. -/
def t0ToYGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (t0Port fieldWidth counterWidth).word
    (mutableYPort fieldWidth counterWidth).word
    (fun bit => Ne.symm (mutableY_t0_ne fieldWidth counterWidth bit bit))

/-- XOR the Montgomery scratch result `t0` into persistent `lambda`. -/
def t0ToLambdaGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  copyGates fieldWidth counterWidth
    (t0Port fieldWidth counterWidth).word
    (lambdaPort fieldWidth counterWidth).word
    (fun bit => Ne.symm (lambda_t0_ne fieldWidth counterWidth bit bit))

/-- Exchange mutable `y1` and `lambda`.  This routes a lambda multiplier into
the one external multiplier port used by the Montgomery kernel. -/
def swapYLambdaGates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  swapGates fieldWidth counterWidth
    (mutableYPort fieldWidth counterWidth).word
    (lambdaPort fieldWidth counterWidth).word
    (fun bit => Layout.mutableYBit_wire_ne_lambdaBit
      fieldWidth counterWidth bit bit)

/-- Exchange mutable `x1` and the compact public target `t0`. -/
def swapXT0Gates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  swapGates fieldWidth counterWidth
    (mutableXPort fieldWidth counterWidth).word
    (t0Port fieldWidth counterWidth).word
    (fun bit => mutableX_t0_ne fieldWidth counterWidth bit bit)

/-- Exchange mutable `y1` and the compact public target `t0`. -/
def swapYT0Gates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  swapGates fieldWidth counterWidth
    (mutableYPort fieldWidth counterWidth).word
    (t0Port fieldWidth counterWidth).word
    (fun bit => mutableY_t0_ne fieldWidth counterWidth bit bit)

/-- The named routing swap exchanges exactly the two persistent point words
and leaves the control plus compact arithmetic carrier unchanged. -/
lemma swapYLambdaGates_stepList (fieldWidth counterWidth : Nat)
    (state : Layout.Registers fieldWidth counterWidth) :
    EncodedBit.GateSpec.stepList
        (swapYLambdaGates fieldWidth counterWidth) state =
      { state with mutableY := state.«λ», «λ» := state.mutableY } := by
  let left := mutableYPort fieldWidth counterWidth
  let right := lambdaPort fieldWidth counterWidth
  let hleftRight : ∀ bit,
      (left.word.bit bit).wire ≠ (right.word.bit bit).wire :=
    fun bit => Layout.mutableYBit_wire_ne_lambdaBit
      fieldWidth counterWidth bit bit
  let result := EncodedBit.Word.swapStep left.word right.word hleftRight state
  have hframe : (result.control, result.arithmetic) =
      (state.control, state.arithmetic) := by
    exact EncodedBit.Word.swapStep_preserves_projection left.word right.word
      hleftRight (fun registers => (registers.control, registers.arithmetic))
      (fun bit registers => by
        rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
        rfl)
      (fun bit registers => by
        rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
        rfl)
      state
  have hleftRead : left.read result = right.read state := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← left.get_bit, ← right.get_bit]
    exact EncodedBit.Word.swapStep_get_left left.word right.word hleftRight bit
      (fun other hne => left.pairwise_ne other bit hne)
      (fun other => Ne.symm
        (Layout.mutableYBit_wire_ne_lambdaBit fieldWidth counterWidth bit
          other))
      (fun other =>
        Layout.mutableYBit_wire_ne_lambdaBit fieldWidth counterWidth other bit)
      (fun other hne => right.pairwise_ne other bit hne) state
  have hrightRead : right.read result = left.read state := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← right.get_bit, ← left.get_bit]
    exact EncodedBit.Word.swapStep_get_right left.word right.word hleftRight bit
      (fun other hne => left.pairwise_ne other bit hne)
      (fun other => Ne.symm
        (Layout.mutableYBit_wire_ne_lambdaBit fieldWidth counterWidth bit
          other))
      (fun other =>
        Layout.mutableYBit_wire_ne_lambdaBit fieldWidth counterWidth other bit)
      (fun other hne => right.pairwise_ne other bit hne) state
  change result = _
  rcases state with ⟨control, mutableY, «λ», arithmetic⟩
  rcases result with ⟨resultControl, resultY, resultLambda,
    resultArithmetic⟩
  simp only [left, right, mutableYPort, lambdaPort] at hleftRead hrightRead
  simp only at hframe
  cases hleftRead
  cases hrightRead
  cases hframe
  rfl

/-- The named compact-word swap exchanges exactly mutable `x1` and `t0`. -/
lemma swapXT0Gates_stepList (fieldWidth counterWidth : Nat)
    (state : Layout.Registers fieldWidth counterWidth) :
    EncodedBit.GateSpec.stepList
        (swapXT0Gates fieldWidth counterWidth) state =
      { state with arithmetic :=
        { state.arithmetic with
          core := { state.arithmetic.core with v := state.arithmetic.target }
          target := state.arithmetic.core.v } } := by
  let left := mutableXPort fieldWidth counterWidth
  let right := t0Port fieldWidth counterWidth
  let hleftRight : ∀ bit,
      (left.word.bit bit).wire ≠ (right.word.bit bit).wire :=
    fun bit => mutableX_t0_ne fieldWidth counterWidth bit bit
  let result := EncodedBit.Word.swapStep left.word right.word hleftRight state
  have hframe :
      left.set (right.set result 0) 0 =
        left.set (right.set state 0) 0 := by
    exact EncodedBit.Word.swapStep_preserves_projection left.word right.word
      hleftRight (fun registers => left.set (right.set registers 0) 0)
      (fun bit registers => by
        rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
        rcases arithmetic with ⟨core, shared, target⟩
        rcases core with
          ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history,
            active, counter⟩
        rfl)
      (fun bit registers => by
        rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
        rcases arithmetic with ⟨core, shared, target⟩
        rfl)
      state
  have hleftRead : left.read result = right.read state := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← left.get_bit, ← right.get_bit]
    exact congrFun
      (EncodedBit.Word.swapStep_get_left_word left.word right.word hleftRight
        left.pairwise_ne right.pairwise_ne
        (mutableX_t0_ne fieldWidth counterWidth) state) bit
  have hrightRead : right.read result = left.read state := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← right.get_bit, ← left.get_bit]
    exact congrFun
      (EncodedBit.Word.swapStep_get_right_word left.word right.word hleftRight
        left.pairwise_ne right.pairwise_ne
        (mutableX_t0_ne fieldWidth counterWidth) state) bit
  change result = _
  rcases state with ⟨control, mutableY, «λ», arithmetic⟩
  rcases arithmetic with ⟨core, shared, target⟩
  rcases core with
    ⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history, active,
      counter⟩
  rcases result with ⟨resultControl, resultY, resultLambda,
    resultArithmetic⟩
  rcases resultArithmetic with ⟨resultCore, resultShared, resultTarget⟩
  rcases resultCore with
    ⟨resultU, resultV, resultCompare, resultS, resultR, resultScratchA,
      resultScratchB, resultHistory, resultActive, resultCounter⟩
  simp only [left, right, mutableXPort, t0Port] at hframe hleftRead hrightRead
  cases hleftRead
  cases hrightRead
  cases hframe
  rfl

/-- The named external-word swap exchanges exactly mutable `y1` and `t0`. -/
lemma swapYT0Gates_stepList (fieldWidth counterWidth : Nat)
    (state : Layout.Registers fieldWidth counterWidth) :
    EncodedBit.GateSpec.stepList
        (swapYT0Gates fieldWidth counterWidth) state =
      { state with
        mutableY := state.arithmetic.target
        arithmetic := { state.arithmetic with target := state.mutableY } } := by
  let left := mutableYPort fieldWidth counterWidth
  let right := t0Port fieldWidth counterWidth
  let hleftRight : ∀ bit,
      (left.word.bit bit).wire ≠ (right.word.bit bit).wire :=
    fun bit => mutableY_t0_ne fieldWidth counterWidth bit bit
  let result := EncodedBit.Word.swapStep left.word right.word hleftRight state
  have hframe :
      left.set (right.set result 0) 0 =
        left.set (right.set state 0) 0 := by
    exact EncodedBit.Word.swapStep_preserves_projection left.word right.word
      hleftRight (fun registers => left.set (right.set registers 0) 0)
      (fun bit registers => by
        rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
        rfl)
      (fun bit registers => by
        rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
        rcases arithmetic with ⟨core, shared, target⟩
        rfl)
      state
  have hleftRead : left.read result = right.read state := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← left.get_bit, ← right.get_bit]
    exact congrFun
      (EncodedBit.Word.swapStep_get_left_word left.word right.word hleftRight
        left.pairwise_ne right.pairwise_ne
        (mutableY_t0_ne fieldWidth counterWidth) state) bit
  have hrightRead : right.read result = left.read state := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← right.get_bit, ← left.get_bit]
    exact congrFun
      (EncodedBit.Word.swapStep_get_right_word left.word right.word hleftRight
        left.pairwise_ne right.pairwise_ne
        (mutableY_t0_ne fieldWidth counterWidth) state) bit
  change result = _
  rcases state with ⟨control, mutableY, «λ», arithmetic⟩
  rcases arithmetic with ⟨core, shared, target⟩
  rcases result with ⟨resultControl, resultY, resultLambda,
    resultArithmetic⟩
  rcases resultArithmetic with ⟨resultCore, resultShared, resultTarget⟩
  simp only [left, right, mutableYPort, t0Port] at hframe hleftRead hrightRead
  cases hleftRead
  cases hrightRead
  cases hframe
  rfl

@[simp] lemma saveT0LowGates_length (fieldWidth counterWidth : Nat) :
    (saveT0LowGates fieldWidth counterWidth).length = fieldWidth := by
  unfold saveT0LowGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma saveXHighGates_length (fieldWidth counterWidth : Nat) :
    (saveXHighGates fieldWidth counterWidth).length = fieldWidth := by
  unfold saveXHighGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma historyLowToT0Gates_length (fieldWidth counterWidth : Nat) :
    (historyLowToT0Gates fieldWidth counterWidth).length = fieldWidth := by
  unfold historyLowToT0Gates
  exact copyGates_length _ _ _ _ _

@[simp] lemma historyHighToXGates_length (fieldWidth counterWidth : Nat) :
    (historyHighToXGates fieldWidth counterWidth).length = fieldWidth := by
  unfold historyHighToXGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma historyLowToCoefficientGates_length
    (fieldWidth counterWidth : Nat) :
    (historyLowToCoefficientGates fieldWidth counterWidth).length =
      fieldWidth := by
  unfold historyLowToCoefficientGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma xToCoefficientGates_length (fieldWidth counterWidth : Nat) :
    (xToCoefficientGates fieldWidth counterWidth).length = fieldWidth := by
  unfold xToCoefficientGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma coefficientToXGates_length (fieldWidth counterWidth : Nat) :
    (coefficientToXGates fieldWidth counterWidth).length = fieldWidth := by
  unfold coefficientToXGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma yToCoefficientGates_length (fieldWidth counterWidth : Nat) :
    (yToCoefficientGates fieldWidth counterWidth).length = fieldWidth := by
  unfold yToCoefficientGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma t0ToCoefficientGates_length (fieldWidth counterWidth : Nat) :
    (t0ToCoefficientGates fieldWidth counterWidth).length = fieldWidth := by
  unfold t0ToCoefficientGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma t0ToYGates_length (fieldWidth counterWidth : Nat) :
    (t0ToYGates fieldWidth counterWidth).length = fieldWidth := by
  unfold t0ToYGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma t0ToLambdaGates_length (fieldWidth counterWidth : Nat) :
    (t0ToLambdaGates fieldWidth counterWidth).length = fieldWidth := by
  unfold t0ToLambdaGates
  exact copyGates_length _ _ _ _ _

@[simp] lemma swapYLambdaGates_length (fieldWidth counterWidth : Nat) :
    (swapYLambdaGates fieldWidth counterWidth).length = 3 * fieldWidth := by
  unfold swapYLambdaGates
  exact swapGates_length _ _ _ _ _

@[simp] lemma swapXT0Gates_length (fieldWidth counterWidth : Nat) :
    (swapXT0Gates fieldWidth counterWidth).length = 3 * fieldWidth := by
  unfold swapXT0Gates
  exact swapGates_length _ _ _ _ _

@[simp] lemma swapYT0Gates_length (fieldWidth counterWidth : Nat) :
    (swapYT0Gates fieldWidth counterWidth).length = 3 * fieldWidth := by
  unfold swapYT0Gates
  exact swapGates_length _ _ _ _ _

end
end RegisterRouting
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
