/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Layout

/-!
# In-place affine point-addition carrier

This module fixes the physical carrier used by the in-place controlled affine
point-addition schedule.  The mutable `x1` word is the compact inversion input
`core.v`, and temporary `t0` is its public `target`; only `y1`, `lambda`, and
the outer control live beside that carrier.  The fixed addend is a classical
gate parameter, and no second point or output register is allocated [RNSL17,
ECDLP.tex:490-555,656-691].

The compact inversion target is the temporary `t0` word.  Its remaining
restored fields are reused by the multiplication, squaring, and modular
addition stages rather than appended as a second arithmetic workspace.  The
single VBE coefficient-adder bank already accounted for by the compact
inversion is therefore the sole width deviation from RNSL17.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace Layout

noncomputable section

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK

/-- Named in-place point-addition carrier. -/
structure Registers (fieldWidth counterWidth : Nat) where
  /-- The outer bit selecting addition by the fixed classical point. -/
  control : Bool
  /-- Mutable affine y coordinate. -/
  mutableY : Word fieldWidth
  /-- Persistent slope temporary from the source straight-line program. -/
  «λ» : Word fieldWidth
  /-- Compact inversion carrier, reused by every arithmetic stage. -/
  arithmetic : MK.Compact.Registers fieldWidth counterWidth
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprRegisters.repr

/-- Product view used by the physical encoding. -/
abbrev RegisterTuple (fieldWidth counterWidth : Nat) :=
  Bool ×
    (Word fieldWidth ×
      (Word fieldWidth × MK.Compact.Registers fieldWidth counterWidth))

/-- All in-place carrier fields except the leading control bit. -/
abbrev TailRegisters (fieldWidth counterWidth : Nat) :=
  Word fieldWidth ×
    (Word fieldWidth × MK.Compact.Registers fieldWidth counterWidth)

/-- Width-parametric encoding of the in-place carrier tail. -/
@[implicit_reducible]
def tailEncoding (fieldWidth counterWidth : Nat) :
    BinaryLabelEncoding (TailRegisters fieldWidth counterWidth) :=
  BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (MK.Compact.encoding fieldWidth counterWidth))

/-- Fieldwise equivalence between the named and product carriers. -/
def registerTupleEquiv (fieldWidth counterWidth : Nat) :
    Registers fieldWidth counterWidth ≃ RegisterTuple fieldWidth counterWidth where
  toFun := fun registers =>
    (registers.control,
      (registers.mutableY, (registers.«λ», registers.arithmetic)))
  invFun := fun registers =>
    { control := registers.1
      mutableY := registers.2.1
      «λ» := registers.2.2.1
      arithmetic := registers.2.2.2 }
  left_inv := by
    intro registers
    cases registers
    rfl
  right_inv := by
    intro registers
    rcases registers with ⟨control, mutableY, «λ», arithmetic⟩
    rfl

/-- Product encoding before restoring field names. -/
@[implicit_reducible]
def registerTupleEncoding (fieldWidth counterWidth : Nat) :
    BinaryLabelEncoding (RegisterTuple fieldWidth counterWidth) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (tailEncoding fieldWidth counterWidth)

/-- Exact physical encoding of the in-place point-addition carrier. -/
@[implicit_reducible]
def encoding (fieldWidth counterWidth : Nat) :
    BinaryLabelEncoding (Registers fieldWidth counterWidth) :=
  (registerTupleEncoding fieldWidth counterWidth).relabel
    (registerTupleEquiv fieldWidth counterWidth)

/-- Encoding a named carrier is symbolically the leading control label
followed by the encoded tail. -/
theorem encoding_encode_control_tail (fieldWidth counterWidth : Nat)
    (registers : Registers fieldWidth counterWidth) :
    (encoding fieldWidth counterWidth).encode registers =
      prodEquiv
        (BinaryLabelEncoding.bool.encode registers.control,
          (tailEncoding fieldWidth counterWidth).encode
            (registers.mutableY, (registers.«λ», registers.arithmetic))) := by
  rfl

/-! ## Addressed fields -/

/-- Outer control bit before restoring named fields. -/
def rawControlBit (fieldWidth counterWidth : Nat) :
    EncodedBit (registerTupleEncoding fieldWidth counterWidth) :=
  BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth)))
    BinaryLabelEncoding.boolBit

/-- One little-endian mutable-y bit before restoring named fields. -/
def rawMutableYBit (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth) :
    EncodedBit (registerTupleEncoding fieldWidth counterWidth) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth)))
    (BinaryLabelEncoding.prodLeftBit (MK.wordEncoding fieldWidth)
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth))
      (BinaryLabelEncoding.finIdentityBit fieldWidth
        (WireAddress.littleEndianWire bit)))

/-- One little-endian slope bit before restoring named fields. -/
def rawLambdaBit (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth) :
    EncodedBit (registerTupleEncoding fieldWidth counterWidth) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth)))
    (BinaryLabelEncoding.prodRightBit (MK.wordEncoding fieldWidth)
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth))
      (BinaryLabelEncoding.prodLeftBit (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth)
        (BinaryLabelEncoding.finIdentityBit fieldWidth
          (WireAddress.littleEndianWire bit))))

/-- One compact-arithmetic bit before restoring named fields. -/
def rawArithmeticBit (fieldWidth counterWidth : Nat)
    (bit : EncodedBit (MK.Compact.encoding fieldWidth counterWidth)) :
    EncodedBit (registerTupleEncoding fieldWidth counterWidth) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth)))
    (BinaryLabelEncoding.prodRightBit (MK.wordEncoding fieldWidth)
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth))
      (BinaryLabelEncoding.prodRightBit (MK.wordEncoding fieldWidth)
        (MK.Compact.encoding fieldWidth counterWidth) bit))

/-- Addressed outer control bit. -/
def controlBit (fieldWidth counterWidth : Nat) :
    EncodedBit (encoding fieldWidth counterWidth) :=
  (rawControlBit fieldWidth counterWidth).relabel
    (registerTupleEquiv fieldWidth counterWidth)

/-- Addressed little-endian mutable-y bit. -/
def mutableYBit (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth) :
    EncodedBit (encoding fieldWidth counterWidth) :=
  (rawMutableYBit fieldWidth counterWidth bit).relabel
    (registerTupleEquiv fieldWidth counterWidth)

/-- Addressed little-endian persistent-slope bit. -/
def lambdaBit (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth) :
    EncodedBit (encoding fieldWidth counterWidth) :=
  (rawLambdaBit fieldWidth counterWidth bit).relabel
    (registerTupleEquiv fieldWidth counterWidth)

/-- Lift one compact-arithmetic bit into the point-addition carrier. -/
def liftArithmeticBit (fieldWidth counterWidth : Nat)
    (bit : EncodedBit (MK.Compact.encoding fieldWidth counterWidth)) :
    EncodedBit (encoding fieldWidth counterWidth) :=
  (rawArithmeticBit fieldWidth counterWidth bit).relabel
    (registerTupleEquiv fieldWidth counterWidth)

/-- Mutable-y word view. -/
def mutableYWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (encoding fieldWidth counterWidth) fieldWidth where
  bit := mutableYBit fieldWidth counterWidth

/-- Persistent slope word view. -/
def lambdaWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (encoding fieldWidth counterWidth) fieldWidth where
  bit := lambdaBit fieldWidth counterWidth

/-- Lift one complete compact-arithmetic word into the point-addition carrier. -/
def liftArithmeticWord (fieldWidth counterWidth wordWidth : Nat)
    (word : EncodedBit.Word
      (MK.Compact.encoding fieldWidth counterWidth) wordWidth) :
    EncodedBit.Word (encoding fieldWidth counterWidth) wordWidth where
  bit := fun bit => liftArithmeticBit fieldWidth counterWidth (word.bit bit)

/-- Mutable-x word view.  This is definitionally the compact inversion input,
not a word appended to the inversion carrier. -/
def mutableXWord (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (encoding fieldWidth counterWidth) fieldWidth :=
  liftArithmeticWord fieldWidth counterWidth fieldWidth
    (MK.Compact.vValueWord fieldWidth counterWidth)

/-- Source `t0` temporary.  This is definitionally the compact inversion
target rather than a separate output word. -/
def t0Word (fieldWidth counterWidth : Nat) :
    EncodedBit.Word (encoding fieldWidth counterWidth) fieldWidth :=
  liftArithmeticWord fieldWidth counterWidth fieldWidth
    (MK.Compact.targetValueWord fieldWidth counterWidth)

@[simp] theorem controlBit_get (fieldWidth counterWidth : Nat)
    (registers : Registers fieldWidth counterWidth) :
    (controlBit fieldWidth counterWidth).get registers = registers.control := by
  rfl

@[simp] theorem mutableYBit_get (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) (registers : Registers fieldWidth counterWidth) :
    (mutableYBit fieldWidth counterWidth bit).get registers =
      registers.mutableY.val.testBit bit.val := by
  change
    (BinaryLabelEncoding.finIdentityBit fieldWidth
      (WireAddress.littleEndianWire bit)).get registers.mutableY = _
  simp [BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit]

@[simp] theorem lambdaBit_get (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) (registers : Registers fieldWidth counterWidth) :
    (lambdaBit fieldWidth counterWidth bit).get registers =
      registers.«λ».val.testBit bit.val := by
  change
    (BinaryLabelEncoding.finIdentityBit fieldWidth
      (WireAddress.littleEndianWire bit)).get registers.«λ» = _
  simp [BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit]

@[simp] theorem liftArithmeticBit_get (fieldWidth counterWidth : Nat)
    (bit : EncodedBit (MK.Compact.encoding fieldWidth counterWidth))
    (registers : Registers fieldWidth counterWidth) :
    (liftArithmeticBit fieldWidth counterWidth bit).get registers =
      bit.get registers.arithmetic := by
  rfl

/-! ## Physical separation -/

/-- Every mutable-y bit is separated from the outer control. -/
theorem mutableYBit_wire_ne_controlBit (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) :
    (mutableYBit fieldWidth counterWidth bit).wire ≠
      (controlBit fieldWidth counterWidth).wire := by
  have hraw :=
    EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth)))
      (BinaryLabelEncoding.prodLeftBit (MK.wordEncoding fieldWidth)
        (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth))
        (BinaryLabelEncoding.finIdentityBit fieldWidth
          (WireAddress.littleEndianWire bit)))
      BinaryLabelEncoding.boolBit
  intro hwire
  apply hraw
  apply Fin.ext
  simpa only [mutableYBit, controlBit, rawMutableYBit, rawControlBit,
    EncodedBit.relabel] using congrArg Fin.val hwire

/-- Every persistent-slope bit is separated from the outer control. -/
theorem lambdaBit_wire_ne_controlBit (fieldWidth counterWidth : Nat)
    (bit : Fin fieldWidth) :
    (lambdaBit fieldWidth counterWidth bit).wire ≠
      (controlBit fieldWidth counterWidth).wire := by
  have hraw :=
    EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth)))
      (BinaryLabelEncoding.prodRightBit (MK.wordEncoding fieldWidth)
        (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth))
        (BinaryLabelEncoding.prodLeftBit (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth)
          (BinaryLabelEncoding.finIdentityBit fieldWidth
            (WireAddress.littleEndianWire bit))))
      BinaryLabelEncoding.boolBit
  intro hwire
  apply hraw
  apply Fin.ext
  simpa only [lambdaBit, controlBit, rawLambdaBit, rawControlBit,
    EncodedBit.relabel] using congrArg Fin.val hwire

/-- Every compact-arithmetic bit is separated from the outer control. -/
theorem liftArithmeticBit_wire_ne_controlBit
    (fieldWidth counterWidth : Nat)
    (bit : EncodedBit (MK.Compact.encoding fieldWidth counterWidth)) :
    (liftArithmeticBit fieldWidth counterWidth bit).wire ≠
      (controlBit fieldWidth counterWidth).wire := by
  have hraw :=
    EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
      BinaryLabelEncoding.bool
      (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
        (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth)))
      (BinaryLabelEncoding.prodRightBit (MK.wordEncoding fieldWidth)
        (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth))
        (BinaryLabelEncoding.prodRightBit (MK.wordEncoding fieldWidth)
          (MK.Compact.encoding fieldWidth counterWidth) bit))
      BinaryLabelEncoding.boolBit
  intro hwire
  apply hraw
  apply Fin.ext
  simpa only [liftArithmeticBit, controlBit, rawArithmeticBit, rawControlBit,
    EncodedBit.relabel] using congrArg Fin.val hwire

/-- Mutable y and the persistent slope occupy different product branches. -/
theorem mutableYBit_wire_ne_lambdaBit
    (fieldWidth counterWidth : Nat) (yBit lambdaIndex : Fin fieldWidth) :
    (mutableYBit fieldWidth counterWidth yBit).wire ≠
      (lambdaBit fieldWidth counterWidth lambdaIndex).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (MK.wordEncoding fieldWidth)
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (MK.Compact.encoding fieldWidth counterWidth))
    (BinaryLabelEncoding.prodLeftBit (MK.wordEncoding fieldWidth)
      (MK.Compact.encoding fieldWidth counterWidth)
      (BinaryLabelEncoding.finIdentityBit fieldWidth
        (WireAddress.littleEndianWire lambdaIndex)))
    (BinaryLabelEncoding.finIdentityBit fieldWidth
      (WireAddress.littleEndianWire yBit))).symm

/-- Mutable y and every compact-arithmetic bit occupy different product branches. -/
theorem mutableYBit_wire_ne_liftArithmeticBit
    (fieldWidth counterWidth : Nat) (yBit : Fin fieldWidth)
    (arithmeticBit : EncodedBit
      (MK.Compact.encoding fieldWidth counterWidth)) :
    (mutableYBit fieldWidth counterWidth yBit).wire ≠
      (liftArithmeticBit fieldWidth counterWidth arithmeticBit).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (MK.wordEncoding fieldWidth)
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (MK.Compact.encoding fieldWidth counterWidth))
    (BinaryLabelEncoding.prodRightBit (MK.wordEncoding fieldWidth)
      (MK.Compact.encoding fieldWidth counterWidth) arithmeticBit)
    (BinaryLabelEncoding.finIdentityBit fieldWidth
      (WireAddress.littleEndianWire yBit))).symm

/-- The persistent slope and every compact-arithmetic bit occupy different
product branches. -/
theorem lambdaBit_wire_ne_liftArithmeticBit
    (fieldWidth counterWidth : Nat) (lambdaIndex : Fin fieldWidth)
    (arithmeticBit : EncodedBit
      (MK.Compact.encoding fieldWidth counterWidth)) :
    (lambdaBit fieldWidth counterWidth lambdaIndex).wire ≠
      (liftArithmeticBit fieldWidth counterWidth arithmeticBit).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  apply EncodedBit.GateSpec.prodRightWire_ne (MK.wordEncoding fieldWidth)
  exact (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (MK.wordEncoding fieldWidth)
    (MK.Compact.encoding fieldWidth counterWidth) arithmeticBit
    (BinaryLabelEncoding.finIdentityBit fieldWidth
      (WireAddress.littleEndianWire lambdaIndex))).symm

/-- Distinct mutable-y positions occupy distinct wires. -/
theorem mutableYBit_wire_ne (fieldWidth counterWidth : Nat)
    (left right : Fin fieldWidth) (hne : left ≠ right) :
    (mutableYBit fieldWidth counterWidth left).wire ≠
      (mutableYBit fieldWidth counterWidth right).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  apply EncodedBit.GateSpec.prodLeftWire_ne
    (BinaryLabelEncoding.prod (MK.wordEncoding fieldWidth)
      (MK.Compact.encoding fieldWidth counterWidth))
  change WireAddress.littleEndianWire left ≠ WireAddress.littleEndianWire right
  intro hwire
  apply hne
  exact WireAddress.bitIndex_injective hwire

/-- Distinct persistent-slope positions occupy distinct wires. -/
theorem lambdaBit_wire_ne (fieldWidth counterWidth : Nat)
    (left right : Fin fieldWidth) (hne : left ≠ right) :
    (lambdaBit fieldWidth counterWidth left).wire ≠
      (lambdaBit fieldWidth counterWidth right).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
  apply EncodedBit.GateSpec.prodRightWire_ne (MK.wordEncoding fieldWidth)
  apply EncodedBit.GateSpec.prodLeftWire_ne
    (MK.Compact.encoding fieldWidth counterWidth)
  change WireAddress.littleEndianWire left ≠ WireAddress.littleEndianWire right
  intro hwire
  apply hne
  exact WireAddress.bitIndex_injective hwire

/-- Lifting compact bits into the point-addition carrier preserves physical
separation. -/
theorem liftArithmeticBit_wire_ne (fieldWidth counterWidth : Nat)
    (left right : EncodedBit (MK.Compact.encoding fieldWidth counterWidth))
    (hne : left.wire ≠ right.wire) :
    (liftArithmeticBit fieldWidth counterWidth left).wire ≠
      (liftArithmeticBit fieldWidth counterWidth right).wire := by
  have hraw := EncodedBit.GateSpec.prodRightWire_ne BinaryLabelEncoding.bool
      (EncodedBit.GateSpec.prodRightWire_ne (MK.wordEncoding fieldWidth)
        (EncodedBit.GateSpec.prodRightWire_ne
          (MK.wordEncoding fieldWidth) hne))
  intro hwire
  apply hraw
  apply Fin.ext
  simpa only [liftArithmeticBit, rawArithmeticBit, EncodedBit.relabel] using
    congrArg Fin.val hwire

/-- The mutable-x input and `t0` output are distinct words inside the compact
carrier; neither is an appended point-addition register. -/
theorem mutableXWord_wire_ne_t0Word
    (fieldWidth counterWidth : Nat) (xBit t0Bit : Fin fieldWidth) :
    ((mutableXWord fieldWidth counterWidth).bit xBit).wire ≠
      ((t0Word fieldWidth counterWidth).bit t0Bit).wire := by
  apply liftArithmeticBit_wire_ne
  simpa only [MK.Compact.vValueWord, MK.Compact.targetValueWord] using
    MK.Compact.liftCoreBit_targetValueBit_wire_ne fieldWidth counterWidth
      (MK.RegisterBits.vValueBit fieldWidth counterWidth xBit) t0Bit

/-! ## Exact width -/

/-- The in-place carrier adds exactly two field words and one control bit to
the compact inversion carrier. -/
theorem encoding_width_exact (fieldWidth counterWidth : Nat)
    (hcounter : 0 < counterWidth) :
    (encoding fieldWidth counterWidth).width =
      10 * fieldWidth + 2 * counterWidth + 9 := by
  simp only [encoding, registerTupleEncoding,
    tailEncoding,
    BinaryLabelEncoding.relabel_width, BinaryLabelEncoding.prod_width,
    BinaryLabelEncoding.bool_width, MK.wordEncoding_width,
    MK.Compact.encoding_width_exact fieldWidth counterWidth hcounter]
  omega

/-- Canonical in-place carrier at the exact fixed-round counter width. -/
def encodingFor (fieldWidth : Nat) :
    BinaryLabelEncoding
      (Registers fieldWidth (MK.Compact.counterWidthFor fieldWidth)) :=
  encoding fieldWidth (MK.Compact.counterWidthFor fieldWidth)

/-- Exact VBE-retaining point-addition width.  No constant or output point is
present in this formula. -/
theorem encodingFor_width_exact (fieldWidth : Nat) (hfield : 0 < fieldWidth) :
    (encodingFor fieldWidth).width =
      10 * fieldWidth + 2 * Nat.clog 2 fieldWidth + 11 := by
  change (encoding fieldWidth
    (MK.Compact.counterWidthFor fieldWidth)).width = _
  have hcounter : 0 < MK.Compact.counterWidthFor fieldWidth := by
    unfold MK.Compact.counterWidthFor
    exact Nat.clog_pos (by omega) (by omega)
  rw [encoding_width_exact fieldWidth
    (MK.Compact.counterWidthFor fieldWidth) hcounter]
  rw [MK.Compact.counterWidthFor,
    MK.Compact.clog_two_mul_eq_add_one fieldWidth hfield]
  omega

/-- The P-256 in-place controlled point-addition carrier has exactly 2587
logical qubits. -/
theorem encodingFor_256_width : (encodingFor 256).width = 2587 := by
  rw [encodingFor_width_exact 256 (by omega)]
  norm_num

end
end Layout
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
