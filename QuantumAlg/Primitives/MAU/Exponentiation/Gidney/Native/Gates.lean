/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.ConditionalListLaws
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word
public import QuantumAlg.Util.ZModUnits
public import Mathlib.Data.ZMod.Basic

/-!
# Literal native identity-word loading

The caller-visible exponent and XOR target are accompanied by two internal
words. The first internal word is loaded with the canonical identity and
unloaded again by actual X gates. These gates implement a word XOR on every
binary label, including noncanonical work labels.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open BinaryLabelEncoding EncodedBit EncodedBit.GateSpec Nat.FixedWidth

/-- Internal power/auxiliary words followed by the supplied exponent/target. -/
public abbrev NativeRegisters (exponentWidth width : Nat) :=
  (Fin (2 ^ width) × Fin (2 ^ width)) ×
    (Fin (2 ^ exponentWidth) × Fin (2 ^ width))

private abbrev workEncoding (width : Nat) :=
  BinaryLabelEncoding.prod (finIdentity width) (finIdentity width)

private abbrev inputEncoding (exponentWidth width : Nat) :=
  BinaryLabelEncoding.prod (finIdentity exponentWidth) (finIdentity width)

/-- Binary coordinates in the same logical order as the prepared context. -/
public def nativeEncoding (exponentWidth width : Nat) :
    BinaryLabelEncoding (NativeRegisters exponentWidth width) :=
  prod (workEncoding width) (inputEncoding exponentWidth width)

private def powerBit (exponentWidth width : Nat) (bit : Fin width) :
    EncodedBit (nativeEncoding exponentWidth width) :=
  BinaryLabelEncoding.prodLeftBit _ _ (BinaryLabelEncoding.prodLeftBit _ _
    (BinaryLabelEncoding.finIdentityBit width (WireAddress.littleEndianWire bit)))

private def powerWord (exponentWidth width : Nat) :
    EncodedBit.Word (nativeEncoding exponentWidth width) width where
  bit := powerBit exponentWidth width

private lemma littleEndianWire_ne {width : Nat} {left right : Fin width}
    (different : left ≠ right) :
    WireAddress.littleEndianWire left ≠ WireAddress.littleEndianWire right := by
  intro same
  exact different (WireAddress.bitIndex_injective same)

@[simp] private lemma powerBit_get (exponentWidth width : Nat) (bit : Fin width)
    (state : NativeRegisters exponentWidth width) :
    (powerBit exponentWidth width bit).get state = state.1.1.val.testBit bit.val := by
  change state.1.1.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private lemma xorConstant_preserves_projection {exponentWidth width : Nat} {α : Type}
    (word : EncodedBit.Word (nativeEncoding exponentWidth width) width)
    (project : NativeRegisters exponentWidth width → α)
    (preserved : ∀ bit state,
      project ((word.bit bit).flip state) = project state)
    (value : Fin (2 ^ width)) (state : NativeRegisters exponentWidth width) :
    project (EncodedBit.Word.xorConstantStep
      word value state) = project state := by
  apply stepList_preserves_of_targetFlipPreserves
  intro gate present
  simp only [EncodedBit.Word.xorConstantGates] at present
  obtain ⟨bit, _, rfl⟩ := List.mem_map.mp present
  exact preserved bit

/-- X gates which visibly load the canonical identity word from zero. -/
def identityLoadGates (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) : List (GateSpec (nativeEncoding exponentWidth width)) :=
  EncodedBit.Word.xorConstantGates (powerWord exponentWidth width)
    (unitResidueWord modulus positive 1)

/-- Independent word-level action of XOR loading the first work word. -/
def xorPower {exponentWidth width : Nat}
    (state : NativeRegisters exponentWidth width) (value : Fin (2 ^ width)) :
    NativeRegisters exponentWidth width :=
  ((⟨state.1.1.val ^^^ value.val, Nat.xor_lt_two_pow state.1.1.isLt value.isLt⟩,
      state.1.2), state.2)

private lemma power_bit_ne (exponentWidth width : Nat)
    (left right : Fin width) (different : left ≠ right) :
    (powerBit exponentWidth width left).wire ≠
      (powerBit exponentWidth width right).wire :=
  EncodedBit.GateSpec.prodLeftWire_ne (inputEncoding exponentWidth width)
    (EncodedBit.GateSpec.prodLeftWire_ne (finIdentity width)
      (by
        change WireAddress.littleEndianWire left ≠ WireAddress.littleEndianWire right
        exact littleEndianWire_ne different))

private lemma xorPower_eq_step (exponentWidth width : Nat)
    (value : Fin (2 ^ width)) (state : NativeRegisters exponentWidth width) :
    xorPower state value =
      EncodedBit.Word.xorConstantStep (powerWord exponentWidth width) value state := by
  apply Prod.ext
  · apply Prod.ext
    · apply Nat.FixedWidth.word_eq_of_testBit_eq
      intro bit
      have action := EncodedBit.Word.xorConstantStep_get_target
        (powerWord exponentWidth width) value bit
        (fun other different => power_bit_ne exponentWidth width other bit different) state
      change (powerBit exponentWidth width bit).get
          (EncodedBit.Word.xorConstantStep (powerWord exponentWidth width) value state) =
        ((powerBit exponentWidth width bit).get state ^^ value.val.testBit bit.val) at action
      rw [powerBit_get, powerBit_get] at action
      have left : (xorPower state value).1.1.val.testBit bit.val =
          (state.1.1.val.testBit bit.val ^^ value.val.testBit bit.val) := by
        exact Nat.testBit_xor state.1.1.val value.val bit.val
      exact left.trans action.symm
    · exact (xorConstant_preserves_projection (powerWord exponentWidth width)
        (fun current => current.1.2) (fun _ _ => rfl) value state).symm
  · exact (xorConstant_preserves_projection (powerWord exponentWidth width)
      Prod.snd (fun _ _ => rfl) value state).symm

/-- The actual identity loader is exactly the independent first-word XOR. -/
lemma identityLoadGates_step (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (state : NativeRegisters exponentWidth width) :
    stepList (identityLoadGates exponentWidth width modulus positive) state =
      xorPower state (unitResidueWord modulus positive 1) := by
  change EncodedBit.Word.xorConstantStep (powerWord exponentWidth width)
    (unitResidueWord modulus positive 1) state = _
  exact (xorPower_eq_step exponentWidth width _ state).symm

end

end QuantumAlg.MAU.Exponentiation.Gidney
