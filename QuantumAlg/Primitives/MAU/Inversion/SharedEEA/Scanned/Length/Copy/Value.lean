/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Positive
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Components.Encoded.BitGates.Word.ValueXor

/-! # Full actual length-copy action has the original finite metadata XOR convention -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Mathematical finite value of the actual low prefix; it is never passed to a program builder. -/
def value (width : Nat) (state : Data width) : BitVec width.size :=
  state.2.2.1.extractLsb' 0 width.size

private lemma data_get (width : Nat) (bit : Fin width.size) (state : Data width) :
    (dataBit width bit).get state = (value width state).getLsbD bit.val := by
  have position : ScanMetadata.addressWidth width - 1 - bit.rev.succ.val = bit.val := by
    simp only [ScanMetadata.addressWidth, Fin.val_succ, Fin.val_rev]
    have within := bit.isLt
    omega
  simp only [dataBit, prefixBit_get, BitVec.getMsbD_eq_getLsbD, bit.rev.succ.isLt,
    decide_true, Bool.true_and, position, value, BitVec.getLsbD_extractLsb', bit.isLt,
    Nat.zero_add]

private lemma target_distinct (width : Nat) (field : Field) :
    Function.Injective (fun index => ((target width field).bit index).wire) := by
  intro left right same
  have values := congrArg Fin.val same
  change (sourceBit width (outputBit width field left)).wire.val =
    (sourceBit width (outputBit width field right)).wire.val at values
  rw [sourceBit_wire, sourceBit_wire] at values
  have first := left.isLt
  have second := right.isLt
  apply Fin.ext
  cases field <;>
    simp only [outputBit, SharedEEA.coefficientLengthBit_wire, SharedEEA.divisorLengthBit_wire,
      Fin.val_rev] at values <;> omega

/-- The actual quantum word XOR has exactly the original arbitrary-target finite value action. -/
lemma xorIntoStep_eq_constant (width : Nat) (field : Field) (state : Data width) :
    Word.xorIntoStep (source width) (target width field) (source_target width field) state =
      Word.xorConstantStep (target width field) (value width state).toFin state := by
  apply Word.xorIntoStep_eq_xorConstantStep (source width) (target width field)
    (fun input output =>
      (source_prefix_ne width (outputBit width field output) input.rev.succ).symm)
    (target_distinct width field) (encoding_surjective width)
  intro index
  exact data_get width index state

/-- Complete native copy agrees with selected finite XOR and returns all other physical inputs. -/
lemma step_eq_constant (width : Nat) (poolFlag : Bool) (field : Field) (state : Data width) :
    step width poolFlag field state =
      if (active width poolFlag).get state && !(conjunctionBit width).get state then
        Word.xorConstantStep (target width field) (value width state).toFin state
      else state := by
  unfold step
  rw [xorIntoStep_eq_constant]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthCopy
