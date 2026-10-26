/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers.BitExt

/-!
# Exact complete geometry operands and unchanged source registers

Both high source positions are the actual existing prefix bits, even when
they are dirty. The full target includes the original conjunction carry.
The actual native addition changes exactly that target; original metadata,
source words, phases, arbitrary Iter and every prefix position survive.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The full original metadata word, before any padding-zero premise. -/
def fieldValue {width : Nat} (field : Field) (state : Data width) : BitVec width.size :=
  match field with
  | .coefficient => state.1.coefficientLength
  | .quotient => state.1.quotientLength
  | .divisor => state.1.divisorLength
  | .shift => state.1.shift

private lemma fieldBit_get (width : Nat) (field : Field) (index : Fin width.size)
    (state : Data width) :
    (fieldBit width field index).get state = (fieldValue field state).getMsbD index.val := by
  cases field <;>
    simp only [fieldBit, fieldValue, sourceBit_get, coefficientLengthBit_get,
      quotientLengthBit_get, divisorLengthBit_get, shiftBit_get]

/-- The original address retains its actual separate carry as the most significant bit. -/
def targetValue (width : Nat) (state : Data width) : BitVec (fullWidth width) :=
  BitVec.cons state.2.2.2 state.2.1

/-- The two original prefix positions remain part of the complete actual source operand. -/
def sourceValue (width : Nat) (positive : 1 ≤ width) (field : Field) (state : Data width) :
    BitVec (fullWidth width) :=
  BitVec.cons ((prefixBit width ⟨0, by unfold ScanMetadata.addressWidth; omega⟩).get state)
    (BitVec.cons ((prefixBit width ⟨1, by
      have sizePositive := Nat.size_pos.mpr positive
      unfold ScanMetadata.addressWidth
      omega⟩).get state) (fieldValue field state))

/-- Every target coordinate is read in the same declared most-significant-first order. -/
lemma target_get (width : Nat) (state : Data width) (index : Fin (fullWidth width)) :
    ((target width).bit index).get state = (targetValue width state).getMsbD index.val := by
  unfold target
  dsimp only
  split
  · rename_i zero
    simp only [targetValue, zero, BitVec.getMsbD_cons_zero]
    rfl
  · rename_i nonzero
    rw [addressBit_get]
    have successor : index.val = (index.val - 1) + 1 := by omega
    change state.2.1.getMsbD (index.val - 1) =
      (BitVec.cons state.2.2.2 state.2.1).getMsbD index.val
    conv_rhs => rw [successor, BitVec.getMsbD_cons_succ]

/-- Both high padding bits and every metadata bit are the originally declared physical bits. -/
lemma source_get (width : Nat) (positive : 1 ≤ width) (field : Field) (state : Data width)
    (index : Fin (fullWidth width)) :
    ((source width positive field).bit index).get state =
      (sourceValue width positive field state).getMsbD index.val := by
  unfold source
  dsimp only
  split
  · rename_i padding
    have small : index.val = 0 ∨ index.val = 1 := by omega
    rcases small with zero | one
    · simp only [sourceValue, zero, BitVec.getMsbD_cons_zero]
    · simp only [sourceValue, one, BitVec.getMsbD_cons_succ, BitVec.getMsbD_cons_zero]
  · rename_i notPadding
    rw [fieldBit_get]
    have successor : index.val = (index.val - 2) + 1 + 1 := by omega
    unfold sourceValue
    conv_rhs => rw [successor, BitVec.getMsbD_cons_succ, BitVec.getMsbD_cons_succ]

/-- The actual complete native target receives the full padded metadata sum. -/
lemma step_targetValue (width : Nat) (positive : 1 ≤ width) (field : Field) (state : Data width) :
    targetValue width (step width positive field state) =
      sourceValue width positive field state + targetValue width state := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := (placement width positive field).step_target_get state
    (sourceValue width positive field state) (targetValue width state)
    (source_get width positive field state) (target_get width state) ⟨index, within⟩
  change ((target width).bit ⟨index, within⟩).get (step width positive field state) = _ at actual
  rw [target_get] at actual
  exact actual

/-- Every original source register survives the actual geometry operation on all finite labels. -/
lemma step_source (width : Nat) (positive : 1 ≤ width) (field : Field) (state : Data width) :
    (step width positive field state).1 = state.1 := by
  apply Registers.eq_of_bit_get_eq
  intro observed
  apply step_observed width positive field state (sourceBit width observed)
  intro index
  unfold target
  dsimp only
  split
  · exact (source_conjunction_ne width observed).symm
  · exact (source_address_ne width observed _).symm

/-- Both original padding positions and the entire remaining prefix word retain their values. -/
lemma step_prefix (width : Nat) (positive : 1 ≤ width) (field : Field) (state : Data width) :
    (step width positive field state).2.2.1 = state.2.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have outside (other : Fin (fullWidth width)) :
      ((target width).bit other).wire ≠ (prefixBit width ⟨index, within⟩).wire := by
    unfold target
    dsimp only
    split
    · exact (prefix_conjunction_ne width _).symm
    · exact address_prefix_ne width _ _
  simpa only [prefixBit_get] using
    step_observed width positive field state (prefixBit width ⟨index, within⟩) outside

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
