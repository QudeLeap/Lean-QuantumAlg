/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment
import all QuantumAlg.Util.Permutation.Rotation

/-! # Nonwrapping original positions for both actual terminal readout directions -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates

private lemma positiveRotation_pow {size : Nat} [NeZero size]
    (distance : Nat) (index : Fin size) (fits : index.val + distance < size) :
    ((finRotate size ^ distance) index).val = index.val + distance := by
  let moved : Fin size := ⟨index.val + distance, fits⟩
  have backward : (finRotate size ^ distance).symm moved = index := by
    change ((finRotate size ^ distance)⁻¹) moved = index
    rw [← inv_pow]
    apply Fin.ext
    rw [Permutation.inverseRotation_pow_apply_of_le distance moved (by
      change distance ≤ index.val + distance
      omega)]
    change index.val + distance - distance = index.val
    omega
  have recovered := congrArg (finRotate size ^ distance) backward
  rw [Equiv.apply_symm_apply] at recovered
  exact congrArg Fin.val recovered.symm

/-- Coefficient source order is reversed static placement; divisor order is unchanged. -/
def priorityIndex (width : Nat) (field : Field) (index : Fin (width + 3)) : Fin (width + 3) :=
  match field with
  | .coefficient => index.rev
  | .divisor => index

/-- An admitted prefix reads its exact original source region, with no modular wrap. -/
lemma selected_position (width : Nat) (field : Field) (key : BitVec width.size)
    (index : Fin (region width field key)) :
    ((permutation width field ^ key.toNat)
      (if field = .divisor then
        finRotate (width + 3)
          (priorityIndex width field ⟨index.val, index.isLt.trans_le (region_le width field key)⟩)
      else priorityIndex width field
        ⟨index.val, index.isLt.trans_le (region_le width field key)⟩)) =
      payloadPosition width field key index := by
  have sourceBound := index.isLt
  have : NeZero (width + 3) := ⟨by omega⟩
  apply Fin.ext
  cases field with
  | coefficient =>
      change index.val < width + 3 - key.toNat at sourceBound
      have fits : key.toNat ≤
          (priorityIndex width .coefficient
            ⟨index.val, index.isLt.trans_le (region_le width .coefficient key)⟩).val := by
        simp only [priorityIndex, Fin.val_rev]
        omega
      rw [if_neg (by decide), permutation,
        Permutation.inverseRotation_pow_apply_of_le key.toNat _ fits]
      simp only [priorityIndex, Fin.val_rev, payloadPosition, region]
      omega
  | divisor =>
      change index.val < width + 3 - 1 - key.toNat at sourceBound
      have within : index.val + (key.toNat + 1) < width + 3 := by
        omega
      have step : (finRotate (width + 3)
          (priorityIndex width .divisor
            ⟨index.val, index.isLt.trans_le (region_le width .divisor key)⟩)).val =
          index.val + 1 := by
        apply coe_finRotate_of_ne_last
        intro same
        have values := congrArg Fin.val same
        change index.val = width + 2 at values
        omega
      rw [if_pos rfl, permutation,
        positiveRotation_pow key.toNat _ (by rw [step]; omega), step]
      simp only [payloadPosition, region]
      omega

/-- Actual gates supply the original selected-region bit in its required priority order. -/
lemma gates_selected_get (width : Nat) (field : Field) (first : Bool)
    (state : Data width) (index : Fin (region width field (boundaryValue field state.1))) :
    (ArithmeticRotation.bit width first
      (priorityIndex width field
        ⟨index.val, index.isLt.trans_le (region_le width field _)⟩)).get
        (GateSpec.stepList (gates width field first) state) =
      (ArithmeticRotation.bit width first
        (payloadPosition width field (boundaryValue field state.1) index)).get state := by
  rw [gates_bit_get, selected_position]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment
