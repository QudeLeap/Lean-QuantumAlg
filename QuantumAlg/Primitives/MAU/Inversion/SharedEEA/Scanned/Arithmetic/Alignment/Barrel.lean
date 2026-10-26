/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Rotation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Readout
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Binary

/-!
# Paid complete-metadata barrel alignment on the original EEA work words

Each original metadata bit controls one actual Fredkin permutation word.
Negative alignment uses the inverse public unit rotation, rather than
repeating a one-bit rotation a quantum-dependent number of times. All
metadata and shared-pool systems remain physically outside the word.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Original work-word positions and the complete original finite metadata field. -/
def barrel (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field) :
    PermutationBarrel (encoding width) (width + 3) width.size where
  bit := ArithmeticRotation.bit width first
  control index := ArithmeticGeometry.fieldBit width field index.rev
  distinct := by
    intro left right same
    apply Fin.ext
    have values := congrArg Fin.val same
    rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
    omega
  separate := by
    intro controlIndex wordIndex same
    have values := congrArg Fin.val same
    rw [ArithmeticGeometry.fieldBit_wire, ArithmeticRotation.bit_value] at values
    have within := wordIndex.isLt
    have metadata := controlIndex.rev.isLt
    cases field <;> cases first <;>
      simp only [ArithmeticGeometry.fieldOffset, Bool.false_eq_true, if_false, if_true] at values
      <;> omega

private lemma control_get (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field)
    (index : Fin width.size) (state : Data width) :
    ((barrel width first field).control index).get state =
      (ArithmeticGeometry.fieldValue field state).getLsbD index.val := by
  change (ArithmeticGeometry.fieldBit width field index.rev).get state = _
  rw [ArithmeticGeometry.fieldBit_get, BitVec.getMsbD_eq_getLsbD]
  simp only [index.rev.isLt, decide_true, Bool.true_and]
  congr 1
  rw [Fin.val_rev]
  have within := index.isLt
  omega

/-- The fixed public inverse unit rotation gives negative readout displacement. -/
def permutation (width : Nat) : Equiv.Perm (Fin (width + 3)) :=
  (finRotate (width + 3))⁻¹

/-- All real native stages execute with no additional quantum system. -/
def gates (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field) :
    List (GateSpec (encoding width)) :=
  (barrel width first field).gates (permutation width)
    (PermutationBarrel.binaryStages width.size)

/-- Every output bit reads exactly its original complete-metadata displaced physical position. -/
lemma gates_bit_get (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width first index).get (GateSpec.stepList (gates width first field)
        state) =
      (ArithmeticRotation.bit width first
        ((permutation width ^ (ArithmeticGeometry.fieldValue field state).toNat) index)).get
        state :=
  (barrel width first field).binary_bit_get (permutation width)
    (ArithmeticGeometry.fieldValue field state) state (fun index => control_get _ _ _ index state)
    index

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
