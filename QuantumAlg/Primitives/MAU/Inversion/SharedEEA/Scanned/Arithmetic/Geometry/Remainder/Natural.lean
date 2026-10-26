/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Remainder
import all QuantumAlg.Util.NumberTheory.SharedEEA.Geometry.Word

/-!
# Exact natural lengths from the actual full-carry geometry circuit

The actual padding and temporary-target zero promises discharge the
physical preparation boundary. The resulting complete temporary word
retains every metadata carry, including wrapped negative lengths on
arbitrary finite source fields [LYL+26, sec_EEA/sub_regshare.tex:278,291-298].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Actual zero padding, rather than discarded high bits, gives the full metadata extension. -/
lemma sourceValue_eq_extend (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    sourceValue width positive field state = ScanGeometry.extend (fieldValue field state) := by
  apply BitVec.eq_of_toNat_eq
  exact (sourceValue_toNat_of_prefix_zero width positive field state clean).trans
    (ScanGeometry.extend_toNat (fieldValue field state)).symm

/-- The actual fixed native sequence prepares precisely the complete mathematical remainder word. -/
lemma remainderStep_targetWord (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : targetValue width state = 0#(fullWidth width)) :
    targetValue width (remainderStep width positive state) =
      ScanGeometry.remainderWord state.1.coefficientLength
        state.1.quotientLength state.1.shift := by
  rw [remainderStep_targetValue, zero, BitVec.zero_xor,
    sourceValue_eq_extend width positive .coefficient state clean,
    sourceValue_eq_extend width positive .quotient state clean,
    sourceValue_eq_extend width positive .shift state clean]
  rfl

/-- The exact natural residue follows from the real circuit, without a source-trajectory premise. -/
lemma remainderStep_target_toNat (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : targetValue width state = 0#(fullWidth width)) :
    (targetValue width (remainderStep width positive state)).toNat =
      ScanGeometry.residue (2 ^ fullWidth width) (width + 3)
        (state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
          state.1.shift.toNat) := by
  rw [remainderStep_targetWord width positive state clean zero, ScanGeometry.remainderWord_toNat]

/-- Complete finite source metadata pass the exact untruncated positive-window test. -/
lemma remainderStep_target_positive_iff (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : targetValue width state = 0#(fullWidth width)) :
    (0 < (targetValue width (remainderStep width positive state)).toNat ∧
      (targetValue width (remainderStep width positive state)).toNat ≤ width + 3) ↔
      state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
        state.1.shift.toNat < width + 3 := by
  rw [remainderStep_targetWord width positive state clean zero]
  exact ScanGeometry.remainderWord_positive_iff _ _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
