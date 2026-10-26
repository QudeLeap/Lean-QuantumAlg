/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Frame

/-! # Exact complete physical range of the two original work words -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed

noncomputable section

open EncodedBit

/-- The pair contains exactly the original two full work words, with no metadata or pool bit. -/
lemma operands_range_iff (width : Nat) (observed : Fin (encoding width).width) :
    observed ∈ Set.range (operands width).wires ↔ observed.val < 2 * (width + 3) := by
  constructor
  · rintro ⟨selected, rfl⟩
    refine Fin.addCases (m := width + 3) (n := width + 3)
      (fun first => ?_) (fun second => ?_) selected
    · change ((wordPairSubsystem _ _ _ _ _).wires
        (Fin.castAdd (width + 3) first)).val < _
      rw [wordPairSubsystem_left, ArithmeticRotation.bit_value]
      simp only [if_true, zero_add]
      have within := first.isLt
      omega
    · change ((wordPairSubsystem _ _ _ _ _).wires
        (Fin.natAdd (width + 3) second)).val < _
      rw [wordPairSubsystem_right, ArithmeticRotation.bit_value]
      simp only [Bool.false_eq_true, if_false]
      have within := second.isLt
      omega
  · intro inside
    by_cases first : observed.val < width + 3
    · let index : Fin (width + 3) := ⟨observed.val, first⟩
      refine ⟨Fin.castAdd (width + 3) index, ?_⟩
      change (wordPairSubsystem _ _ _ _ _).wires (Fin.castAdd (width + 3) index) = _
      rw [wordPairSubsystem_left]
      apply Fin.ext
      rw [ArithmeticRotation.bit_value]
      simp only [if_true, zero_add]
      rfl
    · let index : Fin (width + 3) := ⟨observed.val - (width + 3), by omega⟩
      refine ⟨Fin.natAdd (width + 3) index, ?_⟩
      change (wordPairSubsystem _ _ _ _ _).wires (Fin.natAdd (width + 3) index) = _
      rw [wordPairSubsystem_right]
      apply Fin.ext
      rw [ArithmeticRotation.bit_value]
      simp only [Bool.false_eq_true, if_false]
      change width + 3 + (observed.val - (width + 3)) = observed.val
      omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed
