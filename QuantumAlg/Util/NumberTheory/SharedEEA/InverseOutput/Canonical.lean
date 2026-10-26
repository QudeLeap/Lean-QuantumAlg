/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.InverseOutput

/-! # Canonical nonzero residue of the original signed EEA output -/

namespace QuantumAlg.NumberTheory.SharedEEA.InverseOutput

lemma word_le_modulus (modulus input : Nat) (positive : 0 < input)
    (bounded : input < modulus) : (word modulus input positive bounded).val ≤ modulus := by
  have coefficient := (Capacity.iteration_fields_le _ modulus
    (TerminalPadding.final_admissible modulus input positive bounded)
    (TerminalPadding.final_balance modulus input)).2.2.2
  change SignedInvariant.output modulus (TerminalPadding.finalState modulus input)
    (SignedTrajectory.finalIteration modulus input) ≤ modulus
  unfold SignedInvariant.output
  split
  · exact coefficient
  · exact Nat.sub_le _ _

/-- The actual corrected source output is strictly below the modulus on the original domain. -/
lemma word_lt_modulus (modulus input : Nat) (nontrivial : 1 < modulus)
    (coprime : Nat.Coprime input modulus) (positive : 0 < input)
    (bounded : input < modulus) : (word modulus input positive bounded).val < modulus := by
  let : Fact (1 < modulus) := ⟨nontrivial⟩
  have bound := word_le_modulus modulus input positive bounded
  have product := word_product modulus input coprime positive bounded
  have different : (word modulus input positive bounded).val ≠ modulus := by
    intro same
    have impossible : (0 : ZMod modulus) = 1 := by
      simpa only [same, ZMod.natCast_self, mul_zero] using product
    exact zero_ne_one impossible
  omega

/-- No additional zero test premise is needed for a coprime positive-residue inverse. -/
lemma word_positive (modulus input : Nat) (nontrivial : 1 < modulus)
    (coprime : Nat.Coprime input modulus) (positive : 0 < input)
    (bounded : input < modulus) : 0 < (word modulus input positive bounded).val := by
  let : Fact (1 < modulus) := ⟨nontrivial⟩
  have product := word_product modulus input coprime positive bounded
  have different : (word modulus input positive bounded).val ≠ 0 := by
    intro same
    have impossible : (0 : ZMod modulus) = 1 := by
      simpa only [same, Nat.cast_zero, mul_zero] using product
    exact zero_ne_one impossible
  omega

end QuantumAlg.NumberTheory.SharedEEA.InverseOutput
