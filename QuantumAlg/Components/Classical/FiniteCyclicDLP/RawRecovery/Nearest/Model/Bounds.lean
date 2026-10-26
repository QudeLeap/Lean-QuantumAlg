/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Model

/-!
# Range of the original raw candidate

The original optional recovery contains a canonical residue on success.
Its actual three-cell representation uses a zero candidate on inverse failure.
Both branches therefore supply a natural candidate below the original modulus;
the fixed-width encoding does not truncate any successful residue.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open ClassicalAlgorithms.Modular

noncomputable section

/-- Every original three-cell candidate lies below the modulus, including inverse failure. -/
lemma outputCells_candidate_lt {width : Nat} (spec : ModulusSpec width)
    (input : CShape.Value (InputShape width)) :
    (outputCellsInput spec input).second.first.toNat < spec.modulus := by
  change (outputCellsNormalized spec (normalizeInput spec input)).second.first.toNat < spec.modulus
  cases selected : outputOfNormalized spec (normalizeInput spec input) with
  | none =>
      rw [outputCellsNormalized_of_none spec (normalizeInput spec input) selected]
      change 0 % 2 ^ width < spec.modulus
      rw [Nat.zero_mod]
      exact lt_of_lt_of_le (by decide : 0 < 2) spec.two_le
  | some output =>
      rw [outputCellsNormalized_of_some spec (normalizeInput spec input) output selected]
      change output.candidate.val % 2 ^ width < spec.modulus
      have fits : output.candidate.val < 2 ^ width :=
        lt_of_lt_of_le output.candidate.isLt spec.le_capacity
      rw [Nat.mod_eq_of_lt fits]
      exact output.candidate.isLt

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
