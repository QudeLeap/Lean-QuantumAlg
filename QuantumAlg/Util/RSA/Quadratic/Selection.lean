/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Stored decisions for the original quadratic factor result

These value-level consequences retain the original two-candidate order and
all modulus and logarithm inputs. A recovered nontrivial divisor is below
the modulus, so a word able to hold the modulus also holds every selected
factor without truncation. No execution or resource object is introduced.
-/

namespace QuantumAlg.RSA

/-- The original result is selected by the same two Boolean divisor tests used by native checks. -/
lemma recoverFactorFromShortLog_eq_decisions (modulus logarithm : Nat) :
    let source := quadraticFactorCandidates modulus logarithm
    let firstValid := decide (1 < source.1 ∧ source.1 < modulus ∧ modulus % source.1 = 0)
    let secondValid := decide (1 < source.2 ∧ source.2 < modulus ∧ modulus % source.2 = 0)
    recoverFactorFromShortLog modulus logarithm =
      if firstValid then some source.1 else if secondValid then some source.2 else none := by
  simp only [decide_eq_true_eq]
  rw [quadraticFactorCandidates_eq, recoverFactorFromShortLog_eq]

/-- The original source factor is unchanged by conversion to any word containing the modulus. -/
lemma recoverFactorFromShortLog_map_mod (modulus logarithm width : Nat)
    (capacity : modulus ≤ 2 ^ width) :
    (recoverFactorFromShortLog modulus logarithm).map (fun factor => factor % 2 ^ width) =
      recoverFactorFromShortLog modulus logarithm := by
  cases result : recoverFactorFromShortLog modulus logarithm with
  | none => rfl
  | some factor =>
      have small := (recoverFactorFromShortLog_some_sound result).2.2
      exact congrArg some (Nat.mod_eq_of_lt (small.trans_le capacity))

end QuantumAlg.RSA
