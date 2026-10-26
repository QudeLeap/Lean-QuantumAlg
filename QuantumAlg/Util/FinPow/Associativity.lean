/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow
import Mathlib.Tactic.Ring

/-! # Associativity of the same finite binary label -/

namespace QuantumAlg

/-- Reassociate the width equality without changing the finite label's natural value. -/
def finPowAssoc (before current after : Nat) :
    Fin (2 ^ (before + (current + after))) ≃ Fin (2 ^ ((before + current) + after)) :=
  finCongr (congrArg (fun width : Nat => 2 ^ width) (Nat.add_assoc before current after).symm)

/-- Grouping the first two binary blocks retains the same original big-endian label. -/
lemma prodEquiv_associative (before current after : Nat)
    (first : Fin (2 ^ before)) (middle : Fin (2 ^ current)) (last : Fin (2 ^ after)) :
    finPowAssoc before current after (prodEquiv (first, prodEquiv (middle, last))) =
      prodEquiv (prodEquiv (first, middle), last) := by
  apply Fin.ext
  change (last.val + 2 ^ after * middle.val) + 2 ^ (current + after) * first.val =
    last.val + 2 ^ after * (middle.val + 2 ^ current * first.val)
  rw [pow_add]
  ring

end QuantumAlg
