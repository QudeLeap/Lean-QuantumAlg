/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.GroupTheory.Perm.Sign

/-!
# Linear-size transposition factorizations

The actual finite factor list is Mathlib's ordered construction. Its length
is bounded before any circuit is assembled, so a fixed wire permutation
can be implemented without repeating a unit rotation by its displacement.
-/

namespace QuantumAlg.Permutation

/-- Factoring supported nonfixed points emits at most one transposition per listed point. -/
lemma swapFactorsAux_length_le {α : Type*} [DecidableEq α] (indices : List α)
    (permutation : Equiv.Perm α)
    (supported : ∀ {point}, permutation point ≠ point → point ∈ indices) :
    (Equiv.Perm.swapFactorsAux indices permutation supported).val.length ≤ indices.length := by
  induction indices generalizing permutation with
  | nil => rfl
  | cons point rest ih =>
      rw [Equiv.Perm.swapFactorsAux]
      dsimp only
      split
      next fixed =>
        have smaller : ∀ {other}, permutation other ≠ other → other ∈ rest := by
          intro other moved
          rcases List.mem_cons.mp (supported moved) with same | member
          · subst other
            exact False.elim (moved fixed.symm)
          · exact member
        exact (ih permutation smaller).trans (Nat.le_succ _)
      · have smaller : ∀ {other},
            (Equiv.swap point (permutation point) * permutation) other ≠ other →
              other ∈ rest := by
          intro other moved
          have separated := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self moved
          exact List.mem_of_ne_of_mem separated.2 (supported separated.1)
        exact Nat.succ_le_succ (ih _ smaller)

/-- Every actual ordered finite factorization has linear size in its unchanged carrier. -/
lemma swapFactors_length_le {α : Type*} [Fintype α] [LinearOrder α]
    (permutation : Equiv.Perm α) :
    (Equiv.Perm.swapFactors permutation).val.length ≤ Fintype.card α := by
  unfold Equiv.Perm.swapFactors
  apply (swapFactorsAux_length_le _ permutation (by intro point _; simp)).trans
  simp

end QuantumAlg.Permutation
