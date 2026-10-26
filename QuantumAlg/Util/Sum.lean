/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite sums with explicit cardinality bridges

The index size and its enumeration remain parameters during rewriting. This
avoids unfolding scalar expressions just to identify a computed finite size.
-/

namespace QuantumAlg

open scoped BigOperators

private lemma sumFinEightOfCard {n : Nat} [inst : Fintype (Fin n)]
    {M : Type*} [AddCommMonoid M] (f : Fin n → M) (h : n = 8) :
    ∑ i, f i =
      f (Fin.cast h.symm 0) + f (Fin.cast h.symm 1) +
      f (Fin.cast h.symm 2) + f (Fin.cast h.symm 3) +
      f (Fin.cast h.symm 4) + f (Fin.cast h.symm 5) +
      f (Fin.cast h.symm 6) + f (Fin.cast h.symm 7) := by
  subst n
  have hi : inst = Fin.fintype 8 := Subsingleton.elim _ _
  cases hi
  exact Fin.sum_univ_eight f

private lemma sumFinFourOfCard {n : Nat} [inst : Fintype (Fin n)]
    {M : Type*} [AddCommMonoid M] (f : Fin n → M) (h : n = 4) :
    ∑ i, f i =
      f (Fin.cast h.symm 0) + f (Fin.cast h.symm 1) +
      f (Fin.cast h.symm 2) + f (Fin.cast h.symm 3) := by
  subst n
  have hi : inst = Fin.fintype 4 := Subsingleton.elim _ _
  cases hi
  exact Fin.sum_univ_four f

end QuantumAlg
