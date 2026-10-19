/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting
import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.CommonDivisorTail

/-!
# Order tails in finite cyclic groups

This module contains group-theoretic counting lemmas used by random-generator
arguments.  It is independent of any cryptographic algorithm: the only input
is that the finite group is cyclic.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- In a finite cyclic group, the number of elements whose order is at most
`limit` is bounded by the number of divisors of the group cardinality times
`limit`.

For every divisor `d` of the group cardinality, a cyclic group has exactly
`Nat.totient d` elements of order `d`; this is at most `d`, hence at most
`limit` in the filtered sum. -/
lemma card_orderOf_le_le_card_divisors_mul
    {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (limit : Nat) :
    (Finset.univ.filter fun g : G => orderOf g ≤ limit).card ≤
      (Fintype.card G).divisors.card * limit := by
  classical
  let orders := (Fintype.card G).divisors.filter (fun d => d ≤ limit)
  let fiber := fun d : Nat => Finset.univ.filter (fun g : G => orderOf g = d)
  have hdecompose :
      Finset.univ.filter (fun g : G => orderOf g ≤ limit) =
        orders.biUnion fiber := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · intro hg
      refine ⟨orderOf g, ?_, ?_⟩
      · simp only [orders, Finset.mem_filter]
        exact ⟨Nat.mem_divisors.mpr ⟨orderOf_dvd_card, Fintype.card_ne_zero⟩, hg⟩
      · simp [fiber]
    · rintro ⟨d, hd, hgd⟩
      have hdLimit : d ≤ limit := (Finset.mem_filter.mp hd).2
      have horder : orderOf g = d := by simpa [fiber] using hgd
      simpa [horder] using hdLimit
  rw [hdecompose]
  calc
    (orders.biUnion fiber).card ≤ ∑ d ∈ orders, (fiber d).card :=
      Finset.card_biUnion_le
    _ = ∑ d ∈ orders, Nat.totient d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact IsCyclic.card_orderOf_eq_totient
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    _ ≤ ∑ _d ∈ orders, limit := by
      apply Finset.sum_le_sum
      intro d hd
      exact (Nat.totient_le d).trans (Finset.mem_filter.mp hd).2
    _ = orders.card * limit := by simp
    _ ≤ (Fintype.card G).divisors.card * limit := by
      exact Nat.mul_le_mul_right limit (Finset.card_filter_le _ _)

/-- Multiplying the low-order count by the index cutoff eliminates the floor
in `card / cutoff`. -/
lemma cutoff_mul_card_orderOf_le_card_divisors_mul_card
    {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (cutoff : Nat) :
    cutoff *
        (Finset.univ.filter fun g : G =>
          orderOf g ≤ Fintype.card G / cutoff).card ≤
      (Fintype.card G).divisors.card * Fintype.card G := by
  have hcount := card_orderOf_le_le_card_divisors_mul
    (G := G) (Fintype.card G / cutoff)
  calc
    cutoff *
        (Finset.univ.filter fun g : G =>
          orderOf g ≤ Fintype.card G / cutoff).card ≤
        cutoff *
          ((Fintype.card G).divisors.card *
            (Fintype.card G / cutoff)) :=
      Nat.mul_le_mul_left cutoff hcount
    _ = (Fintype.card G).divisors.card *
        (cutoff * (Fintype.card G / cutoff)) := by ac_rfl
    _ ≤ (Fintype.card G).divisors.card * Fintype.card G := by
      apply Nat.mul_le_mul_left
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self (Fintype.card G) cutoff

/-- If the divisor count is below `2^divisorBits`, then choosing an index
cutoff `2^(divisorBits + tailBits)` makes the fraction of elements below that
order cutoff strictly less than `2^(-tailBits)`. -/
lemma pow_tail_mul_card_lowOrder_lt_card
    {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    {divisorBits tailBits : Nat}
    (hdivisors :
      (Fintype.card G).divisors.card < 2 ^ divisorBits) :
    2 ^ tailBits *
        (Finset.univ.filter fun g : G =>
          orderOf g ≤
            Fintype.card G / 2 ^ (divisorBits + tailBits)).card <
      Fintype.card G := by
  have hcardPos : 0 < Fintype.card G := Fintype.card_pos
  have hweighted :=
    cutoff_mul_card_orderOf_le_card_divisors_mul_card
      (G := G) (2 ^ (divisorBits + tailBits))
  have hstrict :
      (Fintype.card G).divisors.card * Fintype.card G <
        2 ^ divisorBits * Fintype.card G :=
    (Nat.mul_lt_mul_right hcardPos).2 hdivisors
  have hcombined := hweighted.trans_lt hstrict
  have hfactored :
      2 ^ divisorBits *
          (2 ^ tailBits *
            (Finset.univ.filter fun g : G =>
              orderOf g ≤
                Fintype.card G /
                  2 ^ (divisorBits + tailBits)).card) <
        2 ^ divisorBits * Fintype.card G := by
    simpa [pow_add, Nat.mul_assoc] using hcombined
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ divisorBits)).1
    hfactored

end NumberTheory
end QuantumAlg

end
