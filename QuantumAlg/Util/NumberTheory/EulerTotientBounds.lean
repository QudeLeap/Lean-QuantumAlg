/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Size
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Elementary lower bounds for Euler's totient

This module proves a deliberately elementary bit-length lower bound for
Euler's totient.  It is independent of quantum algorithms: the only inputs are
Euler's product formula and the fact that a finite increasing sequence of
distinct primes starts no earlier than `2, 3, ...`.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- For a finite set of primes, the product of the primes is at most one more
than the set cardinality times the product of their predecessors. -/
theorem primeProduct_le_card_succ_mul_predProduct
    (s : Finset Nat) (hprime : ∀ p ∈ s, Nat.Prime p) :
    (∏ p ∈ s, p) ≤
      (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
      simp
  | insert p s hlt ih =>
      have hp_not_mem : p ∉ s := by
        intro hp
        exact (Nat.lt_irrefl p) (hlt p hp)
      have hp_prime : Nat.Prime p :=
        hprime p (Finset.mem_insert_self p s)
      have hs_prime : ∀ q ∈ s, Nat.Prime q := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hsubset : s ⊆ Finset.Ico 2 p := by
        intro q hq
        exact Finset.mem_Ico.mpr ⟨(hs_prime q hq).two_le, hlt q hq⟩
      have hcard : s.card + 2 ≤ p := by
        have hcard' := Finset.card_le_card hsubset
        simp only [Nat.card_Ico] at hcard'
        have hp_two : 2 ≤ p := hp_prime.two_le
        omega
      have hcoefficient :
          p * (s.card + 1) ≤ (s.card + 2) * (p - 1) := by
        have hadded :
            p * (s.card + 1) + (s.card + 2) ≤
              (s.card + 2) * (p - 1) + (s.card + 2) := by
          calc
            p * (s.card + 1) + (s.card + 2) ≤
                p * (s.card + 1) + p :=
              Nat.add_le_add_left hcard _
            _ = (s.card + 2) * p := by ring
            _ = (s.card + 2) * (p - 1) + (s.card + 2) := by
              have hp_decomp : p - 1 + 1 = p :=
                Nat.sub_add_cancel hp_prime.one_le
              calc
                (s.card + 2) * p =
                    (s.card + 2) * ((p - 1) + 1) :=
                  congrArg (fun value => (s.card + 2) * value)
                    hp_decomp.symm
                _ = _ := by rw [Nat.mul_add, Nat.mul_one]
        exact Nat.le_of_add_le_add_right hadded
      simp only [Finset.prod_insert hp_not_mem,
        Finset.card_insert_of_notMem hp_not_mem]
      calc
        p * ∏ q ∈ s, q ≤
            p * ((s.card + 1) * ∏ q ∈ s, (q - 1)) :=
          Nat.mul_le_mul_left p (ih hs_prime)
        _ = (p * (s.card + 1)) * ∏ q ∈ s, (q - 1) := by ring
        _ ≤ ((s.card + 2) * (p - 1)) * ∏ q ∈ s, (q - 1) :=
          Nat.mul_le_mul_right _ hcoefficient
        _ = (s.card + 1 + 1) *
            ((p - 1) * ∏ q ∈ s, (q - 1)) := by ring

/-- A positive natural is at most its totient times one plus the number of its
distinct prime factors. -/
theorem self_le_totient_mul_card_primeFactors_succ
    (n : Nat) :
    n ≤ Nat.totient n * (n.primeFactors.card + 1) := by
  let factors := n.primeFactors
  let predecessorProduct := ∏ p ∈ factors, (p - 1)
  have hfactors :
      (∏ p ∈ factors, p) ≤
        (factors.card + 1) * predecessorProduct := by
    exact primeProduct_le_card_succ_mul_predProduct factors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hpredecessorProduct_pos : 0 < predecessorProduct := by
    exact Finset.prod_pos fun p hp =>
      Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  have hscaled :
      n * predecessorProduct ≤
        (Nat.totient n * (factors.card + 1)) * predecessorProduct := by
    calc
      n * predecessorProduct =
          Nat.totient n * ∏ p ∈ factors, p := by
        simpa [factors, predecessorProduct] using
          (Nat.totient_mul_prod_primeFactors n).symm
      _ ≤ Nat.totient n *
          ((factors.card + 1) * predecessorProduct) :=
        Nat.mul_le_mul_left _ hfactors
      _ = (Nat.totient n * (factors.card + 1)) *
          predecessorProduct := by ring
  exact Nat.le_of_mul_le_mul_right hscaled hpredecessorProduct_pos

/-- The number of distinct prime factors plus one is at most the binary
bit-length of a positive natural. -/
theorem card_primeFactors_succ_le_size (n : Nat) (hn : 0 < n) :
    n.primeFactors.card + 1 ≤ Nat.size n := by
  have hpow :
      2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    exact Finset.pow_card_le_prod n.primeFactors id 2 fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have hproduct :
      (∏ p ∈ n.primeFactors, p) ≤ n :=
    Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hlt : n.primeFactors.card < Nat.size n :=
    (Nat.lt_size).2 (hpow.trans hproduct)
  omega

/-- Elementary binary-size lower bound for Euler's totient:
`n ≤ φ(n) * bitlength(n)` for every positive natural `n`. -/
theorem self_le_totient_mul_size (n : Nat) (hn : 0 < n) :
    n ≤ Nat.totient n * Nat.size n :=
  (self_le_totient_mul_card_primeFactors_succ n).trans
    (Nat.mul_le_mul_left _ (card_primeFactors_succ_le_size n hn))

end NumberTheory
end QuantumAlg

end
