/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Tactic

/-!
# Shor factoring reduction utilities

This module contains the quantum-free gcd bridge used after order finding. It
separates Shor's classical side-condition check from the quantum order-finding
module so the factoring reduction can be reused by resource-accounting layers.

The bridge is Shor's classical reduction from order finding to factoring:
after recovering an even order, nontrivial gcds of `x^(r/2) ± 1` yield factors
unless the usual side conditions fail [Sho95, source.tex:1124-1148] [dW19,
qcnotes.tex:1998-2055].
-/

@[expose] public section

namespace QuantumAlg

namespace ShorFactoring

open Finset

/-- Factoring-reduction gcd step. If `N ∣ a * b` while `N` divides neither `a`
nor `b`, then `gcd(a, N)` is a nontrivial factor of `N`. -/
theorem main_factor_reduction {N a b : ℕ} (hN : 1 < N)
    (hdvd : N ∣ a * b) (ha : ¬ N ∣ a) (hb : ¬ N ∣ b) :
    1 < Nat.gcd a N ∧ Nat.gcd a N < N := by
  have hN0 : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hN)
  have hpos : 0 < Nat.gcd a N := Nat.gcd_pos_of_pos_right a hN0
  have hle : Nat.gcd a N ≤ N := Nat.le_of_dvd hN0 (Nat.gcd_dvd_right a N)
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge 1 (Nat.gcd a N) with h | h
    · exact h
    · exfalso
      have hg1 : Nat.gcd a N = 1 := by omega
      have hca : Nat.Coprime a N := hg1
      exact hb (hca.symm.dvd_of_dvd_mul_left hdvd)
  · rcases Nat.lt_or_ge (Nat.gcd a N) N with h | h
    · exact h
    · exfalso
      have hgN : Nat.gcd a N = N := le_antisymm hle h
      exact ha (hgN ▸ Nat.gcd_dvd_left a N)

/-- Modular side conditions for Shor's gcd bridge. Here `y` is the recovered
half-order residue, normally `x^(r/2)`, and the conditions say
`(y-1)(y+1) ≡ 0 (mod N)` while neither factor is individually `0 (mod N)`. -/
structure GcdBridgeInput (N y : ℕ) : Prop where
  modulus_gt_one : 1 < N
  product_zero_mod : (y - 1) * (y + 1) ≡ 0 [MOD N]
  left_nonzero_mod : ¬ (y - 1) ≡ 0 [MOD N]
  right_nonzero_mod : ¬ (y + 1) ≡ 0 [MOD N]

/-- If a doubled exponent returns `x` to one modulo `N`, then the half-exponent
residue squares to one modulo `N`. -/
theorem half_order_square_modEq_one_of_double {N x k : ℕ}
    (hpow : x ^ (2 * k) ≡ 1 [MOD N]) :
    (x ^ k) * (x ^ k) ≡ 1 [MOD N] := by
  have hpow' : x ^ (k + k) ≡ 1 [MOD N] := by
    simpa [two_mul] using hpow
  simpa [pow_add] using hpow'

/-- Evenness lets the half-order residue be read as `x^(r/2)`. -/
theorem half_order_square_modEq_one {N x r : ℕ}
    (heven : Even r) (hpow : x ^ r ≡ 1 [MOD N]) :
    (x ^ (r / 2)) * (x ^ (r / 2)) ≡ 1 [MOD N] := by
  rcases heven with ⟨k, rfl⟩
  have hhalf : (k + k) / 2 = k := by
    have hdouble : k + k = 2 * k := by omega
    rw [hdouble, Nat.mul_div_right k (by norm_num : 0 < 2)]
  have hdouble : x ^ (2 * k) ≡ 1 [MOD N] := by
    simpa [two_mul] using hpow
  simpa [hhalf] using
    half_order_square_modEq_one_of_double (N := N) (x := x) (k := k) hdouble

/-- Order-level Shor side conditions before packaging the half-order residue for
the gcd bridge. -/
structure HalfOrderGcdInput (N x r : ℕ) : Prop where
  modulus_gt_one : 1 < N
  base_pos : 0 < x
  even_order : Even r
  return_to_one : x ^ r ≡ 1 [MOD N]
  left_nonzero_mod : ¬ (x ^ (r / 2) - 1) ≡ 0 [MOD N]
  right_nonzero_mod : ¬ (x ^ (r / 2) + 1) ≡ 0 [MOD N]

namespace HalfOrderGcdInput

/-- A Shor half-order gcd route has a positive recovered order. If `r = 0`,
the left nonzero side condition would require `0` to be nonzero modulo `N`
[Sho95, source.tex:1124-1148]. -/
theorem order_pos {N x r : ℕ} (h : HalfOrderGcdInput N x r) : 0 < r := by
  by_contra hnot
  have hr : r = 0 := Nat.eq_zero_of_not_pos hnot
  have hzero : (x ^ (r / 2) - 1) = 0 := by
    simp [hr]
  exact h.left_nonzero_mod (by rw [hzero])

end HalfOrderGcdInput

/-- If the half-order residue squares to one modulo `N`, then the product
`(y-1)(y+1)` vanishes modulo `N`. The positivity hypothesis avoids the
truncation edge of natural-number subtraction. -/
theorem product_zero_mod_of_square_modEq_one {N y : ℕ}
    (hypos : 0 < y) (hsquare : y * y ≡ 1 [MOD N]) :
    (y - 1) * (y + 1) ≡ 0 [MOD N] := by
  rw [Nat.modEq_iff_dvd]
  rw [Nat.modEq_iff_dvd] at hsquare
  convert hsquare using 1
  change (0 : ℤ) - ↑((y - 1) * (y + 1)) = (1 : ℤ) - ↑(y * y)
  have hy1 : 1 ≤ y := Nat.succ_le_of_lt hypos
  rw [Nat.cast_mul, Nat.cast_sub hy1, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  ring

/-- Package the usual Shor square-one side conditions as a `GcdBridgeInput`. -/
theorem gcdBridgeInput_of_square_modEq_one {N y : ℕ}
    (hN : 1 < N) (hypos : 0 < y) (hsquare : y * y ≡ 1 [MOD N])
    (hleft : ¬ (y - 1) ≡ 0 [MOD N])
    (hright : ¬ (y + 1) ≡ 0 [MOD N]) :
    GcdBridgeInput N y where
  modulus_gt_one := hN
  product_zero_mod := product_zero_mod_of_square_modEq_one hypos hsquare
  left_nonzero_mod := hleft
  right_nonzero_mod := hright

/-- Package even-order Shor side conditions as a `GcdBridgeInput` for the
half-order residue. -/
theorem gcdBridgeInput_of_half_order {N x r : ℕ}
    (h : HalfOrderGcdInput N x r) :
    GcdBridgeInput N (x ^ (r / 2)) where
  modulus_gt_one := h.modulus_gt_one
  product_zero_mod :=
    product_zero_mod_of_square_modEq_one
      (pow_pos h.base_pos (r / 2))
      (half_order_square_modEq_one h.even_order h.return_to_one)
  left_nonzero_mod := h.left_nonzero_mod
  right_nonzero_mod := h.right_nonzero_mod

/-- Bridge from Shor's modular side conditions to the reusable gcd factoring
core. Both gcd expressions are nontrivial factors under the same hypotheses. -/
theorem gcd_bridge {N y : ℕ} (h : GcdBridgeInput N y) :
    (1 < Nat.gcd (y - 1) N ∧ Nat.gcd (y - 1) N < N) ∧
      (1 < Nat.gcd (y + 1) N ∧ Nat.gcd (y + 1) N < N) := by
  have hprod : N ∣ (y - 1) * (y + 1) :=
    Nat.modEq_zero_iff_dvd.mp h.product_zero_mod
  have hleft : ¬ N ∣ y - 1 := fun hdvd =>
    h.left_nonzero_mod (Nat.modEq_zero_iff_dvd.mpr hdvd)
  have hright : ¬ N ∣ y + 1 := fun hdvd =>
    h.right_nonzero_mod (Nat.modEq_zero_iff_dvd.mpr hdvd)
  constructor
  · exact main_factor_reduction h.modulus_gt_one hprod hleft hright
  · exact main_factor_reduction h.modulus_gt_one (by simpa [mul_comm] using hprod)
      hright hleft

/-- Direct bridge from Shor's square-one side conditions to nontrivial gcd
factors. -/
private theorem gcd_bridge_of_square_modEq_one {N y : ℕ}
    (hN : 1 < N) (hypos : 0 < y) (hsquare : y * y ≡ 1 [MOD N])
    (hleft : ¬ (y - 1) ≡ 0 [MOD N])
    (hright : ¬ (y + 1) ≡ 0 [MOD N]) :
    (1 < Nat.gcd (y - 1) N ∧ Nat.gcd (y - 1) N < N) ∧
      (1 < Nat.gcd (y + 1) N ∧ Nat.gcd (y + 1) N < N) :=
  gcd_bridge (gcdBridgeInput_of_square_modEq_one hN hypos hsquare hleft hright)

/-- Direct bridge from even-order Shor side conditions to nontrivial gcd
factors for the half-order residue. -/
theorem gcd_bridge_of_half_order {N x r : ℕ}
    (h : HalfOrderGcdInput N x r) :
    (1 < Nat.gcd (x ^ (r / 2) - 1) N ∧ Nat.gcd (x ^ (r / 2) - 1) N < N) ∧
      (1 < Nat.gcd (x ^ (r / 2) + 1) N ∧ Nat.gcd (x ^ (r / 2) + 1) N < N) :=
  gcd_bridge (gcdBridgeInput_of_half_order h)

/-! ## Semiprime factor-return certificates -/

/-- Declared semiprime model for the RSA correctness layer. The final field is
the semiprime divisor eliminator consumed by the factor-return theorem: every
nontrivial divisor of `N` is one of the two declared prime factors. Keeping it
as part of the model lets RSA correctness assembly depend on a single explicit
semiprime certificate rather than re-proving the divisor classification at each
route endpoint. -/
structure SemiprimeFactorModel (N : ℕ) where
  /-- Left prime factor in the semiprime factor model. -/
  leftFactor : ℕ
  /-- Right prime factor in the semiprime factor model. -/
  rightFactor : ℕ
  left_prime : Nat.Prime leftFactor
  right_prime : Nat.Prime rightFactor
  distinct : leftFactor ≠ rightFactor
  product_eq : N = leftFactor * rightFactor
  nontrivial_factor_eq_declared :
    ∀ {d : ℕ}, d ∣ N → 1 < d → d < N →
      d = leftFactor ∨ d = rightFactor

namespace SemiprimeFactorModel

/-- Build the semiprime factor model directly from two public distinct primes.
The nontrivial-divisor eliminator is derived here, so later Shor endpoints do
not have to take it as an extra public assumption. -/
def ofDistinctPrimes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) : SemiprimeFactorModel (p * q) where
  leftFactor := p
  rightFactor := q
  left_prime := hp
  right_prime := hq
  distinct := hpq
  product_eq := rfl
  nontrivial_factor_eq_declared := by
    intro d hdvd hgt hlt
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hgprod : Nat.gcd d p * Nat.gcd d q = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (x := d) hcop).mpr hdvd
    have hgp : Nat.gcd d p = 1 ∨ Nat.gcd d p = p :=
      hp.eq_one_or_self_of_dvd (Nat.gcd d p) (Nat.gcd_dvd_right d p)
    have hgq : Nat.gcd d q = 1 ∨ Nat.gcd d q = q :=
      hq.eq_one_or_self_of_dvd (Nat.gcd d q) (Nat.gcd_dvd_right d q)
    rcases hgp with hgp | hgp <;> rcases hgq with hgq | hgq
    · have hd1 : d = 1 := by
        rw [← hgprod, hgp, hgq]
      omega
    · right
      rw [← hgprod, hgp, hgq]
      exact Nat.one_mul q
    · left
      rw [← hgprod, hgp, hgq]
      exact Nat.mul_one p
    · have hdpq : d = p * q := by
        rw [← hgprod, hgp, hgq]
      have : p * q < p * q := by
        rw [hdpq] at hlt
        exact hlt
      exact False.elim ((lt_irrefl (p * q)) this)

end SemiprimeFactorModel

/-! ## Random-base sample space for semiprime moduli -/

namespace SemiprimeFactorModel

/-- The left prime factor divides the public semiprime modulus. -/
theorem leftFactor_dvd_modulus {N : ℕ} (model : SemiprimeFactorModel N) :
    model.leftFactor ∣ N := by
  exact ⟨model.rightFactor, model.product_eq⟩

/-- The right prime factor divides the public semiprime modulus. -/
theorem rightFactor_dvd_modulus {N : ℕ} (model : SemiprimeFactorModel N) :
    model.rightFactor ∣ N := by
  exact ⟨model.leftFactor, by simpa [Nat.mul_comm] using model.product_eq⟩

/-- The declared prime factors are coprime. -/
theorem leftRight_coprime {N : ℕ} (model : SemiprimeFactorModel N) :
    Nat.Coprime model.leftFactor model.rightFactor :=
  (Nat.coprime_primes model.left_prime model.right_prime).mpr model.distinct

/-- A semiprime model has nontrivial public modulus. -/
theorem modulus_gt_one {N : ℕ} (model : SemiprimeFactorModel N) :
    1 < N := by
  have hmul : 2 * 2 ≤ model.leftFactor * model.rightFactor :=
    Nat.mul_le_mul model.left_prime.two_le model.right_prime.two_le
  rw [model.product_eq]
  exact Nat.lt_of_lt_of_le (by norm_num : 1 < 2 * 2) hmul

/-- The left declared prime factor is a proper divisor of the public semiprime
modulus. -/
theorem leftFactor_lt_modulus {N : ℕ} (model : SemiprimeFactorModel N) :
    model.leftFactor < N := by
  calc
    model.leftFactor < model.leftFactor * model.rightFactor := by
      have h :=
        Nat.mul_lt_mul_of_pos_left model.right_prime.one_lt
          model.left_prime.pos
      simpa using h
    _ = N := model.product_eq.symm

/-- The right declared prime factor is a proper divisor of the public semiprime
modulus. -/
theorem rightFactor_lt_modulus {N : ℕ} (model : SemiprimeFactorModel N) :
    model.rightFactor < N := by
  calc
    model.rightFactor < model.rightFactor * model.leftFactor := by
      have h :=
        Nat.mul_lt_mul_of_pos_left model.left_prime.one_lt
          model.right_prime.pos
      simpa using h
    _ = model.leftFactor * model.rightFactor := Nat.mul_comm _ _
    _ = N := model.product_eq.symm

/-- A declared prime factor that is not two is an odd-prime factor in the
numeric form required by Shor's good-base analysis. -/
theorem leftFactor_gt_two_of_ne_two {N : ℕ}
    (model : SemiprimeFactorModel N)
    (hleft_ne_two : model.leftFactor ≠ 2) :
    2 < model.leftFactor := by
  have htwo := model.left_prime.two_le
  omega

/-- A declared prime factor that is not two is an odd-prime factor in the
numeric form required by Shor's good-base analysis. -/
theorem rightFactor_gt_two_of_ne_two {N : ℕ}
    (model : SemiprimeFactorModel N)
    (hright_ne_two : model.rightFactor ≠ 2) :
    2 < model.rightFactor := by
  have htwo := model.right_prime.two_le
  omega

end SemiprimeFactorModel

/-! ## Two-adic order vocabulary for Shor good-base analysis -/

/-- The exponent of the largest power of two dividing an order. Shor's
good-base analysis compares these exponents across the CRT components of the
random base [Sho95, source.tex:1147-1169]. -/
def twoAdicOrderValuation (r : ℕ) : ℕ :=
  r.factorization 2

/-- The two-adic order valuation of an LCM is the maximum of the two component
valuations. -/
theorem twoAdicOrderValuation_lcm {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    twoAdicOrderValuation (Nat.lcm a b) =
      max (twoAdicOrderValuation a) (twoAdicOrderValuation b) := by
  simp [twoAdicOrderValuation, Nat.factorization_lcm ha hb]

/-- A nonzero natural number has positive two-adic order valuation exactly when
it is even. -/
theorem twoAdicOrderValuation_pos_iff_even {r : ℕ}
    (hr : r ≠ 0) :
    0 < twoAdicOrderValuation r ↔ Even r := by
  rw [even_iff_two_dvd, twoAdicOrderValuation, ← Nat.succ_le_iff,
    Nat.prime_two.dvd_iff_one_le_factorization hr]

/-- If the right component order has strictly larger two-adic valuation, the
LCM of the two component orders is even. -/
theorem even_lcm_of_left_twoAdic_lt_right {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : twoAdicOrderValuation a < twoAdicOrderValuation b) :
    Even (Nat.lcm a b) := by
  rw [← twoAdicOrderValuation_pos_iff_even (Nat.lcm_ne_zero ha hb)]
  rw [twoAdicOrderValuation_lcm ha hb]
  exact lt_of_le_of_lt (Nat.zero_le _)
    (lt_of_lt_of_le hlt (le_max_right _ _))

/-- If the component orders have unequal two-adic valuations, their LCM is
even. This is the order-level halving precondition used by Shor's good-base
criterion [Sho95, source.tex:1150-1155]. -/
theorem even_lcm_of_twoAdic_ne {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : twoAdicOrderValuation a ≠ twoAdicOrderValuation b) :
    Even (Nat.lcm a b) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact even_lcm_of_left_twoAdic_lt_right ha hb hlt
  · rw [Nat.lcm_comm]
    exact even_lcm_of_left_twoAdic_lt_right hb ha hgt

/-- Halving equality for the LCM when the component orders have unequal
two-adic valuations. -/
private theorem two_mul_lcm_div_two_of_twoAdic_ne {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : twoAdicOrderValuation a ≠ twoAdicOrderValuation b) :
    2 * (Nat.lcm a b / 2) = Nat.lcm a b := by
  simpa [mul_comm] using
    Nat.div_mul_cancel (even_lcm_of_twoAdic_ne ha hb hne).two_dvd

/-- When the right component order has larger two-adic valuation, half of the
LCM is still positive. -/
theorem lcm_div_two_pos_of_left_twoAdic_lt_right {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : twoAdicOrderValuation a < twoAdicOrderValuation b) :
    0 < Nat.lcm a b / 2 := by
  have hb_even : Even b :=
    (twoAdicOrderValuation_pos_iff_even hb).mp
      (lt_of_le_of_lt (Nat.zero_le _) hlt)
  rcases hb_even with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk0
    have hb_zero : b = 0 := by
      rw [hk, hk_zero]
    exact hb hb_zero
  have hb_two : 2 ≤ b := by
    rw [hk]
    omega
  have hb_le_lcm : b ≤ Nat.lcm a b :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero ha hb))
      (Nat.dvd_lcm_right a b)
  exact Nat.div_pos (le_trans hb_two hb_le_lcm) (by norm_num)

/-- If the right component order has larger two-adic valuation, the left
component order divides half of the LCM. -/
theorem left_dvd_lcm_div_two_of_left_twoAdic_lt_right {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : twoAdicOrderValuation a < twoAdicOrderValuation b) :
    a ∣ Nat.lcm a b / 2 := by
  have hhalf_ne : Nat.lcm a b / 2 ≠ 0 :=
    (lcm_div_two_pos_of_left_twoAdic_lt_right ha hb hlt).ne'
  rw [← Nat.factorization_le_iff_dvd ha hhalf_ne]
  rw [Finsupp.le_def]
  intro p
  have htwo_dvd_lcm : 2 ∣ Nat.lcm a b :=
    (even_lcm_of_left_twoAdic_lt_right ha hb hlt).two_dvd
  have hfactor_half :
      (Nat.lcm a b / 2).factorization =
        (Nat.lcm a b).factorization - (2 : ℕ).factorization :=
    Nat.factorization_div htwo_dvd_lcm
  by_cases hp2 : p = 2
  · subst p
    have h2 : (2 : ℕ).factorization 2 = 1 := by
      simpa using Nat.prime_two.factorization_self
    have hfactor_lcm :
        twoAdicOrderValuation (Nat.lcm a b) = twoAdicOrderValuation b := by
      rw [twoAdicOrderValuation_lcm ha hb]
      exact max_eq_right (le_of_lt hlt)
    have hfactor_lcm_raw :
        (Nat.lcm a b).factorization 2 = b.factorization 2 := by
      simpa [twoAdicOrderValuation] using hfactor_lcm
    have hhalf_two :
        (Nat.lcm a b / 2).factorization 2 =
          twoAdicOrderValuation b - 1 := by
      have hraw := congrArg (fun f => f 2) hfactor_half
      simpa [twoAdicOrderValuation, hfactor_lcm_raw, h2] using hraw
    have : twoAdicOrderValuation a ≤ twoAdicOrderValuation b - 1 := by
      omega
    simpa [twoAdicOrderValuation, hhalf_two]
  · have hfactor_lcm :
        (Nat.lcm a b).factorization p =
          max (a.factorization p) (b.factorization p) := by
      have h := Nat.factorization_lcm ha hb
      simpa using congrArg (fun f => f p) h
    have hp_factor : (2 : ℕ).factorization p = 0 := by
      rw [Nat.prime_two.factorization]
      simp [hp2]
    have hhalf_p :
        (Nat.lcm a b / 2).factorization p =
          (Nat.lcm a b).factorization p := by
      simpa [hp_factor] using congrArg (fun f => f p) hfactor_half
    rw [hhalf_p, hfactor_lcm]
    exact le_max_left _ _

/-- If the right component order has larger two-adic valuation, it does not
divide half of the LCM. -/
theorem right_not_dvd_lcm_div_two_of_left_twoAdic_lt_right {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : twoAdicOrderValuation a < twoAdicOrderValuation b) :
    ¬ b ∣ Nat.lcm a b / 2 := by
  intro hdvd
  have hhalf_ne : Nat.lcm a b / 2 ≠ 0 :=
    (lcm_div_two_pos_of_left_twoAdic_lt_right ha hb hlt).ne'
  have hfact_le :
      twoAdicOrderValuation b ≤ twoAdicOrderValuation (Nat.lcm a b / 2) := by
    simpa [twoAdicOrderValuation] using
      ((Nat.factorization_le_iff_dvd hb hhalf_ne).mpr hdvd 2)
  have htwo_dvd_lcm : 2 ∣ Nat.lcm a b :=
    (even_lcm_of_left_twoAdic_lt_right ha hb hlt).two_dvd
  have hfactor_half :
      twoAdicOrderValuation (Nat.lcm a b / 2) =
        twoAdicOrderValuation (Nat.lcm a b) - 1 := by
    have h := Nat.factorization_div htwo_dvd_lcm
    have h2 : (2 : ℕ).factorization 2 = 1 := by
      simpa using Nat.prime_two.factorization_self
    simpa [twoAdicOrderValuation, h2] using congrArg (fun f => f 2) h
  have hfactor_lcm :
      twoAdicOrderValuation (Nat.lcm a b) = twoAdicOrderValuation b := by
    rw [twoAdicOrderValuation_lcm ha hb]
    exact max_eq_right (le_of_lt hlt)
  omega

/-! ## Cyclic counting support for Shor good bases -/

/-- If `a ∣ n` and the two-adic valuation of `a` is strictly smaller than that
of `n`, then `a` divides `n / 2`. This is the arithmetic core behind the
half-kernel partition in Shor's cyclic good-base count [Sho95,
source.tex:1155-1169]. -/
theorem dvd_div_two_of_twoAdic_lt {a n : ℕ}
    (ha : a ≠ 0) (hn : n ≠ 0) (hdvd : a ∣ n)
    (hlt : twoAdicOrderValuation a < twoAdicOrderValuation n) :
    a ∣ n / 2 := by
  have hn_even : Even n :=
    (twoAdicOrderValuation_pos_iff_even hn).mp
      (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have htwo_dvd_n : 2 ∣ n := hn_even.two_dvd
  have hhalf_ne : n / 2 ≠ 0 := by
    rcases hn_even with ⟨m, hm⟩
    have hm' : n = 2 * m := by
      simpa [two_mul] using hm
    have hmpos : 0 < m := by
      by_contra hm0
      have hmz : m = 0 := Nat.eq_zero_of_not_pos hm0
      rw [hm', hmz] at hn
      exact hn rfl
    rw [hm', Nat.mul_div_right m (by norm_num : 0 < 2)]
    exact hmpos.ne'
  rw [← Nat.factorization_le_iff_dvd ha hhalf_ne]
  rw [Finsupp.le_def]
  intro p
  have hfactor_half :
      (n / 2).factorization =
        n.factorization - (2 : ℕ).factorization :=
    Nat.factorization_div htwo_dvd_n
  have hfactor_dvd :
      a.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd ha hn).mpr hdvd
  by_cases hp2 : p = 2
  · subst p
    have h2 : (2 : ℕ).factorization 2 = 1 := by
      simpa using Nat.prime_two.factorization_self
    have hhalf_two :
        (n / 2).factorization 2 =
          twoAdicOrderValuation n - 1 := by
      have hraw := congrArg (fun f => f 2) hfactor_half
      simpa [twoAdicOrderValuation, h2] using hraw
    have : twoAdicOrderValuation a ≤ twoAdicOrderValuation n - 1 := by
      omega
    simpa [twoAdicOrderValuation, hhalf_two]
  · have hp_factor : (2 : ℕ).factorization p = 0 := by
      rw [Nat.prime_two.factorization]
      simp [hp2]
    have hhalf_p :
        (n / 2).factorization p = n.factorization p := by
      simpa [hp_factor] using congrArg (fun f => f p) hfactor_half
    rw [hhalf_p]
    exact hfactor_dvd p

/-- Two-adic order valuation is monotone along divisibility of nonzero natural
numbers. -/
theorem twoAdicOrderValuation_le_of_dvd {a n : ℕ}
    (ha : a ≠ 0) (hn : n ≠ 0) (hdvd : a ∣ n) :
    twoAdicOrderValuation a ≤ twoAdicOrderValuation n := by
  simpa [twoAdicOrderValuation] using
    ((Nat.factorization_le_iff_dvd ha hn).mpr hdvd 2)

/-- In a finite cyclic group of even order, the half-kernel
`{x | x^(|G|/2)=1}` has exactly half the group cardinality. This is the
counting partition used in Shor's good-base probability lower bound [Sho95,
source.tex:1155-1169]. -/
theorem card_pow_card_div_two_eq_one_eq_half
    {G : Type*} [Group G] [DecidableEq G] [Fintype G] [IsCyclic G]
    (hEven : Even (Fintype.card G)) :
    #{x : G | x ^ (Fintype.card G / 2) = 1} = Fintype.card G / 2 := by
  classical
  have hcard_pos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have htwo_dvd : 2 ∣ Fintype.card G := hEven.two_dvd
  have hhalf_pos : 0 < Fintype.card G / 2 := by
    rcases hEven with ⟨m, hm⟩
    have hm' : Fintype.card G = 2 * m := by
      simpa [two_mul] using hm
    have hmpos : 0 < m := by
      by_contra hm0
      have hmz : m = 0 := Nat.eq_zero_of_not_pos hm0
      rw [hm'] at hcard_pos
      simp [hmz] at hcard_pos
    rw [hm', Nat.mul_div_right m (by norm_num : 0 < 2)]
    exact hmpos
  apply le_antisymm
  · exact IsCyclic.card_pow_eq_one_le hhalf_pos
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    let H : Subgroup G := Subgroup.zpowers (g ^ 2)
    have hH_sub :
        (H : Set G).toFinset ⊆
          ({x : G | x ^ (Fintype.card G / 2) = 1} : Finset G) := by
      intro x hx
      rw [Set.mem_toFinset] at hx
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hx_dvd : orderOf x ∣ orderOf (g ^ 2) :=
        orderOf_dvd_of_mem_zpowers hx
      have horder_g : orderOf g = Fintype.card G := by
        simpa [Nat.card_eq_fintype_card] using
          orderOf_eq_card_of_forall_mem_zpowers hg
      have hg2 : orderOf (g ^ 2) = Fintype.card G / 2 := by
        rw [orderOf_pow, horder_g]
        have hgcd : Nat.gcd (Fintype.card G) 2 = 2 := by
          exact Nat.gcd_eq_right htwo_dvd
        simp [hgcd]
      exact (orderOf_dvd_iff_pow_eq_one).mp (by simpa [hg2] using hx_dvd)
    have hH_card : #(H : Set G).toFinset = Fintype.card G / 2 := by
      rw [Set.toFinset_card]
      change Fintype.card H = Fintype.card G / 2
      rw [Fintype.card_zpowers]
      have horder_g : orderOf g = Fintype.card G := by
        simpa [Nat.card_eq_fintype_card] using
          orderOf_eq_card_of_forall_mem_zpowers hg
      rw [orderOf_pow, horder_g]
      have hgcd : Nat.gcd (Fintype.card G) 2 = 2 := by
        exact Nat.gcd_eq_right htwo_dvd
      simp [hgcd]
    have hle := Finset.card_le_card hH_sub
    simpa [hH_card] using hle

/-- Every fixed two-adic order-valuation fiber in a finite cyclic group of even
order has cardinality at most half the group. Shor uses this fiber bound to show
that the equal-valuation bad event has probability at most one half [Sho95,
source.tex:1155-1169]. -/
theorem card_twoAdicOrderValuation_fiber_le_half
    {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (hEven : Even (Fintype.card G)) (k : ℕ) :
    2 * #{x : G | twoAdicOrderValuation (orderOf x) = k} ≤ Fintype.card G := by
  classical
  let n := Fintype.card G
  let S : Finset G := {x : G | x ^ (n / 2) = 1}
  have hn_pos : 0 < n := by
    dsimp [n]
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hS_card : #S = n / 2 := by
    dsimp [S, n]
    exact card_pow_card_div_two_eq_one_eq_half hEven
  have hhalf_ne_n : n / 2 ≠ 0 := by
    rcases hEven with ⟨m, hm⟩
    have hm' : n = 2 * m := by
      dsimp [n]
      simpa [two_mul] using hm
    have hmpos : 0 < m := by
      by_contra hm0
      have hmz : m = 0 := Nat.eq_zero_of_not_pos hm0
      rw [hm', hmz] at hn_ne
      exact hn_ne rfl
    rw [hm', Nat.mul_div_right m (by norm_num : 0 < 2)]
    exact hmpos.ne'
  have hsub_or_compl :
      ({x : G | twoAdicOrderValuation (orderOf x) = k} : Finset G) ⊆ S ∨
        ({x : G | twoAdicOrderValuation (orderOf x) = k} : Finset G) ⊆ Sᶜ := by
    by_cases hk : k < twoAdicOrderValuation n
    · left
      intro x hx
      rw [mem_filter] at hx ⊢
      refine ⟨mem_univ _, ?_⟩
      have horder_ne : orderOf x ≠ 0 := (orderOf_pos x).ne'
      have horder_dvd : orderOf x ∣ n := by
        dsimp [n]
        exact orderOf_dvd_card
      have hlt : twoAdicOrderValuation (orderOf x) < twoAdicOrderValuation n := by
        simpa [hx.2] using hk
      exact (orderOf_dvd_iff_pow_eq_one).mp
        (dvd_div_two_of_twoAdic_lt horder_ne hn_ne horder_dvd hlt)
    · right
      intro x hx
      rw [mem_filter] at hx
      rw [mem_compl, mem_filter]
      intro hxS
      have hpow : x ^ (n / 2) = 1 := hxS.2
      have horder_ne : orderOf x ≠ 0 := (orderOf_pos x).ne'
      have horder_dvd_half : orderOf x ∣ n / 2 :=
        (orderOf_dvd_iff_pow_eq_one).mpr hpow
      have hle_half :
          twoAdicOrderValuation (orderOf x) ≤ twoAdicOrderValuation (n / 2) :=
        twoAdicOrderValuation_le_of_dvd horder_ne hhalf_ne_n horder_dvd_half
      have hn_even : Even n := hEven
      have htwo_dvd_n : 2 ∣ n := hn_even.two_dvd
      have hfactor_half :
          (n / 2).factorization =
            n.factorization - (2 : ℕ).factorization :=
        Nat.factorization_div htwo_dvd_n
      have h2 : (2 : ℕ).factorization 2 = 1 := by
        simpa using Nat.prime_two.factorization_self
      have hval_half :
          twoAdicOrderValuation (n / 2) =
            twoAdicOrderValuation n - 1 := by
        have hraw := congrArg (fun f => f 2) hfactor_half
        simpa [twoAdicOrderValuation, h2] using hraw
      have hk_ge : twoAdicOrderValuation n ≤ k := by omega
      have hval_ge : twoAdicOrderValuation n ≤ twoAdicOrderValuation (orderOf x) := by
        simpa [hx.2] using hk_ge
      have hn_val_pos : 0 < twoAdicOrderValuation n :=
        (twoAdicOrderValuation_pos_iff_even hn_ne).mpr hEven
      have hval_half_lt :
          twoAdicOrderValuation (n / 2) < twoAdicOrderValuation n := by
        rw [hval_half]
        omega
      exact not_lt_of_ge hval_ge (lt_of_le_of_lt hle_half hval_half_lt)
  rcases hsub_or_compl with hsub | hsub
  · have hle : #{x : G | twoAdicOrderValuation (orderOf x) = k} ≤ n / 2 := by
      exact (Finset.card_le_card hsub).trans_eq hS_card
    have hn_even' : n = 2 * (n / 2) := by
      exact (Nat.div_mul_cancel hEven.two_dvd).symm.trans (by rw [mul_comm])
    omega
  · have hcompl_card : #Sᶜ = n / 2 := by
      rw [Finset.card_compl, hS_card]
      have hn_even' : n = 2 * (n / 2) := by
        exact (Nat.div_mul_cancel hEven.two_dvd).symm.trans (by rw [mul_comm])
      omega
    have hle : #{x : G | twoAdicOrderValuation (orderOf x) = k} ≤ n / 2 := by
      exact (Finset.card_le_card hsub).trans_eq hcompl_card
    have hn_even' : n = 2 * (n / 2) := by
      exact (Nat.div_mul_cancel hEven.two_dvd).symm.trans (by rw [mul_comm])
    omega

/-- Count pairs whose component orders have the same two-adic valuation. -/
@[nolint unusedArguments]
noncomputable def valuationEqualPairCount (G H : Type*) [Group G] [Group H]
    [Fintype G] [Fintype H] : ℕ :=
  #{z : G × H |
    twoAdicOrderValuation (orderOf z.1) =
      twoAdicOrderValuation (orderOf z.2)}

/-- If the left component is cyclic of even cardinality, then pairs with equal
two-adic order valuations occupy at most half of the product sample space
[Sho95, source.tex:1155-1169]. -/
theorem valuationEqualPairCount_le_half_left
    {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H]
    [IsCyclic G] (hEvenG : Even (Fintype.card G)) :
    2 * valuationEqualPairCount G H ≤ Fintype.card (G × H) := by
  classical
  unfold valuationEqualPairCount
  have hfiber (y : H) :
      #{x : G |
        twoAdicOrderValuation (orderOf x) =
          twoAdicOrderValuation (orderOf y)} ≤ Fintype.card G / 2 := by
    have h :=
      card_twoAdicOrderValuation_fiber_le_half
        (G := G) hEvenG (twoAdicOrderValuation (orderOf y))
    omega
  have hsum :
      #{z : G × H |
        twoAdicOrderValuation (orderOf z.1) =
          twoAdicOrderValuation (orderOf z.2)} ≤
        Fintype.card H * (Fintype.card G / 2) := by
    rw [Finset.card_filter]
    rw [← Finset.univ_product_univ (α := G) (β := H)]
    rw [Finset.sum_product]
    rw [Finset.sum_comm]
    calc
      (∑ y ∈ (Finset.univ : Finset H), ∑ x ∈ (Finset.univ : Finset G),
          if twoAdicOrderValuation (orderOf x) =
              twoAdicOrderValuation (orderOf y) then 1 else 0)
          ≤ ∑ _y ∈ (Finset.univ : Finset H), Fintype.card G / 2 := by
            gcongr with y hy
            have h := hfiber y
            rw [Finset.card_filter] at h
            simpa using h
      _ = Fintype.card H * (Fintype.card G / 2) := by
        simp [Finset.sum_const]
  have hcard_even : Fintype.card G = 2 * (Fintype.card G / 2) := by
    exact (Nat.div_mul_cancel hEvenG.two_dvd).symm.trans (by rw [mul_comm])
  rw [Fintype.card_prod, hcard_even]
  nlinarith [hsum]

/-- If the left cyclic component has even cardinality, then there is an actual
component pair whose component orders have different two-adic valuations. This
is the existence counterpart of the bad-event half-count in Shor's semiprime
random-base analysis [Sho95, source.tex:1155-1169]. -/
theorem exists_valuation_ne_of_left_even
    {G H : Type*} [Group G] [Group H]
    [Fintype G] [Finite H]
    [IsCyclic G] (hEvenG : Even (Fintype.card G)) :
    ∃ z : G × H,
      twoAdicOrderValuation (orderOf z.1) ≠
        twoAdicOrderValuation (orderOf z.2) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  by_contra hnone
  have hall : ∀ z : G × H,
      twoAdicOrderValuation (orderOf z.1) =
        twoAdicOrderValuation (orderOf z.2) := by
    intro z
    by_contra hz
    exact hnone ⟨z, hz⟩
  have hfilter :
      ({z : G × H |
        twoAdicOrderValuation (orderOf z.1) =
          twoAdicOrderValuation (orderOf z.2)} : Finset (G × H)) =
        Finset.univ := by
    ext z
    simp [hall z]
  have hbad_eq :
      valuationEqualPairCount G H = Fintype.card (G × H) := by
    unfold valuationEqualPairCount
    rw [hfilter]
    simp
  have hle := valuationEqualPairCount_le_half_left
    (G := G) (H := H) hEvenG
  rw [hbad_eq] at hle
  have hpos : 0 < Fintype.card (G × H) :=
    Fintype.card_pos_iff.mpr ⟨(1, 1)⟩
  omega

/-- Public random-base sample for Shor's semiprime factor-yield route. The
sample space is the unit group of the public modulus, before any successful-base
condition is imposed [Sho95, source.tex:1132-1169]. -/
structure RandomBaseUnitSample {N : ℕ}
    (model : SemiprimeFactorModel N) where
  /-- Selected random unit modulo the public semiprime modulus. -/
  unit : (ZMod N)ˣ

namespace RandomBaseUnitSample

/-- Interpret a raw unit as a random-base sample. -/
def ofUnit {N : ℕ} {model : SemiprimeFactorModel N}
    (u : (ZMod N)ˣ) : RandomBaseUnitSample model where
  unit := u

@[simp] theorem ofUnit_unit {N : ℕ} {model : SemiprimeFactorModel N}
    (u : (ZMod N)ˣ) : (ofUnit (model := model) u).unit = u :=
  rfl

/-- Canonical natural-number representative of the sampled unit. This is the
base used by the classical gcd bridge after order recovery. -/
def baseResidue {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) : ℕ :=
  (sample.unit : ZMod N).val

/-- The canonical base representative denotes the sampled unit modulo `N`. -/
theorem baseResidue_natCast {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    ((sample.baseResidue : ℕ) : ZMod N) = (sample.unit : ZMod N) := by
  haveI : NeZero N :=
    ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one)⟩
  exact ZMod.natCast_zmod_val (sample.unit : ZMod N)

/-- The sampled unit's canonical base representative is positive. -/
theorem baseResidue_pos {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    0 < sample.baseResidue := by
  haveI : Fact (1 < N) := ⟨model.modulus_gt_one⟩
  exact (ZMod.val_pos).mpr (Units.ne_zero sample.unit)

/-- If the sampled unit returns to one, so does its canonical natural-number
representative modulo `N`. -/
theorem baseResidue_pow_modEq_one_of_unit_pow_eq_one
    {N r : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hpow : sample.unit ^ r = 1) :
    sample.baseResidue ^ r ≡ 1 [MOD N] := by
  have hzmod : (((sample.baseResidue ^ r : ℕ) : ZMod N) = (1 : ZMod N)) := by
    have hval := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hpow
    have hbase' :
        (((sample.unit : ZMod N).val : ℕ) : ZMod N) = (sample.unit : ZMod N) := by
      simpa [baseResidue] using baseResidue_natCast sample
    simpa [baseResidue, hbase', Units.val_pow_eq_pow_val, Nat.cast_pow] using hval
  have hzmod' :
      (((sample.baseResidue ^ r : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N)) := by
    simpa using hzmod
  exact (ZMod.natCast_eq_natCast_iff (sample.baseResidue ^ r) 1 N).mp hzmod'

/-- Projection of a public semiprime unit sample to the left prime-factor
component. This is a structural CRT-facing projection, not a good-base
assumption [Sho95, source.tex:1132-1169]. -/
def leftComponent {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) : (ZMod model.leftFactor)ˣ :=
  ZMod.unitsMap model.leftFactor_dvd_modulus sample.unit

/-- Projection of a public semiprime unit sample to the right prime-factor
component. -/
def rightComponent {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) : (ZMod model.rightFactor)ˣ :=
  ZMod.unitsMap model.rightFactor_dvd_modulus sample.unit

@[simp] theorem leftComponent_val {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    (sample.leftComponent : ZMod model.leftFactor) =
      ((sample.unit : ZMod N).cast : ZMod model.leftFactor) :=
  rfl

@[simp] theorem rightComponent_val {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    (sample.rightComponent : ZMod model.rightFactor) =
      ((sample.unit : ZMod N).cast : ZMod model.rightFactor) :=
  rfl

/-- Pair of prime-factor components associated with a random unit sample. The
order-decomposition theorems for this pair are tracked separately; this
definition only exposes the public sample carrier and its projections [Sho95,
source.tex:1132-1169]. -/
def componentPair {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    (ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ :=
  (sample.leftComponent, sample.rightComponent)

@[simp] theorem componentPair_fst {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    sample.componentPair.1 = sample.leftComponent :=
  rfl

@[simp] theorem componentPair_snd {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    sample.componentPair.2 = sample.rightComponent :=
  rfl

/-- CRT equivalence from the public semiprime unit group to the two prime-factor
unit groups. This is the semiprime specialization of Shor's component-order
decomposition before the good-base counting argument [Sho95,
source.tex:1147-1156]. -/
noncomputable def crtComponentEquiv {N : ℕ}
    (model : SemiprimeFactorModel N) :
    (ZMod N)ˣ ≃* (ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ :=
  (Units.mapEquiv (ZMod.ringEquivCongr model.product_eq).toMulEquiv).trans
    ((Units.mapEquiv (ZMod.chineseRemainder model.leftRight_coprime).toMulEquiv).trans
      MulEquiv.prodUnits)

/-- The CRT component pair used for order decomposition. This pair is
definitionally tied to the CRT equivalence rather than to a good-base
assumption. -/
noncomputable def crtComponentPair {N : ℕ}
    {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    (ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ :=
  crtComponentEquiv model sample.unit

/-- Shor's semiprime good-base event for a sampled public unit: the two CRT
component orders have different two-adic valuations [Sho95,
source.tex:1155-1169]. -/
def GoodEvent {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) : Prop :=
  twoAdicOrderValuation (orderOf sample.crtComponentPair.1) ≠
    twoAdicOrderValuation (orderOf sample.crtComponentPair.2)

/-- The left component order divides the global public-unit order. -/
theorem leftComponent_order_dvd_global {N : ℕ}
    {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    orderOf sample.leftComponent ∣ orderOf sample.unit :=
  orderOf_map_dvd (ZMod.unitsMap model.leftFactor_dvd_modulus) sample.unit

/-- The right component order divides the global public-unit order. -/
theorem rightComponent_order_dvd_global {N : ℕ}
    {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    orderOf sample.rightComponent ∣ orderOf sample.unit :=
  orderOf_map_dvd (ZMod.unitsMap model.rightFactor_dvd_modulus) sample.unit

/-- The LCM of the structural component orders divides the global public-unit
order. -/
private theorem componentOrder_lcm_dvd_global {N : ℕ}
    {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    Nat.lcm (orderOf sample.leftComponent) (orderOf sample.rightComponent) ∣
      orderOf sample.unit :=
  Nat.lcm_dvd (leftComponent_order_dvd_global sample)
    (rightComponent_order_dvd_global sample)

/-- Under the CRT unit equivalence, the order of a public semiprime unit is the
LCM of the two prime-factor component orders, matching the component-order step
in Shor's good-base sketch [Sho95, source.tex:1147-1156]. -/
theorem orderOf_eq_lcm_crtComponentPair {N : ℕ}
    {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model) :
    orderOf sample.unit =
      Nat.lcm (orderOf sample.crtComponentPair.1)
        (orderOf sample.crtComponentPair.2) := by
  have h :
      orderOf ((crtComponentEquiv model).toMonoidHom sample.unit) =
        orderOf sample.unit :=
    orderOf_injective (crtComponentEquiv model).toMonoidHom
      (crtComponentEquiv model).injective sample.unit
  rw [← h]
  simpa [crtComponentPair] using
    (Prod.orderOf_mk
      (a := ((crtComponentEquiv model) sample.unit).1)
      (b := ((crtComponentEquiv model) sample.unit).2))

/-- In the asymmetric two-adic case, the smaller-valuation CRT component
becomes the identity after the global half-order exponent. -/
theorem left_crtComponent_pow_lcm_div_two_eq_one_of_leftTwoAdic_lt_right
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.crtComponentPair.1 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = 1 := by
  have ha : orderOf sample.crtComponentPair.1 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.1).ne'
  have hb : orderOf sample.crtComponentPair.2 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.2).ne'
  exact (orderOf_dvd_iff_pow_eq_one).mp
    (left_dvd_lcm_div_two_of_left_twoAdic_lt_right ha hb hlt)

/-- In the asymmetric two-adic case, the larger-valuation CRT component is not
the identity after the global half-order exponent. -/
theorem right_crtComponent_pow_lcm_div_two_ne_one_of_leftTwoAdic_lt_right
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.crtComponentPair.2 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ 1 := by
  have ha : orderOf sample.crtComponentPair.1 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.1).ne'
  have hb : orderOf sample.crtComponentPair.2 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.2).ne'
  intro hpow
  exact right_not_dvd_lcm_div_two_of_left_twoAdic_lt_right ha hb hlt
    ((orderOf_dvd_iff_pow_eq_one).mpr hpow)

/-- The CRT half-order product is not the identity when the right component
has larger two-adic valuation. -/
theorem crtComponentPair_pow_lcm_div_two_ne_one_of_leftTwoAdic_lt_right
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.crtComponentPair ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ 1 := by
  intro h
  have hright :
      sample.crtComponentPair.2 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = 1 := by
    simpa using congrArg Prod.snd h
  exact right_crtComponent_pow_lcm_div_two_ne_one_of_leftTwoAdic_lt_right
    sample hlt hright

/-- The CRT half-order product is not the global negative-one branch when the
right component has larger two-adic valuation and the left factor has odd
characteristic. -/
theorem crtComponentPair_pow_lcm_div_two_ne_neg_one_of_leftTwoAdic_lt_right
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hleftOdd : 2 < model.leftFactor)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.crtComponentPair ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ -1 := by
  haveI : Fact (2 < model.leftFactor) := ⟨hleftOdd⟩
  intro h
  have hleft :
      sample.crtComponentPair.1 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = (-1 : (ZMod model.leftFactor)ˣ) := by
    simpa using congrArg Prod.fst h
  have hone :
      sample.crtComponentPair.1 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = 1 :=
    left_crtComponent_pow_lcm_div_two_eq_one_of_leftTwoAdic_lt_right sample hlt
  have hunit : (1 : (ZMod model.leftFactor)ˣ) = -1 :=
    hone.symm.trans hleft
  have hval :=
    congrArg (fun u : (ZMod model.leftFactor)ˣ =>
      (u : ZMod model.leftFactor)) hunit
  exact ZMod.neg_one_ne_one (n := model.leftFactor) hval.symm

/-- Symmetric identity component theorem for the case where the left component
has larger two-adic valuation. -/
theorem right_crtComponent_pow_lcm_div_two_eq_one_of_rightTwoAdic_lt_left
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.2) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.1)) :
    sample.crtComponentPair.2 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = 1 := by
  have ha : orderOf sample.crtComponentPair.2 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.2).ne'
  have hb : orderOf sample.crtComponentPair.1 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.1).ne'
  have hdiv :=
    left_dvd_lcm_div_two_of_left_twoAdic_lt_right ha hb hlt
  rw [Nat.lcm_comm] at hdiv
  exact (orderOf_dvd_iff_pow_eq_one).mp hdiv

/-- Symmetric non-identity component theorem for the case where the left
component has larger two-adic valuation. -/
theorem left_crtComponent_pow_lcm_div_two_ne_one_of_rightTwoAdic_lt_left
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.2) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.1)) :
    sample.crtComponentPair.1 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ 1 := by
  have ha : orderOf sample.crtComponentPair.2 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.2).ne'
  have hb : orderOf sample.crtComponentPair.1 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.1).ne'
  have hnot :=
    right_not_dvd_lcm_div_two_of_left_twoAdic_lt_right ha hb hlt
  rw [Nat.lcm_comm] at hnot
  intro hpow
  exact hnot ((orderOf_dvd_iff_pow_eq_one).mpr hpow)

/-- The CRT half-order product is not the identity when the left component has
larger two-adic valuation. -/
theorem crtComponentPair_pow_lcm_div_two_ne_one_of_rightTwoAdic_lt_left
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.2) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.1)) :
    sample.crtComponentPair ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ 1 := by
  intro h
  have hleft :
      sample.crtComponentPair.1 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = 1 := by
    simpa using congrArg Prod.fst h
  exact left_crtComponent_pow_lcm_div_two_ne_one_of_rightTwoAdic_lt_left
    sample hlt hleft

/-- The CRT half-order product is not the global negative-one branch when the
left component has larger two-adic valuation and the right factor has odd
characteristic. -/
theorem crtComponentPair_pow_lcm_div_two_ne_neg_one_of_rightTwoAdic_lt_left
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hrightOdd : 2 < model.rightFactor)
    (hlt :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.2) <
        twoAdicOrderValuation (orderOf sample.crtComponentPair.1)) :
    sample.crtComponentPair ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ -1 := by
  haveI : Fact (2 < model.rightFactor) := ⟨hrightOdd⟩
  intro h
  have hright :
      sample.crtComponentPair.2 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = (-1 : (ZMod model.rightFactor)ˣ) := by
    simpa using congrArg Prod.snd h
  have hone :
      sample.crtComponentPair.2 ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) = 1 :=
    right_crtComponent_pow_lcm_div_two_eq_one_of_rightTwoAdic_lt_left sample hlt
  have hunit : (1 : (ZMod model.rightFactor)ˣ) = -1 :=
    hone.symm.trans hright
  have hval :=
    congrArg (fun u : (ZMod model.rightFactor)ˣ =>
      (u : ZMod model.rightFactor)) hunit
  exact ZMod.neg_one_ne_one (n := model.rightFactor) hval.symm

/-- Unequal component two-adic order valuations force the CRT half-order product
away from the identity. -/
theorem crtComponentPair_pow_lcm_div_two_ne_one_of_twoAdic_ne
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hne :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) ≠
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.crtComponentPair ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ 1 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact crtComponentPair_pow_lcm_div_two_ne_one_of_leftTwoAdic_lt_right sample hlt
  · exact crtComponentPair_pow_lcm_div_two_ne_one_of_rightTwoAdic_lt_left sample hgt

/-- Unequal component two-adic order valuations force the CRT half-order product
away from the negative-one branch, under explicit odd-prime-factor hypotheses. -/
theorem crtComponentPair_pow_lcm_div_two_ne_neg_one_of_twoAdic_ne
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hleftOdd : 2 < model.leftFactor)
    (hrightOdd : 2 < model.rightFactor)
    (hne :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) ≠
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.crtComponentPair ^
        (Nat.lcm (orderOf sample.crtComponentPair.1)
          (orderOf sample.crtComponentPair.2) / 2) ≠ -1 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact crtComponentPair_pow_lcm_div_two_ne_neg_one_of_leftTwoAdic_lt_right
      sample hleftOdd hlt
  · exact crtComponentPair_pow_lcm_div_two_ne_neg_one_of_rightTwoAdic_lt_left
      sample hrightOdd hgt

/-- Unequal component two-adic order valuations force the global half-order
power away from the identity. -/
theorem unit_pow_halfOrder_ne_one_of_twoAdic_ne
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hne :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) ≠
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.unit ^ (orderOf sample.unit / 2) ≠ 1 := by
  intro hunit
  have hmap :
      (crtComponentEquiv model sample.unit) ^
          (orderOf sample.unit / 2) = 1 := by
    simpa using congrArg (fun u => crtComponentEquiv model u) hunit
  have horder := orderOf_eq_lcm_crtComponentPair sample
  have hpair :
      sample.crtComponentPair ^
          (Nat.lcm (orderOf sample.crtComponentPair.1)
            (orderOf sample.crtComponentPair.2) / 2) = 1 := by
    simpa [crtComponentPair, horder] using hmap
  exact crtComponentPair_pow_lcm_div_two_ne_one_of_twoAdic_ne sample hne hpair

/-- Unequal component two-adic order valuations force the global half-order
power away from the negative-one branch, under explicit odd-prime-factor
hypotheses. -/
theorem unit_pow_halfOrder_ne_neg_one_of_twoAdic_ne
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hleftOdd : 2 < model.leftFactor)
    (hrightOdd : 2 < model.rightFactor)
    (hne :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) ≠
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    sample.unit ^ (orderOf sample.unit / 2) ≠ -1 := by
  intro hunit
  have hmap_neg :
      (crtComponentEquiv model) (-1 : (ZMod N)ˣ) =
        (-1 : (ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ) := by
    ext
    · simp [crtComponentEquiv, Units.coe_mapEquiv, MulEquiv.prodUnits]
    · simp [crtComponentEquiv, Units.coe_mapEquiv, MulEquiv.prodUnits]
  have hmap :
      (crtComponentEquiv model sample.unit) ^
          (orderOf sample.unit / 2) = -1 := by
    simpa [hmap_neg] using congrArg (fun u => crtComponentEquiv model u) hunit
  have horder := orderOf_eq_lcm_crtComponentPair sample
  have hpair :
      sample.crtComponentPair ^
          (Nat.lcm (orderOf sample.crtComponentPair.1)
            (orderOf sample.crtComponentPair.2) / 2) = -1 := by
    simpa [crtComponentPair, horder] using hmap
  exact crtComponentPair_pow_lcm_div_two_ne_neg_one_of_twoAdic_ne
    sample hleftOdd hrightOdd hne hpair

/-- Unit-level Shor good-base criterion for a semiprime random base: unequal
two-adic valuations of the two CRT component orders make the global order even,
and the global half-order power is neither `1` nor `-1` [Sho95,
source.tex:1150-1155]. -/
theorem halfOrderPow_ne_one_and_negOne_of_twoAdic_ne
    {N : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (hleftOdd : 2 < model.leftFactor)
    (hrightOdd : 2 < model.rightFactor)
    (hne :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) ≠
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    Even (orderOf sample.unit) ∧
      sample.unit ^ (orderOf sample.unit / 2) ≠ 1 ∧
      sample.unit ^ (orderOf sample.unit / 2) ≠ (-1 : (ZMod N)ˣ) := by
  have horder := orderOf_eq_lcm_crtComponentPair sample
  have hleft_ne : orderOf sample.crtComponentPair.1 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.1).ne'
  have hright_ne : orderOf sample.crtComponentPair.2 ≠ 0 :=
    (orderOf_pos sample.crtComponentPair.2).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [horder]
    exact even_lcm_of_twoAdic_ne hleft_ne hright_ne hne
  · exact unit_pow_halfOrder_ne_one_of_twoAdic_ne sample hne
  · exact unit_pow_halfOrder_ne_neg_one_of_twoAdic_ne
      sample hleftOdd hrightOdd hne

/-- A non-identity half-order unit power gives the left nonzero modular
side-condition for the canonical natural-number representative. -/
theorem left_nonzero_mod_of_unit_halfOrder_ne_one
    {N k : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (h : sample.unit ^ k ≠ 1) :
    ¬ (sample.baseResidue ^ k - 1) ≡ 0 [MOD N] := by
  intro hmod
  have hpos : 0 < sample.baseResidue ^ k :=
    pow_pos (baseResidue_pos sample) k
  have hone_le : 1 ≤ sample.baseResidue ^ k := Nat.succ_le_of_lt hpos
  have hzsub :
      (((sample.baseResidue ^ k - 1 : ℕ) : ZMod N) = (0 : ZMod N)) := by
    have :=
      (ZMod.natCast_eq_natCast_iff (sample.baseResidue ^ k - 1) 0 N).mpr hmod
    simpa using this
  have hpow_zmod : ((sample.baseResidue ^ k : ℕ) : ZMod N) = (1 : ZMod N) := by
    have hsub :
        ((sample.baseResidue ^ k : ℕ) : ZMod N) - (1 : ZMod N) = 0 := by
      simpa [Nat.cast_sub hone_le] using hzsub
    exact sub_eq_zero.mp hsub
  have hunit : sample.unit ^ k = 1 := by
    apply Units.ext
    have hbase' :
        (((sample.unit : ZMod N).val : ℕ) : ZMod N) = (sample.unit : ZMod N) := by
      simpa [baseResidue] using baseResidue_natCast sample
    simpa [baseResidue, hbase', Units.val_pow_eq_pow_val, Nat.cast_pow] using hpow_zmod
  exact h hunit

/-- A non-negative-one half-order unit power gives the right nonzero modular
side-condition for the canonical natural-number representative. -/
theorem right_nonzero_mod_of_unit_halfOrder_ne_neg_one
    {N k : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (h : sample.unit ^ k ≠ -1) :
    ¬ (sample.baseResidue ^ k + 1) ≡ 0 [MOD N] := by
  intro hmod
  have hzadd :
      (((sample.baseResidue ^ k + 1 : ℕ) : ZMod N) = (0 : ZMod N)) := by
    have :=
      (ZMod.natCast_eq_natCast_iff (sample.baseResidue ^ k + 1) 0 N).mpr hmod
    simpa using this
  have hpow_zmod : ((sample.baseResidue ^ k : ℕ) : ZMod N) = (-1 : ZMod N) := by
    have hadd :
        ((sample.baseResidue ^ k : ℕ) : ZMod N) + (1 : ZMod N) = 0 := by
      simpa [Nat.cast_add] using hzadd
    exact add_eq_zero_iff_eq_neg.mp hadd
  have hunit : sample.unit ^ k = -1 := by
    apply Units.ext
    have hbase' :
        (((sample.unit : ZMod N).val : ℕ) : ZMod N) = (sample.unit : ZMod N) := by
      simpa [baseResidue] using baseResidue_natCast sample
    simpa [baseResidue, hbase', Units.val_pow_eq_pow_val, Nat.cast_pow] using hpow_zmod
  exact h hunit

/-- Build Shor's half-order gcd input from a semiprime random-base sample whose
CRT component orders satisfy the good-base two-adic criterion [Sho95,
source.tex:1150-1155]. The recovered order `r` is kept explicit so the bridge
matches the order-finding handoff instead of silently replacing it by an
internal definition. -/
theorem halfOrderGcdInput_of_goodBase
    {N r : ℕ} {model : SemiprimeFactorModel N}
    (sample : RandomBaseUnitSample model)
    (horder : orderOf sample.unit = r)
    (hleftOdd : 2 < model.leftFactor)
    (hrightOdd : 2 < model.rightFactor)
    (hne :
      twoAdicOrderValuation (orderOf sample.crtComponentPair.1) ≠
        twoAdicOrderValuation (orderOf sample.crtComponentPair.2)) :
    HalfOrderGcdInput N sample.baseResidue r := by
  have hgood :=
    halfOrderPow_ne_one_and_negOne_of_twoAdic_ne
      sample hleftOdd hrightOdd hne
  refine
    { modulus_gt_one := model.modulus_gt_one
      base_pos := baseResidue_pos sample
      even_order := ?_
      return_to_one := ?_
      left_nonzero_mod := ?_
      right_nonzero_mod := ?_ }
  · simpa [horder] using hgood.1
  · rw [← horder]
    exact baseResidue_pow_modEq_one_of_unit_pow_eq_one sample
      (pow_orderOf_eq_one sample.unit)
  · rw [← horder]
    exact left_nonzero_mod_of_unit_halfOrder_ne_one sample hgood.2.1
  · rw [← horder]
    exact right_nonzero_mod_of_unit_halfOrder_ne_neg_one sample hgood.2.2

/-- Existence of an actual Shor good-base sample for a public semiprime with
odd left prime factor. This connects the counting theorem to a concrete sample
whose CRT component orders have unequal two-adic valuations [Sho95,
source.tex:1155-1169]. -/
theorem exists_crtComponentPair_twoAdic_ne
    {N : ℕ} (model : SemiprimeFactorModel N)
    (hleftOdd : 2 < model.leftFactor) :
    ∃ sample : RandomBaseUnitSample model,
      GoodEvent sample := by
  classical
  letI : NeZero N :=
    ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one)⟩
  letI : NeZero model.leftFactor := ⟨model.left_prime.ne_zero⟩
  letI : NeZero model.rightFactor := ⟨model.right_prime.ne_zero⟩
  letI : IsCyclic (ZMod model.leftFactor)ˣ :=
    ZMod.isCyclic_units_prime model.left_prime
  have hleftEven : Even (Fintype.card (ZMod model.leftFactor)ˣ) := by
    rw [ZMod.card_units_eq_totient]
    have hne_two : model.leftFactor ≠ 2 := by omega
    rw [Nat.totient_prime model.left_prime]
    exact model.left_prime.even_sub_one hne_two
  obtain ⟨z, hz⟩ :=
    exists_valuation_ne_of_left_even
      (G := (ZMod model.leftFactor)ˣ)
      (H := (ZMod model.rightFactor)ˣ) hleftEven
  let sample : RandomBaseUnitSample model :=
    RandomBaseUnitSample.ofUnit ((crtComponentEquiv model).symm z)
  refine ⟨sample, ?_⟩
  simpa [GoodEvent, sample, crtComponentPair] using hz

/-- Existence of the internal half-order gcd route associated with a Shor
good-base sample. The selected sample and route are produced inside the proof
from public semiprime oddness assumptions; endpoint theorems should consume a
higher-level bridge instead of taking these witnesses as public inputs [Sho95,
source.tex:1132-1169; source.tex:1155-1169]. -/
theorem exists_halfOrderGcdInput_of_publicGoodEvent
    {N : ℕ} (model : SemiprimeFactorModel N)
    (hleftOdd : 2 < model.leftFactor)
    (hrightOdd : 2 < model.rightFactor) :
    ∃ sample : RandomBaseUnitSample model,
      HalfOrderGcdInput N sample.baseResidue (orderOf sample.unit) := by
  obtain ⟨sample, hne⟩ :=
    exists_crtComponentPair_twoAdic_ne model hleftOdd
  exact ⟨sample,
    sample.halfOrderGcdInput_of_goodBase rfl hleftOdd hrightOdd hne⟩

end RandomBaseUnitSample

namespace SemiprimeFactorModel

/-- The Euler totient of the left odd prime factor is even. This supplies the
cyclic half-fiber counting hypothesis used in Shor's semiprime random-base
analysis [Sho95, source.tex:1155-1169]. -/
theorem leftFactor_totient_even {N : ℕ} (model : SemiprimeFactorModel N)
    (hleftOdd : 2 < model.leftFactor) :
    Even (Nat.totient model.leftFactor) := by
  have hne_two : model.leftFactor ≠ 2 := by omega
  rw [Nat.totient_prime model.left_prime]
  exact model.left_prime.even_sub_one hne_two

/-- CRT-side bad-base count: the number of component pairs whose orders have the
same two-adic valuation. Via `crtComponentEquiv`, this is the bad-event count
for the random unit modulo the public semiprime [Sho95, source.tex:1155-1169]. -/
noncomputable def crtBadBaseCount {N : ℕ} (model : SemiprimeFactorModel N) :
    ℕ := by
  letI : NeZero model.leftFactor := ⟨model.left_prime.ne_zero⟩
  letI : NeZero model.rightFactor := ⟨model.right_prime.ne_zero⟩
  exact valuationEqualPairCount (ZMod model.leftFactor)ˣ (ZMod model.rightFactor)ˣ

/-- CRT-side good-base count, as the complement of the equal-valuation bad event
inside the public random-unit sample space. -/
noncomputable def crtGoodBaseCount {N : ℕ} (model : SemiprimeFactorModel N) :
    ℕ :=
  Nat.totient N - model.crtBadBaseCount

/-- The actual finite carrier of Shor good-base samples. Its cardinality is the
registered good-event count used by the public lower-bound package [Sho95,
source.tex:1155-1169]. -/
noncomputable def goodEventUnits {N : ℕ} (model : SemiprimeFactorModel N) :
    Finset (ZMod N)ˣ := by
  classical
  letI : NeZero N :=
    ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one)⟩
  exact Finset.univ.filter fun u =>
    RandomBaseUnitSample.GoodEvent
      (RandomBaseUnitSample.ofUnit (model := model) u)

/-- The finite carrier of Shor good-base samples has cardinality equal to the
CRT good-base count used by the lower-bound package [Sho95,
source.tex:1155-1169]. -/
theorem card_goodEventUnits_eq_crtGoodBaseCount {N : ℕ}
    (model : SemiprimeFactorModel N) :
    #model.goodEventUnits = model.crtGoodBaseCount := by
  classical
  letI : NeZero N :=
    ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one)⟩
  letI : NeZero model.leftFactor := ⟨model.left_prime.ne_zero⟩
  letI : NeZero model.rightFactor := ⟨model.right_prime.ne_zero⟩
  let equiv := RandomBaseUnitSample.crtComponentEquiv model
  let goodPairs : Finset ((ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ) :=
    Finset.univ.filter fun z =>
      twoAdicOrderValuation (orderOf z.1) ≠
        twoAdicOrderValuation (orderOf z.2)
  have hmap :
      model.goodEventUnits.image equiv.toEquiv = goodPairs := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
      have hu_good :
          RandomBaseUnitSample.GoodEvent
            (RandomBaseUnitSample.ofUnit (model := model) u) := by
        simpa [goodEventUnits] using hu
      simpa [goodPairs, RandomBaseUnitSample.GoodEvent,
        RandomBaseUnitSample.crtComponentPair] using hu_good
    · intro hz
      refine Finset.mem_image.mpr ?_
      refine ⟨equiv.symm z, ?_, by simp [equiv]⟩
      simp [goodEventUnits, goodPairs, RandomBaseUnitSample.GoodEvent,
        RandomBaseUnitSample.crtComponentPair] at hz ⊢
      simpa [equiv] using hz
  have hcard_good : #model.goodEventUnits = #goodPairs := by
    rw [← hmap]
    exact (Finset.card_image_of_injective _ equiv.toEquiv.injective).symm
  have hbad :
      model.crtBadBaseCount =
        #{z : (ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ |
          twoAdicOrderValuation (orderOf z.1) =
            twoAdicOrderValuation (orderOf z.2)} := by
    simp [crtBadBaseCount, valuationEqualPairCount]
  have hpartition :
      #goodPairs +
          #{z : (ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ |
            twoAdicOrderValuation (orderOf z.1) =
              twoAdicOrderValuation (orderOf z.2)}
        =
          Fintype.card
            ((ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ) := by
    let p : (ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ → Prop :=
      fun z =>
        twoAdicOrderValuation (orderOf z.1) ≠
          twoAdicOrderValuation (orderOf z.2)
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ :
          Finset ((ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ))) p
    simpa [goodPairs, p] using h
  have htotient :
      Nat.totient N =
        Fintype.card
          ((ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ) := by
    have hcard :
        Nat.totient N =
          Fintype.card (ZMod N)ˣ := by
      rw [ZMod.card_units_eq_totient]
    have hcrt :
        Fintype.card (ZMod N)ˣ =
          Fintype.card
            ((ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ) :=
      Fintype.card_congr (RandomBaseUnitSample.crtComponentEquiv model).toEquiv
    exact hcard.trans hcrt
  rw [hcard_good, crtGoodBaseCount, hbad, htotient]
  omega

/-- The equal two-adic valuation bad event has count at most one half of the
public semiprime unit sample space [Sho95, source.tex:1155-1169]. -/
theorem crtBadBaseCount_atMostHalf {N : ℕ}
    (model : SemiprimeFactorModel N)
    (hleftOdd : 2 < model.leftFactor) :
    2 * model.crtBadBaseCount ≤ Nat.totient N := by
  classical
  letI : NeZero N :=
    ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one)⟩
  letI : NeZero model.leftFactor := ⟨model.left_prime.ne_zero⟩
  letI : NeZero model.rightFactor := ⟨model.right_prime.ne_zero⟩
  letI : IsCyclic (ZMod model.leftFactor)ˣ :=
    ZMod.isCyclic_units_prime model.left_prime
  have hleftEven : Even (Fintype.card (ZMod model.leftFactor)ˣ) := by
    rw [ZMod.card_units_eq_totient]
    exact model.leftFactor_totient_even hleftOdd
  have h :=
    valuationEqualPairCount_le_half_left
      (G := (ZMod model.leftFactor)ˣ)
      (H := (ZMod model.rightFactor)ˣ) hleftEven
  have hcard :
      Nat.totient N =
        Fintype.card (ZMod N)ˣ := by
    rw [ZMod.card_units_eq_totient]
  have hcrt :
      Fintype.card (ZMod N)ˣ =
        Fintype.card ((ZMod model.leftFactor)ˣ × (ZMod model.rightFactor)ˣ) :=
    Fintype.card_congr (RandomBaseUnitSample.crtComponentEquiv model).toEquiv
  rw [hcard, hcrt]
  simpa [crtBadBaseCount] using h

/-- Equivalently, the unequal two-adic valuation good-base event has count at
least one half of the public semiprime unit sample space [Sho95,
source.tex:1155-1169]. -/
theorem crtGoodBaseCount_atLeastHalf {N : ℕ}
    (model : SemiprimeFactorModel N)
    (hleftOdd : 2 < model.leftFactor) :
    Nat.totient N ≤ 2 * model.crtGoodBaseCount := by
  have hbad := model.crtBadBaseCount_atMostHalf hleftOdd
  unfold crtGoodBaseCount
  omega

/-- Public-boundary package for Shor's random-base good-event lower bound. It
keeps only the public semiprime model, the odd-prime side conditions, the
random-unit sample-space count, and the counted good-event lower bound; it does
not take a selected successful base or a factor-yield certificate as input
[Sho95, source.tex:1132-1169; source.tex:1155-1169]. -/
structure RandomBaseGoodEventLowerBound {N : ℕ}
    (model : SemiprimeFactorModel N) where
  /-- The left prime factor is odd. -/
  leftFactor_gt_two : 2 < model.leftFactor
  /-- The right prime factor is odd. -/
  rightFactor_gt_two : 2 < model.rightFactor
  /-- Count of the public random-unit sample space modulo `N`. -/
  sampleSpaceCount : ℕ
  /-- Count of the unequal-valuation good-base event. -/
  goodEventCount : ℕ
  sampleSpaceCount_eq : sampleSpaceCount = Nat.totient N
  goodEventCount_eq : goodEventCount = model.crtGoodBaseCount
  sampleSpaceCount_pos : 0 < sampleSpaceCount
  goodEvent_atLeast_oneHalf : sampleSpaceCount ≤ 2 * goodEventCount

-- Generated structure lemma; the public lower-bound package should simplify
-- through named projections, not constructor-injectivity field explosions.
attribute [-simp] RandomBaseGoodEventLowerBound.mk.injEq
attribute [nolint simpNF] RandomBaseGoodEventLowerBound.mk.injEq

/-- Assemble the public-boundary random-base good-event lower bound from a
public semiprime model with two odd prime factors. The one-half inequality is
derived from the counted CRT good-event theorem, rather than supplied as an
endpoint input [Sho95, source.tex:1155-1169]. -/
noncomputable def randomBaseGoodEventLowerBound {N : ℕ}
    (model : SemiprimeFactorModel N)
    (hleftOdd : 2 < model.leftFactor)
    (hrightOdd : 2 < model.rightFactor) :
    RandomBaseGoodEventLowerBound model where
  leftFactor_gt_two := hleftOdd
  rightFactor_gt_two := hrightOdd
  sampleSpaceCount := Nat.totient N
  goodEventCount := model.crtGoodBaseCount
  sampleSpaceCount_eq := rfl
  goodEventCount_eq := rfl
  sampleSpaceCount_pos := by
    exact Nat.totient_pos.mpr
      (Nat.lt_trans Nat.zero_lt_one model.modulus_gt_one)
  goodEvent_atLeast_oneHalf := model.crtGoodBaseCount_atLeastHalf hleftOdd

namespace RandomBaseGoodEventLowerBound

/-- The counted good-base event is nonempty. This turns the public one-half
lower-bound fields into an existence fact over the actual good-event carrier
[Sho95, source.tex:1155-1169]. -/
theorem goodEventCount_pos {N : ℕ} {model : SemiprimeFactorModel N}
    (good : RandomBaseGoodEventLowerBound model) :
    0 < good.goodEventCount := by
  by_contra hnot
  have hzero : good.goodEventCount = 0 := Nat.eq_zero_of_not_pos hnot
  have hle_zero : good.sampleSpaceCount ≤ 0 := by
    simpa [hzero] using good.goodEvent_atLeast_oneHalf
  have hzero_lt : 0 < 0 :=
    lt_of_lt_of_le good.sampleSpaceCount_pos hle_zero
  exact (Nat.lt_irrefl 0 hzero_lt)

/-- Existence of an actual random-base sample in the counted good event. -/
theorem exists_goodEventSample {N : ℕ}
    {model : SemiprimeFactorModel N}
    (good : RandomBaseGoodEventLowerBound model) :
    ∃ sample : RandomBaseUnitSample model, RandomBaseUnitSample.GoodEvent sample := by
  classical
  have hcard :
      #model.goodEventUnits = good.goodEventCount := by
    rw [model.card_goodEventUnits_eq_crtGoodBaseCount, good.goodEventCount_eq]
  have hnonempty : (model.goodEventUnits).Nonempty :=
    Finset.card_pos.mp (by simpa [hcard] using good.goodEventCount_pos)
  rcases hnonempty with ⟨u, hu⟩
  refine ⟨RandomBaseUnitSample.ofUnit u, ?_⟩
  simpa [goodEventUnits] using hu

/-- Existence of the internal Shor half-order gcd route from the counted
good-base event. The selected sample remains internal to this proof artifact
and is not an endpoint-facing assumption [Sho95, source.tex:1132-1169;
source.tex:1155-1169]. -/
theorem exists_halfOrderGcdInput {N : ℕ}
    {model : SemiprimeFactorModel N}
    (good : RandomBaseGoodEventLowerBound model) :
    ∃ sample : RandomBaseUnitSample model,
      RandomBaseUnitSample.GoodEvent sample ∧
        HalfOrderGcdInput N sample.baseResidue (orderOf sample.unit) := by
  obtain ⟨sample, hgood⟩ := good.exists_goodEventSample
  exact ⟨sample, hgood,
    sample.halfOrderGcdInput_of_goodBase rfl good.leftFactor_gt_two
      good.rightFactor_gt_two hgood⟩

end RandomBaseGoodEventLowerBound

end SemiprimeFactorModel

/-- A returned divisor together with the proof that it is one of the two
declared semiprime factors. -/
structure FactorReturnCertificate {N : ℕ} (model : SemiprimeFactorModel N) where
  /-- Recovered factor or candidate output carried by this certificate. -/
  output : ℕ
  output_dvd_modulus : output ∣ N
  output_gt_one : 1 < output
  output_lt_modulus : output < N
  output_eq_declared_factor :
    output = model.leftFactor ∨ output = model.rightFactor

namespace FactorReturnCertificate

/-- Build a factor-return certificate from any nontrivial divisor of the
declared semiprime modulus. -/
def ofNontrivialDivisor {N d : ℕ} (model : SemiprimeFactorModel N)
    (hdvd : d ∣ N) (hgt : 1 < d) (hlt : d < N) :
    FactorReturnCertificate model where
  output := d
  output_dvd_modulus := hdvd
  output_gt_one := hgt
  output_lt_modulus := hlt
  output_eq_declared_factor :=
    model.nontrivial_factor_eq_declared hdvd hgt hlt

/-- The returned divisor is one of the two declared semiprime factors. -/
theorem output_mem_declared_factors {N : ℕ}
    {model : SemiprimeFactorModel N}
    (cert : FactorReturnCertificate model) :
    cert.output = model.leftFactor ∨ cert.output = model.rightFactor :=
  cert.output_eq_declared_factor

/-- The declared left factor is itself a valid returned factor certificate.
This is the trivial semiprime branch used before entering Shor's odd-prime
random-base analysis. -/
def declaredLeft {N : ℕ} (model : SemiprimeFactorModel N) :
    FactorReturnCertificate model where
  output := model.leftFactor
  output_dvd_modulus := model.leftFactor_dvd_modulus
  output_gt_one := model.left_prime.one_lt
  output_lt_modulus := model.leftFactor_lt_modulus
  output_eq_declared_factor := Or.inl rfl

/-- The declared right factor is itself a valid returned factor certificate.
This is the trivial semiprime branch used before entering Shor's odd-prime
random-base analysis. -/
def declaredRight {N : ℕ} (model : SemiprimeFactorModel N) :
    FactorReturnCertificate model where
  output := model.rightFactor
  output_dvd_modulus := model.rightFactor_dvd_modulus
  output_gt_one := model.right_prime.one_lt
  output_lt_modulus := model.rightFactor_lt_modulus
  output_eq_declared_factor := Or.inr rfl

end FactorReturnCertificate

/-- Left gcd branch of Shor's reduction, packaged as a returned factor
certificate for a declared semiprime modulus. -/
def leftFactorReturnCertificate {N y : ℕ}
    (model : SemiprimeFactorModel N) (h : GcdBridgeInput N y) :
    FactorReturnCertificate model :=
  FactorReturnCertificate.ofNontrivialDivisor model
    (Nat.gcd_dvd_right (y - 1) N)
    (gcd_bridge h).1.1
    (gcd_bridge h).1.2

/-- Right gcd branch of Shor's reduction, packaged as a returned factor
certificate for a declared semiprime modulus. -/
def rightFactorReturnCertificate {N y : ℕ}
    (model : SemiprimeFactorModel N) (h : GcdBridgeInput N y) :
    FactorReturnCertificate model :=
  FactorReturnCertificate.ofNontrivialDivisor model
    (Nat.gcd_dvd_right (y + 1) N)
    (gcd_bridge h).2.1
    (gcd_bridge h).2.2

/-- Half-order left branch, the usual `gcd(x^(r/2)-1,N)` Shor output. -/
def halfOrderLeftFactorReturnCertificate {N x r : ℕ}
    (model : SemiprimeFactorModel N) (h : HalfOrderGcdInput N x r) :
    FactorReturnCertificate model :=
  leftFactorReturnCertificate model (gcdBridgeInput_of_half_order h)

/-- Half-order right branch, the usual `gcd(x^(r/2)+1,N)` Shor output. -/
def halfOrderRightFactorReturnCertificate {N x r : ℕ}
    (model : SemiprimeFactorModel N) (h : HalfOrderGcdInput N x r) :
    FactorReturnCertificate model :=
  rightFactorReturnCertificate model (gcdBridgeInput_of_half_order h)

/-- A probabilistic Shor-style factor-return certificate: the output is a
declared semiprime factor, and the rational success lower bound is explicit.
The probability analysis that supplies the numerator and denominator is kept as
data so this utility layer stays independent from the order-finding probability
module. -/
structure ProbabilisticFactorReturnCertificate {N : ℕ}
    (model : SemiprimeFactorModel N) where
  /-- Recovered factor or candidate output carried by this certificate. -/
  output : FactorReturnCertificate model
  /-- Numerator of the certified success-probability lower bound. -/
  successNumerator : ℕ
  /-- Denominator of the certified success-probability lower bound. -/
  successDenominator : ℕ
  successDenominator_pos : 0 < successDenominator
  success_atLeast :
    2 * successDenominator ≤ 3 * successNumerator

namespace ProbabilisticFactorReturnCertificate

/-- The stored output is one of the declared semiprime factors. -/
theorem output_mem_declared_factors {N : ℕ}
    {model : SemiprimeFactorModel N}
    (cert : ProbabilisticFactorReturnCertificate model) :
    cert.output.output = model.leftFactor ∨
      cert.output.output = model.rightFactor :=
  cert.output.output_mem_declared_factors

/-- The stored rational success lower bound is at least two thirds. -/
theorem successAtLeastTwoThirds {N : ℕ}
    {model : SemiprimeFactorModel N}
    (cert : ProbabilisticFactorReturnCertificate model) :
    2 * cert.successDenominator ≤ 3 * cert.successNumerator :=
  cert.success_atLeast

end ProbabilisticFactorReturnCertificate

end ShorFactoring

end QuantumAlg
