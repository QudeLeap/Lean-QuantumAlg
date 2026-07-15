/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.ModularMultiplicationDomain
public import QuantumAlg.Util.ShorFactoring
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Fintype
public import Mathlib.Tactic

/-!
# Order-finding classical utilities

This module contains the quantum-free order-finding input vocabulary and the
classical bridges used by Shor-style factoring reductions. Keeping these facts
in `Util` lets factoring proofs consume recovered-order side conditions without
importing the circuit/QPE-facing order-finding algorithm module.

The statements follow Shor's order-finding-to-factoring reduction and classical
post-processing [Sho95, source.tex:1124-1148] [dW19, qcnotes.tex:1998-2301].
-/

@[expose] public section

namespace QuantumAlg

namespace OrderFinding

/-- Source-level number-theoretic assumptions for exact order finding:
`N ≥ 2`, `x` is coprime to `N`, and `r` is the least positive exponent with
`x^r ≡ 1 (mod N)`. -/
structure Input (N x r : ℕ) : Prop where
  modulus_ge_two : 2 ≤ N
  coprime : Nat.Coprime x N
  order_pos : 0 < r
  order_eq_one : x ^ r % N = 1
  minimal : ∀ m : ℕ, 0 < m → x ^ m % N = 1 → r ≤ m

/-- Exact order recovery from the dyadic phase-estimation output. -/
theorem main_recovery {t s r : ℕ} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (hsr : Nat.Coprime s r) :
    2 ^ t / Nat.gcd (s * (2 ^ t / r)) (2 ^ t) = r := by
  obtain ⟨m, hm⟩ := hrt
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · exfalso
      have h2 : 0 < 2 ^ t := pow_pos (by norm_num) t
      rw [hm, hm0, Nat.mul_zero] at h2
      exact (Nat.lt_irrefl 0) h2
    · exact hm0
  have hdiv : 2 ^ t / r = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hr
  have hsr1 : Nat.gcd s r = 1 := hsr
  have hgcd : Nat.gcd (s * (2 ^ t / r)) (2 ^ t) = m := by
    rw [hdiv, hm, Nat.gcd_mul_right, hsr1, Nat.one_mul]
  rw [hgcd, hm]
  exact Nat.mul_div_cancel r hmpos

/-! ### Register-size bridges -/

/-- If an order `r` is strictly below a modulus `N`, the Shor-style public
register-size bound `N^2 <= 2^t` supplies the scaled-error hypothesis
`r^2 < 2^t`. -/
theorem publicRegisterBound_implies_scaledError_of_order_lt_modulus {N r t : ℕ}
    (hrN : r < N) (hregister : N ^ 2 ≤ 2 ^ t) :
    (r : ℝ) ^ 2 < (2 : ℝ) ^ t := by
  have hsquare : r ^ 2 < N ^ 2 := by
    exact Nat.pow_lt_pow_left hrN (by norm_num : (2 : ℕ) ≠ 0)
  have hnat : r ^ 2 < 2 ^ t := lt_of_lt_of_le hsquare hregister
  exact_mod_cast hnat

/-- The Shor-style public register-size bound alone does not imply the stronger
large-register hypothesis `12*r <= 2^t` used by the current finite
large-register proof. -/
private theorem publicRegisterBound_not_imply_largeRegister :
    (2 ^ 2 ≤ 2 ^ 2 ∧ 2 ^ 2 < 2 * 2 ^ 2) ∧ ¬ 12 * 1 ≤ 2 ^ 2 := by
  norm_num

/-- A source-side strengthening with `12*N <= 2^t` would imply the current
large-register hypothesis from the natural order bound `r <= N`. -/
theorem largeRegister_of_order_le_modulus {N r t : ℕ}
    (hrN : r ≤ N) (hregister : 12 * N ≤ 2 ^ t) :
    12 * r ≤ 2 ^ t := by
  nlinarith

/-- For moduli at least `12`, Shor's public register lower bound `N^2 <= 2^t`
already supplies the large-register hypothesis used by the current finite
source-joint probability route [Sho95, source.tex:1183-1185]. -/
theorem largeRegister_of_publicRegisterBound_of_modulus_ge_twelve
    {N r t : ℕ} (hN : 12 ≤ N) (hrN : r < N)
    (hregister : N ^ 2 ≤ 2 ^ t) :
    12 * r ≤ 2 ^ t := by
  have hr_le : r ≤ N := le_of_lt hrN
  calc
    12 * r ≤ N * r := Nat.mul_le_mul_right r hN
    _ ≤ N * N := Nat.mul_le_mul_left N hr_le
    _ = N ^ 2 := by rw [pow_two]
    _ ≤ 2 ^ t := hregister

/-- In the small-modulus Shor register window, the public upper bound
`2^t < 2N^2` gives a uniform finite search bound for the phase-register size
[Sho95, source.tex:1183-1185]. -/
theorem smallModulus_publicRegisterWindow_t_lt_nine
    {N t : ℕ} (hN_lt : N < 12) (hhi : 2 ^ t < 2 * N ^ 2) :
    t < 9 := by
  by_contra hnot
  have ht_ge : 9 ≤ t := Nat.le_of_not_gt hnot
  have hpow_ge : 2 ^ 9 ≤ 2 ^ t :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) ht_ge
  have hN_le : N ≤ 11 := Nat.le_of_lt_succ hN_lt
  have hsmall : 2 * N ^ 2 < 2 ^ 9 := by
    nlinarith
  have hpow_lt : 2 ^ t < 2 ^ 9 := lt_trans hhi hsmall
  exact (not_le_of_gt hpow_lt) hpow_ge

/-- In the small-modulus branch left by the restored Shor register window,
failure of the current large-register route is confined to an explicit finite
candidate list. This is only a search-space classification: later lemmas still
have to discard impossible orders and prove the residual pointwise probability
certificates [Sho95, source.tex:1183-1185]. -/
theorem smallModulus_publicRegisterWindow_large_or_residual
    {N r t : ℕ}
    (hN_ge : 2 ≤ N) (hN_lt : N < 12) (hr_lt : r < N)
    (hlo : N ^ 2 ≤ 2 ^ t) (hhi : 2 ^ t < 2 * N ^ 2) :
    12 * r ≤ 2 ^ t ∨
      (N = 2 ∧ t = 2 ∧ r = 1) ∨
      (N = 3 ∧ t = 4 ∧ r = 2) ∨
      (N = 4 ∧ t = 4 ∧ (r = 2 ∨ r = 3)) ∨
      (N = 5 ∧ t = 5 ∧ (r = 3 ∨ r = 4)) ∨
      (N = 7 ∧ t = 6 ∧ r = 6) ∨
      (N = 8 ∧ t = 6 ∧ (r = 6 ∨ r = 7)) := by
  have ht_lt : t < 9 := smallModulus_publicRegisterWindow_t_lt_nine hN_lt hhi
  interval_cases N <;> interval_cases t <;> omega

/-! ### Classical factoring reduction (gcd step) -/

/-- Compatibility alias for Shor's gcd side-condition input. -/
abbrev ShorGcdBridgeInput := ShorFactoring.GcdBridgeInput

/-- Compatibility alias for Shor's even-order gcd side-condition input. -/
abbrev ShorHalfOrderGcdInput := ShorFactoring.HalfOrderGcdInput

/-- Compatibility wrapper for the quantum-free factoring-reduction gcd step. -/
theorem main_factor_reduction {N a b : ℕ} (hN : 1 < N)
    (hdvd : N ∣ a * b) (ha : ¬ N ∣ a) (hb : ¬ N ∣ b) :
    1 < Nat.gcd a N ∧ Nat.gcd a N < N :=
  ShorFactoring.main_factor_reduction hN hdvd ha hb

/-- Compatibility wrapper for the half-order square-one bridge. -/
private theorem shor_half_order_square_modEq_one {N x r : ℕ}
    (heven : Even r) (hpow : x ^ r ≡ 1 [MOD N]) :
    (x ^ (r / 2)) * (x ^ (r / 2)) ≡ 1 [MOD N] :=
  ShorFactoring.half_order_square_modEq_one heven hpow

/-- If the order-finding unit-group element generated by `a` has order `r`,
then the source-level natural-number base satisfies `a^r = 1 (mod N)`. This is
the bridge from the order-finding carrier `(ZMod N)^x` to Shor's classical
half-order side-condition vocabulary. -/
theorem shor_return_to_one_modEq_of_unitOfCoprime_order {N n a r : ℕ}
    (D : ModularMultiplicationDomain N n) (ha : Nat.Coprime a N)
    (horder : orderOf (D.unitOfCoprime a ha) = r) :
    a ^ r ≡ 1 [MOD N] := by
  have hunit : (D.unitOfCoprime a ha) ^ r = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one (D.unitOfCoprime a ha)
  have hzmod : ((a ^ r : ℕ) : ZMod N) = (1 : ZMod N) := by
    have hval :=
      congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hunit
    simpa [Units.val_pow_eq_pow_val, Nat.cast_pow] using hval
  have hzmod' : ((a ^ r : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
    simpa using hzmod
  exact (ZMod.natCast_eq_natCast_iff (a ^ r) 1 N).mp hzmod'

/-- The source-level `OrderFinding.Input` minimality condition identifies the
same order as the canonical `ZMod.unitOfCoprime` carrier. -/
theorem orderOf_zmodUnitOfCoprime_eq_input_order {N a r : ℕ}
    (hinput : OrderFinding.Input N a r) :
    orderOf (ZMod.unitOfCoprime a hinput.coprime) = r := by
  have hN_gt_one : 1 < N :=
    Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hinput.modulus_ge_two
  have hone_mod : 1 % N = 1 := Nat.mod_eq_of_lt hN_gt_one
  rw [orderOf_eq_iff hinput.order_pos]
  constructor
  · apply Units.ext
    have hmod : a ^ r ≡ 1 [MOD N] := by
      rw [Nat.ModEq]
      simp [hinput.order_eq_one, hone_mod]
    have hzmod : ((a ^ r : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff (a ^ r) 1 N).mpr hmod
    change (((ZMod.unitOfCoprime a hinput.coprime) ^ r : (ZMod N)ˣ) : ZMod N) =
      ((1 : (ZMod N)ˣ) : ZMod N)
    simpa [Units.val_pow_eq_pow_val, Nat.cast_pow] using hzmod
  · intro m hm hpos hpow
    have hzmod : ((a ^ m : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
      have hval := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hpow
      simpa [Units.val_pow_eq_pow_val, Nat.cast_pow] using hval
    have hmodEq : a ^ m ≡ 1 [MOD N] :=
      (ZMod.natCast_eq_natCast_iff (a ^ m) 1 N).mp hzmod
    have hmod : a ^ m % N = 1 := by
      rw [Nat.ModEq] at hmodEq
      simpa [hone_mod] using hmodEq
    have hle := hinput.minimal m hpos hmod
    omega

/-- The source-level `OrderFinding.Input` minimality condition identifies the
same order as the unit-group carrier used by the modular-multiplication
circuit. This removes a downstream handoff where Shor's gcd bridge had to
assume `orderOf (unitOfCoprime a) = r` separately from the order-finding input. -/
theorem orderOf_unitOfCoprime_eq_input_order {N n a r : ℕ}
    (D : ModularMultiplicationDomain N n) (hinput : OrderFinding.Input N a r) :
    orderOf (D.unitOfCoprime a hinput.coprime) = r := by
  simpa [ModularMultiplicationDomain.unitOfCoprime] using
    orderOf_zmodUnitOfCoprime_eq_input_order hinput

/-- The source-level order is strictly smaller than the modulus. -/
theorem input_order_lt_modulus {N a r : ℕ}
    (hinput : OrderFinding.Input N a r) :
    r < N := by
  have hN_gt_one : 1 < N :=
    Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hinput.modulus_ge_two
  have horder := orderOf_zmodUnitOfCoprime_eq_input_order hinput
  have hlt :
      orderOf ((ZMod.unitOfCoprime a hinput.coprime : (ZMod N)ˣ) : ZMod N) < N :=
    ZMod.orderOf_lt hN_gt_one _
  rw [orderOf_units, horder] at hlt
  exact hlt

/-- The source-level order divides Euler's totient of the modulus. This is the
small-case elimination bridge used when the restored Shor register window leaves
finite residual candidates that cannot occur as unit-group orders. -/
theorem input_order_dvd_totient {N a r : ℕ}
    (hinput : OrderFinding.Input N a r) :
    r ∣ Nat.totient N := by
  have hN_pos : 0 < N :=
    Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hinput.modulus_ge_two
  haveI : NeZero N := ⟨Nat.ne_of_gt hN_pos⟩
  have horder := orderOf_zmodUnitOfCoprime_eq_input_order hinput
  have hdvd :
      orderOf (ZMod.unitOfCoprime a hinput.coprime) ∣ Fintype.card (ZMod N)ˣ :=
    orderOf_dvd_card
  rw [ZMod.card_units_eq_totient] at hdvd
  simpa [horder] using hdvd

/-- For actual order-finding inputs, the small-modulus residual list can be
sharpened by eliminating candidate orders that do not divide Euler's totient of
the modulus. The remaining cases are the finite inputs consumed by the
pointwise-certificate pass. -/
theorem smallModulus_publicRegisterWindow_large_or_possibleResidual
    {N a r t : ℕ}
    (hinput : OrderFinding.Input N a r) (hN_lt : N < 12)
    (hlo : N ^ 2 ≤ 2 ^ t) (hhi : 2 ^ t < 2 * N ^ 2) :
    12 * r ≤ 2 ^ t ∨
      (N = 2 ∧ t = 2 ∧ r = 1) ∨
      (N = 3 ∧ t = 4 ∧ r = 2) ∨
      (N = 4 ∧ t = 4 ∧ r = 2) ∨
      (N = 5 ∧ t = 5 ∧ r = 4) ∨
      (N = 7 ∧ t = 6 ∧ r = 6) := by
  have hclass :=
    smallModulus_publicRegisterWindow_large_or_residual
      hinput.modulus_ge_two hN_lt (input_order_lt_modulus hinput) hlo hhi
  have hdvd := input_order_dvd_totient hinput
  rcases hclass with hlarge | hres
  · exact Or.inl hlarge
  right
  rcases hres with h2 | hres
  · exact Or.inl h2
  rcases hres with h3 | hres
  · exact Or.inr (Or.inl h3)
  rcases hres with h4 | hres
  · rcases h4 with ⟨hN, ht, hr | hr⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hN, ht, hr⟩))
    · subst N
      subst t
      subst r
      have htot : Nat.totient 4 = 2 := by
        rw [show 4 = 2 ^ 2 by norm_num,
          Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 2)]
        norm_num
      rw [htot] at hdvd
      norm_num at hdvd
  rcases hres with h5 | hres
  · rcases h5 with ⟨hN, ht, hr | hr⟩
    · subst N
      subst t
      subst r
      have htot : Nat.totient 5 = 4 := by
        rw [Nat.totient_prime (by norm_num : Nat.Prime 5)]
      rw [htot] at hdvd
      norm_num at hdvd
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hN, ht, hr⟩)))
  rcases hres with h7 | h8
  · exact Or.inr (Or.inr (Or.inr (Or.inr h7)))
  rcases h8 with ⟨hN, ht, hr | hr⟩
  · subst N
    subst t
    subst r
    have htot : Nat.totient 8 = 4 := by
      rw [show 8 = 2 ^ 3 by norm_num,
        Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 3)]
      norm_num
    rw [htot] at hdvd
    norm_num at hdvd
  · subst N
    subst t
    subst r
    have htot : Nat.totient 8 = 4 := by
      rw [show 8 = 2 ^ 3 by norm_num,
        Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 3)]
      norm_num
    rw [htot] at hdvd
    norm_num at hdvd

/-- Build Shor's half-order gcd side-condition input from an order found on the
selected unit-group carrier plus the standard even/nontrivial half-order
checks. -/
theorem shor_halfOrderGcdInput_of_unitOfCoprime_order {N n a r : ℕ}
    (D : ModularMultiplicationDomain N n) (ha : Nat.Coprime a N)
    (hN : 1 < N) (ha_pos : 0 < a)
    (horder : orderOf (D.unitOfCoprime a ha) = r)
    (heven : Even r)
    (hleft : ¬ (a ^ (r / 2) - 1) ≡ 0 [MOD N])
    (hright : ¬ (a ^ (r / 2) + 1) ≡ 0 [MOD N]) :
    ShorHalfOrderGcdInput N a r where
  modulus_gt_one := hN
  base_pos := ha_pos
  even_order := heven
  return_to_one := shor_return_to_one_modEq_of_unitOfCoprime_order D ha horder
  left_nonzero_mod := hleft
  right_nonzero_mod := hright

/-- Build Shor's half-order gcd side-condition input directly from the
order-finding input vocabulary. The base positivity follows from coprimality
and `N ≥ 2`, so callers only provide the source side-condition checks that
Shor treats as retry/failure cases. -/
theorem shor_halfOrderGcdInput_of_input_order {N n a r : ℕ}
    (D : ModularMultiplicationDomain N n) (hinput : OrderFinding.Input N a r)
    (heven : Even r)
    (hleft : ¬ (a ^ (r / 2) - 1) ≡ 0 [MOD N])
    (hright : ¬ (a ^ (r / 2) + 1) ≡ 0 [MOD N]) :
    ShorHalfOrderGcdInput N a r := by
  have hN : 1 < N := Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hinput.modulus_ge_two
  have ha_pos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hnot
    have hcop : Nat.gcd a N = 1 := hinput.coprime
    rw [ha0, Nat.gcd_zero_left] at hcop
    omega
  exact shor_halfOrderGcdInput_of_unitOfCoprime_order D hinput.coprime hN
    ha_pos (orderOf_unitOfCoprime_eq_input_order D hinput) heven hleft hright

/-- Compatibility wrapper for the quantum-free Shor gcd bridge. -/
theorem shor_gcd_bridge {N y : ℕ} (h : ShorGcdBridgeInput N y) :
    (1 < Nat.gcd (y - 1) N ∧ Nat.gcd (y - 1) N < N) ∧
      (1 < Nat.gcd (y + 1) N ∧ Nat.gcd (y + 1) N < N) :=
  ShorFactoring.gcd_bridge h

/-- Compatibility wrapper from even-order Shor side conditions to nontrivial
gcd factors. -/
theorem shor_gcd_bridge_of_half_order {N x r : ℕ}
    (h : ShorHalfOrderGcdInput N x r) :
    (1 < Nat.gcd (x ^ (r / 2) - 1) N ∧ Nat.gcd (x ^ (r / 2) - 1) N < N) ∧
      (1 < Nat.gcd (x ^ (r / 2) + 1) N ∧ Nat.gcd (x ^ (r / 2) + 1) N < N) :=
  ShorFactoring.gcd_bridge_of_half_order h

/-- Direct Shor side-condition bridge from an order found on the selected
unit-group carrier to nontrivial gcd factors for the half-order residue. -/
private theorem shor_gcd_bridge_of_unitOfCoprime_order {N n a r : ℕ}
    (D : ModularMultiplicationDomain N n) (ha : Nat.Coprime a N)
    (hN : 1 < N) (ha_pos : 0 < a)
    (horder : orderOf (D.unitOfCoprime a ha) = r)
    (heven : Even r)
    (hleft : ¬ (a ^ (r / 2) - 1) ≡ 0 [MOD N])
    (hright : ¬ (a ^ (r / 2) + 1) ≡ 0 [MOD N]) :
    (1 < Nat.gcd (a ^ (r / 2) - 1) N ∧ Nat.gcd (a ^ (r / 2) - 1) N < N) ∧
      (1 < Nat.gcd (a ^ (r / 2) + 1) N ∧ Nat.gcd (a ^ (r / 2) + 1) N < N) :=
  shor_gcd_bridge_of_half_order
    (shor_halfOrderGcdInput_of_unitOfCoprime_order D ha hN ha_pos horder
      heven hleft hright)

/-- Direct Shor side-condition bridge from the order-finding input vocabulary
to nontrivial gcd factors for the half-order residue. -/
theorem shor_gcd_bridge_of_input_order {N n a r : ℕ}
    (D : ModularMultiplicationDomain N n) (hinput : OrderFinding.Input N a r)
    (heven : Even r)
    (hleft : ¬ (a ^ (r / 2) - 1) ≡ 0 [MOD N])
    (hright : ¬ (a ^ (r / 2) + 1) ≡ 0 [MOD N]) :
    (1 < Nat.gcd (a ^ (r / 2) - 1) N ∧ Nat.gcd (a ^ (r / 2) - 1) N < N) ∧
      (1 < Nat.gcd (a ^ (r / 2) + 1) N ∧ Nat.gcd (a ^ (r / 2) + 1) N < N) :=
  shor_gcd_bridge_of_half_order
    (shor_halfOrderGcdInput_of_input_order D hinput heven hleft hright)

end OrderFinding

end QuantumAlg
