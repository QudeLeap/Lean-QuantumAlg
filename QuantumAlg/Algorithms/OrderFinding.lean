/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.QPE

/-!
# Order finding (exact, dyadic period `r ∣ 2^t`)

Order finding is the quantum core of Shor's factoring algorithm. Factoring
reduces to it: for `x` coprime to `N`, the order `r` is the least `r > 0` with
`x^r ≡ 1 (mod N)`, and when `r` is even with `x^{r/2} ≢ ±1 (mod N)` the
greatest common divisors `gcd(x^{r/2} ± 1, N)` are nontrivial factors of `N`
[dW19, qcnotes.tex:1998, 2055]. The arithmetic facts behind that reduction are
that `x` not coprime to `N` already exposes a factor `gcd(x, N)`
[dW19, qcnotes.tex:2009], that the even/`±1` promise holds with probability at
least `1/2` [dW19, qcnotes.tex:2018], and that `(x^{r/2}+1)(x^{r/2}-1)` is a
multiple of `N` whose factors must be shared with `N`
[dW19, qcnotes.tex:2040-2049].

This module formalizes the **exact** regime where the period divides the
register size, `r ∣ 2^t`. There the eigenphase of the modular-multiplication
unitary is the dyadic rational `φ = s/r = (s · 2^t/r) / 2^t`, so quantum phase
estimation (`QuantumAlg.Algorithms.QPE`) is reused as a decoupled interface: it
returns the basis index `j = s · (2^t / r)` exactly. The order is then recovered
by a purely classical `Nat`-gcd computation, with no continued fractions needed
in this exact case:

`r = 2^t / gcd(s · (2^t / r), 2^t)`  whenever  `gcd(s, r) = 1`.

The modular-multiplication unitary `U_a` and its eigenstructure, together with
the general (`r ∤ 2^t`) continued-fraction recovery and the full factoring
pipeline, are out of scope here and are tracked as separate extended-algorithm
work.

## Main results

- `QuantumAlg.order_recovery` — the exact gcd recovery of the order:
  `2^t / gcd(s · (2^t/r), 2^t) = r` for `r ∣ 2^t` and `gcd(s, r) = 1`.
- `QuantumAlg.order_finding_exact` — exact order finding: phase estimation of
  the eigenphase `s/r` reads out `|j⟩` with `j = s · (2^t/r)`, and that `j`
  recovers the order `r`.
- `QuantumAlg.nontrivial_factor_of_dvd_mul` — the classical factoring-reduction
  step: if `N ∣ a · b` but `N ∤ a` and `N ∤ b`, then `gcd(a, N)` is a nontrivial
  factor `1 < gcd(a, N) < N`.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-! ### Classical order recovery -/

/-- **Exact order recovery.** When the period `r` divides the register size
`2^t` and `s` is coprime to `r`, the phase-estimation outcome
`j = s · (2^t / r)` determines the order by a single gcd:
`2^t / gcd(j, 2^t) = r`. The proof is pure `Nat` number theory:
`gcd(s · (2^t/r), 2^t) = gcd(s, r) · (2^t/r) = 2^t/r`, and dividing `2^t` by it
returns `r` [dW19, qcnotes.tex:1998]. -/
theorem order_recovery {t s r : ℕ} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
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
    rw [hm]; exact Nat.mul_div_cancel_left m hr
  have hsr1 : Nat.gcd s r = 1 := hsr
  have hgcd : Nat.gcd (s * (2 ^ t / r)) (2 ^ t) = m := by
    rw [hdiv, hm, Nat.gcd_mul_right, hsr1, Nat.one_mul]
  rw [hgcd, hm]
  exact Nat.mul_div_cancel r hmpos

/-! ### Exact order finding via phase estimation -/

/-- **Exact order finding.** Let the modular-multiplication unitary have the
dyadic eigenphase `φ = s/r` with `r ∣ 2^t` and `gcd(s, r) = 1`, and let
`j = s · (2^t / r)` be the phase-estimation register index. Then:

1. exact quantum phase estimation reads out `|j⟩` (the inverse-QFT readout of
   the phase superposition for `φ = s/r` is the basis state `|j⟩`), reusing
   `QuantumAlg.qpe_correct`; and
2. that outcome recovers the order, `2^t / gcd(j, 2^t) = r`.

This is the decoupled correctness statement: phase estimation enters only
through its proved interface, and the construction of the unitary whose
eigenphase is `s/r` is deferred [dW19, qcnotes.tex:2055]. -/
theorem order_finding_exact {t s r : ℕ} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (hsr : Nat.Coprime s r) (j : Fin (2 ^ t))
    (hj : j.val = s * (2 ^ t / r)) :
    Gate.apply (invQFT t) (phaseState t ((s : ℝ) / r)) = ket j
      ∧ 2 ^ t / Nat.gcd j.val (2 ^ t) = r := by
  refine ⟨?_, ?_⟩
  · apply qpe_correct
    rw [hj]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have h2t0 : (2 : ℝ) ^ t ≠ 0 := by positivity
    have hrr : (r : ℝ) * ((2 ^ t / r : ℕ) : ℝ) = (2 : ℝ) ^ t := by
      exact_mod_cast Nat.mul_div_cancel' hrt
    rw [div_eq_div_iff hr0 h2t0]
    push_cast
    rw [← hrr]; ring
  · rw [hj]; exact order_recovery hr hrt hsr

/-! ### Classical factoring reduction (gcd step) -/

/-- **Factoring-reduction gcd step.** If `N ∣ a · b` while `N` divides neither
`a` nor `b`, then `gcd(a, N)` is a nontrivial factor of `N`, i.e.
`1 < gcd(a, N) < N`. Applied to `a = x^{r/2} - 1`, `b = x^{r/2} + 1` (whose
product `x^r - 1 ≡ 0 (mod N)`), this is exactly how a nontrivial period yields a
factor of `N` [dW19, qcnotes.tex:2040-2049]. -/
theorem nontrivial_factor_of_dvd_mul {N a b : ℕ} (hN : 1 < N)
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

end

end QuantumAlg
