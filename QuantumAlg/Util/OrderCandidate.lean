/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.ModularMultiplicationDomain
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Classical order-candidate validation

This module contains quantum-free predicates and soundness lemmas for validating
candidate orders after the classical post-processing stage. The generic monoid
version is used for mathematical reuse; the modular-multiplication-domain
wrappers pin the vocabulary to the selected `(ZMod N)^x` carrier.

The validation role is the classical check after Shor period/order recovery:
candidate denominators are tested by return-to-one and then used in the gcd
factoring bridge [Sho95, source.tex:1124-1148] [dW19, qcnotes.tex:2263-2301].
-/

@[expose] public section

namespace QuantumAlg

namespace OrderCandidate

variable {G : Type*} [Monoid G]

/-- A candidate exponent returns the group element to one. -/
def IsPowerReturn (g : G) (r : ℕ) : Prop :=
  0 < r ∧ g ^ r = 1

/-- A smaller positive exponent also returns the group element to one. This is
the non-minimality witness used by failure accounting. -/
def HasSmallerPowerReturn (g : G) (r : ℕ) : Prop :=
  ∃ d, d < r ∧ 0 < d ∧ g ^ d = 1

/-- A candidate exponent passes the minimal order check. -/
def IsMinimalPowerReturn (g : G) (r : ℕ) : Prop :=
  IsPowerReturn g r ∧ ∀ d, d < r → 0 < d → g ^ d ≠ 1

/-- Coarse rejection reasons for candidate-order validation. The constructors
separate zero candidates, failed return-to-one checks, and non-minimal positive
returns for later success-probability accounting. -/
inductive RejectionReason (g : G) (r : ℕ) : Prop where
  | zeroCandidate (h : r = 0)
  | noPowerReturn (h : g ^ r ≠ 1)
  | nonMinimal (h : HasSmallerPowerReturn g r)

private theorem isPowerReturn_pos {g : G} {r : ℕ} (h : IsPowerReturn g r) :
    0 < r :=
  h.1

theorem isPowerReturn_pow_eq_one {g : G} {r : ℕ} (h : IsPowerReturn g r) :
    g ^ r = 1 :=
  h.2

private theorem orderOf_dvd_of_isPowerReturn {g : G} {r : ℕ}
    (h : IsPowerReturn g r) :
    orderOf g ∣ r :=
  orderOf_dvd_of_pow_eq_one h.2

theorem orderOf_eq_of_isMinimalPowerReturn {g : G} {r : ℕ}
    (h : IsMinimalPowerReturn g r) :
    orderOf g = r := by
  exact (orderOf_eq_iff h.1.1).mpr ⟨h.1.2, h.2⟩

theorem isMinimalPowerReturn_of_orderOf_eq {g : G} {r : ℕ}
    (hr : 0 < r) (horder : orderOf g = r) :
    IsMinimalPowerReturn g r := by
  exact ⟨⟨hr, (orderOf_eq_iff hr).mp horder |>.1⟩,
    (orderOf_eq_iff hr).mp horder |>.2⟩

/-- Soundness of accepting a minimal order candidate. -/
theorem validateMinimalPowerReturn_sound {g : G} {r : ℕ}
    (h : IsMinimalPowerReturn g r) :
    r = orderOf g :=
  (orderOf_eq_of_isMinimalPowerReturn h).symm

theorem not_isMinimalPowerReturn_of_rejectionReason {g : G} {r : ℕ}
    (h : RejectionReason g r) :
    ¬ IsMinimalPowerReturn g r := by
  intro hmin
  cases h with
  | zeroCandidate hz =>
      exact (Nat.ne_of_gt hmin.1.1) hz
  | noPowerReturn hpow =>
      exact hpow hmin.1.2
  | nonMinimal hsmall =>
      rcases hsmall with ⟨d, hdr, hdpos, hdpow⟩
      exact hmin.2 d hdr hdpos hdpow

private theorem rejectionReason_of_not_isMinimalPowerReturn {g : G} {r : ℕ}
    (h : ¬ IsMinimalPowerReturn g r) :
    RejectionReason g r := by
  classical
  by_cases hz : r = 0
  · exact RejectionReason.zeroCandidate hz
  · have hr : 0 < r := Nat.pos_of_ne_zero hz
    by_cases hpow : g ^ r = 1
    · by_cases hsmall : HasSmallerPowerReturn g r
      · exact RejectionReason.nonMinimal hsmall
      · exact False.elim (h ⟨⟨hr, hpow⟩, fun d hdr hdpos hdpow =>
          hsmall ⟨d, hdr, hdpos, hdpow⟩⟩)
    · exact RejectionReason.noPowerReturn hpow

end OrderCandidate

namespace ModularMultiplicationDomain

/-- Modular-multiplication order-candidate return-to-one check on the selected
unit-group carrier. -/
def IsOrderCandidate {N n : ℕ} (D : ModularMultiplicationDomain N n)
    (a : UnitCarrier D) (r : ℕ) : Prop :=
  OrderCandidate.IsPowerReturn a r

/-- Minimal modular-multiplication order candidate on the selected unit-group
carrier. -/
def AcceptsOrderCandidate {N n : ℕ} (D : ModularMultiplicationDomain N n)
    (a : UnitCarrier D) (r : ℕ) : Prop :=
  OrderCandidate.IsMinimalPowerReturn a r

/-- Failure vocabulary for modular-multiplication order-candidate validation. -/
def OrderCandidateRejection {N n : ℕ} (D : ModularMultiplicationDomain N n)
    (a : UnitCarrier D) (r : ℕ) : Prop :=
  OrderCandidate.RejectionReason a r

private theorem acceptsOrderCandidate_sound {N n : ℕ} (D : ModularMultiplicationDomain N n)
    {a : UnitCarrier D} {r : ℕ}
    (h : D.AcceptsOrderCandidate a r) :
    r = orderOf a :=
  OrderCandidate.validateMinimalPowerReturn_sound h

private theorem orderOf_eq_of_acceptsOrderCandidate {N n : ℕ} (D : ModularMultiplicationDomain N n)
    {a : UnitCarrier D} {r : ℕ}
    (h : D.AcceptsOrderCandidate a r) :
    orderOf a = r :=
  OrderCandidate.orderOf_eq_of_isMinimalPowerReturn h

private theorem acceptsOrderCandidate_pow_eq_one {N n : ℕ} (D : ModularMultiplicationDomain N n)
    {a : UnitCarrier D} {r : ℕ}
    (h : D.AcceptsOrderCandidate a r) :
    a ^ r = 1 :=
  OrderCandidate.isPowerReturn_pow_eq_one h.1

private theorem not_acceptsOrderCandidate_of_rejection {N n : ℕ}
    (D : ModularMultiplicationDomain N n) {a : UnitCarrier D} {r : ℕ}
    (h : D.OrderCandidateRejection a r) :
    ¬ D.AcceptsOrderCandidate a r :=
  OrderCandidate.not_isMinimalPowerReturn_of_rejectionReason h

end ModularMultiplicationDomain

end QuantumAlg
