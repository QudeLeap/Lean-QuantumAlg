/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Quantum-free asymptotic helpers

This module contains small asymptotic wrappers that do not depend on the
quantum `Gate` or `HilbertOperator` layers.
-/

section

namespace QuantumAlg

/-- Natural-number resource functions compared by Mathlib's real-valued
`Asymptotics.IsBigO` relation at infinity. -/
public def NatBigO (f g : ℕ → ℕ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (f n : ℝ))
    (fun n : ℕ => (g n : ℝ))

namespace NatBigO

lemma refl (f : ℕ → ℕ) : NatBigO f f := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with n
  simp

/-- Multiplying a natural-number resource function by a fixed constant preserves
its `NatBigO` class. -/
lemma const_mul_left (c : ℕ) (f : ℕ → ℕ) :
    NatBigO (fun n : ℕ => c * f n) f := by
  refine Asymptotics.IsBigO.of_bound (c : ℝ) ?_
  filter_upwards with n
  simp [norm_mul]

/-- An eventual pointwise natural-number bound supplies the corresponding
real-valued `NatBigO` certificate. -/
lemma of_eventually_le_const_mul {f g : ℕ → ℕ} (c : ℕ)
    (h : ∀ᶠ n in Filter.atTop, f n ≤ c * g n) : NatBigO f g := by
  refine Asymptotics.IsBigO.of_bound (c : ℝ) ?_
  filter_upwards [h] with n hn
  simpa only [Real.norm_natCast, Nat.cast_mul] using (Nat.cast_le.2 hn :
    (f n : ℝ) ≤ ((c * g n : Nat) : ℝ))

end NatBigO

end QuantumAlg

end
