/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! # Whole-word arithmetic from an incremented high subword and unchanged low bits -/

namespace QuantumAlg.Nat.FixedWidth.ModularSuffix

/-- Incrementing a high subword adds its place value modulo the complete capacity. -/
lemma increment_reconstruction (base highCapacity value : Nat) (positive : 0 < base) :
    value % base + base * ((value / base + 1) % highCapacity) =
      (value + base) % (base * highCapacity) := by
  rw [Nat.mod_mul, Nat.add_mod_right, Nat.add_div_right value positive]

/-- The two actual subword readouts determine the whole modular-increment result. -/
lemma increment_of_low_high {base highCapacity before after : Nat}
    (positive : 0 < base) (low : after % base = before % base)
    (high : after / base = (before / base + 1) % highCapacity) :
    after = (before + base) % (base * highCapacity) := by
  calc
    after = after % base + base * (after / base) := (Nat.mod_add_div after base).symm
    _ = before % base + base * ((before / base + 1) % highCapacity) := by rw [low, high]
    _ = _ := increment_reconstruction base highCapacity before positive

/-- A literal reversed increment corresponds to subtracting the same place value. -/
lemma increment_inverse {capacity place before : Nat}
    (fits : place ≤ capacity) (canonical : before < capacity) :
    ((before + place) % capacity + (capacity - place)) % capacity = before := by
  rw [Nat.mod_add_mod]
  have balance : before + place + (capacity - place) = before + capacity := by omega
  rw [balance, Nat.add_mod_right, Nat.mod_eq_of_lt canonical]

end QuantumAlg.Nat.FixedWidth.ModularSuffix
