/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Cslib.Algorithms.Lean.TimeM

/-!
# Trusted cost annotations

This module connects Lean-QuantumAlg theorem endpoints to CSLib's `TimeM`
interface. A value of `Timed α` returns an object of type `α` and carries a
trusted natural-number cost annotation.

The cost annotation is intentionally not derived from the Lean evaluator or from
matrix dimensions. Following CSLib's `TimeM` convention, correctness is proved
on `.ret`, while `.time` records the selected model. In the current quantum
algorithm bridge, one unit means one oracle query for the single-query
Walsh-Hadamard algorithms, and one good/bad-plane iterate for amplitude
amplification and Grover.

This is an operator-level bridge over the existing pure-state and gate
semantics. Fuller quantum program logics, such as density-operator or
Hoare-style semantics for quantum while programs, are future extensions rather
than prerequisites for this TimeM layer.
-/

@[expose] public section

namespace QuantumAlg

universe u

/-- A CSLib `TimeM` computation with natural-number cost. -/
abbrev Timed (α : Type u) := Cslib.Algorithms.Lean.TimeM ℕ α

namespace Timed

/-- Attach a trusted cost to a return value. -/
def trusted {α : Type u} (cost : ℕ) (ret : α) : Timed α := ⟨ret, cost⟩

@[simp]
theorem trusted_ret {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).ret = ret := rfl

@[simp]
theorem trusted_time {α : Type u} (cost : ℕ) (ret : α) :
    (trusted cost ret).time = cost := rfl

end Timed

end QuantumAlg
