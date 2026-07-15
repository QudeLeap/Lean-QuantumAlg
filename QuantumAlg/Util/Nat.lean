/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init

/-!
# Natural-number utility lemmas

This module collects quantum-free natural-number helpers used across resource
formulas. These definitions are purely arithmetic adapters, not algorithm
claims.
-/

@[expose] public section

namespace QuantumAlg
namespace Nat

/-- Integer ceiling of a nonnegative rational coefficient `num / den`, encoded
as the standard natural-number upper-bound expression. -/
def ceilDiv (num den : ℕ) : ℕ :=
  (num + den - 1) / den

@[simp]
theorem ceilDiv_eq (num den : ℕ) :
    ceilDiv num den = (num + den - 1) / den :=
  rfl

end Nat
end QuantumAlg
