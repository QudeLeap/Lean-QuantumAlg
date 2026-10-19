/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Lean.Elab.Tactic.Omega

/-!
# Shared original-bank classical storage arithmetic

The native and declared-query executions use the same sixteen sample slots
and selector workspace. This scalar identity does not import either execution.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.SpaceArithmetic

/-- The independent classical bit allowance of the original shared bank. -/
lemma bank_classical_arithmetic (M d A : Nat) :
    d + d * 1 + 0 + (1 + M + 16 * d + (18 * M + 1)) +
        ((9 * M + 14).max 1).max (A + (8 * M + 2)) + (1 + M + (M + 1)) =
      21 * M + 18 * d + 4 + max (9 * M + 14) (A + 8 * M + 2) := by
  change d + d * 1 + 0 + (1 + M + 16 * d + (18 * M + 1)) +
    max (max (9 * M + 14) 1) (A + (8 * M + 2)) + (1 + M + (M + 1)) = _
  rw [Nat.max_eq_left (by omega : 1 ≤ 9 * M + 14)]
  rw [show A + (8 * M + 2) = A + 8 * M + 2 by omega]
  omega

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.SpaceArithmetic
