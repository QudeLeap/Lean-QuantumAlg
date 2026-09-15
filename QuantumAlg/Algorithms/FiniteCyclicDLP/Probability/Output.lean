/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber

/-!
# The original discrete-logarithm residue fits its output word
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The expected candidate encoding is not truncated by the endpoint word
width. -/
theorem expectedOutput_toNat {P : KnownOrderProblem G}
    (input : Probability.SecretInput P) :
    (CShape.wordOfNat (orderWidth P) input.secret.val).toNat =
      input.secret.val := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  rw [CShape.wordOfNat_val, Nat.mod_eq_of_lt]
  exact (ZMod.val_lt input.secret).trans_le (order_le_fourierModulus P)

end

end QuantumAlg.FiniteCyclicDLP.Canonical
