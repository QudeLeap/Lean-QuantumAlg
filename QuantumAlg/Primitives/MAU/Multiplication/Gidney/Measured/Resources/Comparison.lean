/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.General

/-!
# Comparison of the independently proved tight and full-domain native allowances

The odd-modulus allowance is smaller in its native Toffoli coordinate. The
full-domain allowance retains the separately counted two-bit CNOT circuit.
No runtime program or actual resource observation is changed by this pure
comparison [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Addition.Gidney.Measured.Instruction

/-- The tight independently stated pool fits the independently stated full-domain pool. -/
lemma multiplicationBudget_le_general (oracles : OracleModel) (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) (width : Nat) :
    multiplicationBudget oracles operations services width ≤
      generalMultiplicationBudget oracles operations services width := by
  unfold multiplicationBudget generalMultiplicationBudget
  apply coordinatePool_mono
  · unfold generalToffoliBound
    by_cases two : width = 2
    · subst width
      decide
    · rw [if_neg two]
      omega
  · unfold generalCnotBound
    by_cases two : width = 2
    · subst width
      decide
    · rw [if_neg two]
  · exact le_rfl
  · exact le_rfl

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
