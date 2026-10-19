/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Branch

/-!
# Exact classical selection through actual branch sums

Selecting an earlier classical label commutes with selecting a later stored
value. It also distributes over the interpreter's admissible branch sum,
retaining every full quantum/reference block [dW19, qcnotes.tex:5381,5409].
-/

namespace QuantumAlg.ExecutionState

noncomputable section

open scoped BigOperators

variable {C D E I : Type} [Fintype C] {R : Register}

/-- Two actual classical selections retain exactly the intersection of their full blocks. -/
lemma selectClassical_comm [DecidableEq D] [DecidableEq E]
    (state : ExecutionState C R) (first : C → D) (second : C → E)
    (left : D) (right : E) :
    (state.selectClassical first left).selectClassical second right =
      (state.selectClassical second right).selectClassical first left := by
  apply ExecutionState.ext
  intro label
  by_cases firstSelected : first label = left <;>
    by_cases secondSelected : second label = right <;>
    simp only [selectClassical_block, firstSelected, secondSelected, if_true, if_false]

/-- Selection distributes over every complete density block in an admissible branch sum. -/
lemma selectClassical_finiteSum_block_matrix [Fintype I] [DecidableEq D]
    (states : I → ExecutionState C R) (total : ∑ index, (states index).mass ≤ 1)
    (read : C → D) (selected : D) (label : C) :
    (((finiteSum states total).selectClassical read selected).block label).matrix =
      ∑ index, (((states index).selectClassical read selected).block label).matrix := by
  by_cases active : read label = selected
  · simp only [selectClassical_block, active, if_true, finiteSum_block_matrix]
  · simp only [selectClassical_block, active, if_false, DensityOperator.zero_matrix,
      Finset.sum_const_zero]

end

end QuantumAlg.ExecutionState
