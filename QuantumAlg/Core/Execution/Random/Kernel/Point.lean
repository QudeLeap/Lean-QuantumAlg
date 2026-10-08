/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Random.Kernel
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Deterministic transitions as exact stochastic state updates

A point distribution retains exactly the block selected by its declared
deterministic result. This equality includes every classical and quantum
correlation and all zero-mass inputs; it does not replace a stochastic native
operation or oracle by a caller-supplied evaluator.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open scoped Classical in
/-- Point-valued kernels coincide with the complete deterministic record update. -/
public theorem kernelChoice_pure {C Outcome : Type} [Fintype C] [Fintype Outcome]
    {R : Register} (state : ExecutionState C R) (choice : C → Outcome) :
    kernelChoice state (fun value => PMF.pure (choice value)) =
      state.mapClassical (fun value => (value, choice value)) := by
  apply ExecutionState.ext
  intro result
  rcases result with ⟨value, outcome⟩
  apply DensityOperator.ext
  rw [kernelChoice_block_matrix]
  change (PMF.pure (choice value) outcome).toReal • (state.block value).matrix =
    ∑ entry, if (entry, choice entry) = (value, outcome) then (state.block entry).matrix else 0
  by_cases same : outcome = choice value
  · subst outcome
    simp [PMF.pure_apply, Prod.mk.injEq, ite_and]
  · simp [PMF.pure_apply, same, Prod.mk.injEq, ite_and, Ne.symm same]

end

end QuantumAlg.Execution
