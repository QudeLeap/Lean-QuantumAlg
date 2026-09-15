/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Classical grouping of complete supported execution blocks

Deterministic readouts that agree on positive-mass inputs produce the same
complete quantum state. Grouping blocks preserves a common mass-weighted
state promise. These are observations of the existing execution state and
do not introduce an instruction or discard quantum-reference coordinates.
-/

namespace QuantumAlg

noncomputable section

namespace ExecutionState

variable {C D : Type} [Fintype C] [Fintype D] [DecidableEq D] {R : Register}

/-- Agreement on actual positive-mass inputs determines every complete output block. -/
theorem mapClassical_eq_of_support (state : ExecutionState C R) (first second : C → D)
    (agree : ∀ entry, 0 < (state.block entry).mass → first entry = second entry) :
    state.mapClassical first = state.mapClassical second := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [mapClassical_block_matrix, mapClassical_block_matrix]
  apply Finset.sum_congr rfl
  intro entry _present
  by_cases positive : 0 < (state.block entry).mass
  · rw [agree entry positive]
  · have zeroMass := le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    rw [state.block_eq_zero_of_mass_eq_zero entry zeroMass, DensityOperator.zero_matrix]
    simp only [ite_self]

/-- A common normalized target remains the same after any finite classical grouping. -/
theorem mapClassical_mixed (state : ExecutionState C R) (read : C → D)
    (target : DensityOperator R) (normalized : target.IsNormalized)
    (holds : ∀ entry, (StatePromise.mixed target normalized).Holds (state.block entry))
    (result : D) :
    (StatePromise.mixed target normalized).Holds ((state.mapClassical read).block result) := by
  change ((state.mapClassical read).block result).matrix =
    ((state.mapClassical read).block result).mass • target.matrix
  rw [mapClassical_block_matrix, mapClassical_block_mass, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro entry _present
  by_cases selected : read entry = result
  · simp only [selected, if_true]
    exact holds entry
  · simp only [selected, if_false, zero_smul]

end ExecutionState

namespace AlgorithmRun

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Forgetting path records before reading the output leaves every complete output block intact. -/
theorem finalState_readout {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {shape : CShape} (program : AlgorithmRun pre post shape) (Reference : Register)
    (state : ExecutionState (Store pre) (Register.prod pre.register Reference)) :
    (program.finalState Reference state).mapClassical program.output.eval =
      (program.execute Reference state).mapClassical
        (fun record => program.output.eval record.1) := by
  unfold AlgorithmRun.finalState
  exact ExecutionState.executionState_mapClassical_comp
    (program.execute Reference state) Prod.fst program.output.eval

end AlgorithmRun

end

end QuantumAlg
