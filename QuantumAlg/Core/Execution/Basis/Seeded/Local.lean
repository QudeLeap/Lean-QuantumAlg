/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density

/-!
# Local density of an actual normalized basis seed

The support invariant keeps every stored reference block. Summing those
blocks derives a pure local density without assuming independent classical
inputs or a pure external reference.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

/-- A normalized complete seed has exactly the corresponding pure local marginal. -/
theorem basisSeeded_localDensity {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seed : ctx.register.Index)
    (seeded : Holds seed state) (normalized : state.IsNormalized) :
    state.quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket (R := ctx.register) seed) := by
  have pure : (StatePromise.pure (NormalizedVector.ket (R := ctx.register) seed)).Holds
      state.quantumMarginal.marginalLeft := by
    apply StatePromise.statePromise_pureKet_of_row_support
    intro row different column
    rw [DensityOperator.marginalLeft_matrix]
    apply Finset.sum_eq_zero
    intro reference _
    rw [← ExecutionState.mapClassical_quantumMarginal state (fun record => record.1)]
    simp only [ExecutionState.quantumMarginal, Matrix.sum_apply]
    change (∑ stored : Store ctx,
      ((state.mapClassical (fun record => record.1)).block stored).matrix
        (row, reference) (column, reference)) = 0
    apply Finset.sum_eq_zero
    intro stored _
    rw [store_matrix, seeded]
    simp only [different, false_and, if_false]
  have mass : state.quantumMarginal.marginalLeft.mass = 1 := by
    rw [DensityOperator.marginalLeft_mass, ExecutionState.quantumMarginal_mass]
    exact normalized
  change state.quantumMarginal.marginalLeft.matrix =
    state.quantumMarginal.marginalLeft.mass •
      (DensityOperator.ofPure (NormalizedVector.ket (R := ctx.register) seed)).matrix at pure
  rw [mass, one_smul] at pure
  exact DensityOperator.ext pure

end

end QuantumAlg.Execution.BasisSeeded
