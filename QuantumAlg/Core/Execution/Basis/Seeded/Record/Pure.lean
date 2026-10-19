/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Record
import all QuantumAlg.Core.Execution.Pure.Point

import all QuantumAlg.Core.Execution.Pure.Selection

/-!
# Pure local observation of every complete seeded record
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

open Execution

attribute [local instance] Classical.decEq

/-- Every complete seeded block keeps its original mass under full local observation. -/
lemma block_pure_fullSelection {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (entry : Store ctx × History) :
    (StatePromise.pure (NormalizedVector.ket
      (ctx.quantumLayout.restrictSelectedBasis Finset.univ seed))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
        (state.block entry)) := by
  apply StatePromise.pureKet_fullSelection_of_localMarginal ctx.quantumLayout
    (state.block entry) seed
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  exact block_entry_zero seed state seeded entry row column reference reference
    (fun supported => different supported.1)

end

end QuantumAlg.Execution.BasisSeeded
