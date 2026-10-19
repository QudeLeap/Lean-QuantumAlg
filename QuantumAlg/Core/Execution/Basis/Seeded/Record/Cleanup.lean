/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Record.Pure
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation

/-!
# Complete-record restart from full actual basis support

The conversion is proved with abstract execution contexts. It does not
normalize a concrete allocation tree or inspect an execution path.
-/

namespace QuantumAlg.Execution.BasisSeeded

open Execution

noncomputable section

private lemma block_pure_allSelection {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seed : ctx.register.Index) (seeded : Holds seed state)
    (selection : Finset (Fin ctx.systemCount)) (all : selection = Finset.univ)
    (entry : Store ctx × History) :
    (StatePromise.pure (NormalizedVector.ket
      (ctx.quantumLayout.restrictSelectedBasis selection seed))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout selection Reference
        (state.block entry)) := by
  cases all
  exact block_pure_fullSelection seed state seeded entry

/-- Full actual support and an owned output bank give the same fixed seed on every record. -/
lemma reinitializedAt_of_holds {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (environment : model.Environment) (seed : post.register.Index)
    (supported : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History)),
      Holds seed (code.execute environment Reference state))
    (noBorrowedQuantum : post.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt code environment
      (post.quantumLayout.restrictSelectedBasis post.borrowedSelectionᶜ seed) := by
  have all : post.borrowedSelectionᶜ = Finset.univ := by
    simp [RuntimeCtx.borrowedSelection, noBorrowedQuantum]
  intro Reference History _ state record
  exact block_pure_allSelection
    (code.execute environment Reference state) seed (supported Reference state)
    post.borrowedSelectionᶜ all record

end

end QuantumAlg.Execution.BasisSeeded
