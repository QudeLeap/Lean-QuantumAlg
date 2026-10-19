/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Measured.FeedForward

/-!
# Complete earlier-history fibers under actual sequential execution

The actual interpreter reassociates its two newly generated paths. An arbitrary
predicate on the original history is transported through that reassociation,
while the complete final Store and quantum/reference matrix remain selected.
These are mathematical matrix observations of the same physical Circuit.
No earlier-history predicate is discarded, and no physical operation is added.

This generic composition bridge does not supply the corresponding one-stage
instrument law or its legal-path expansion. Those remain separate obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace HistoryMatrices

noncomputable section

open QuantumAlg QuantumAlg.Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Arbitrary classical fiber sums preserve the selected complete quantum matrix. -/
private lemma mapped_filter_matrix {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (state : ExecutionState C R) (labels : C → D) (predicate : D → Prop)
    {mapDecision : DecidableEq D} {outputDecision : DecidablePred predicate}
    {inputDecision : DecidablePred (fun original => predicate (labels original))} :
    (@ExecutionState.filterClassical D _ R
      (@ExecutionState.mapClassical C D _ _ R mapDecision state labels)
      predicate outputDecision).quantumMarginal.matrix =
      (@ExecutionState.filterClassical C _ R state
        (fun original => predicate (labels original)) inputDecision).quantumMarginal.matrix := by
  cases Subsingleton.elim mapDecision (Classical.decEq D)
  cases Subsingleton.elim outputDecision
    (fun value => Classical.propDecidable (predicate value))
  cases Subsingleton.elim inputDecision
    (fun value => Classical.propDecidable (predicate (labels value)))
  ext row column
  rw [ExecutionState.filterClassical_matrix_weighted,
    ExecutionState.weightedMatrixEntry_mapClassical,
    ExecutionState.filterClassical_matrix_weighted]

/-- Reassociation keeps every complete final Store and every selected original-history fiber. -/
lemma seq_store_history_matrix {model : ExecutionModel}
    {environment : model.Environment} {allowAllocation : Bool}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle allowAllocation)
    (second : Circuit model middle post allowAllocation)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History))
    (stored : Store post) (predicate : History → Prop) :
    (((first.seq second).execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ((second.execute environment Reference (first.execute environment Reference
        state)).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1.1)).quantumMarginal.matrix := by
  let nested : State post Reference
      (model.HiddenState × ((History × first.Path) × second.Path)) :=
    second.execute environment Reference (first.execute environment Reference state)
  let update : Store post × (model.HiddenState × ((History × first.Path) × second.Path)) →
      Store post × (model.HiddenState × (History × (first.seq second).Path)) :=
    fun record => (record.1,
      (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))
  let observe (result : State post Reference
      (model.HiddenState × (History × (first.seq second).Path))) :=
    (result.filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix
  have executed := congrArg observe (Circuit.execute_seq environment first second state)
  have regrouped :
      State.mapHistory (K := model.HiddenState × (History × (first.seq second).Path)) nested
        (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) =
        @ExecutionState.mapClassical
          (Store post × (model.HiddenState × ((History × first.Path) × second.Path)))
          (Store post × (model.HiddenState × (History × (first.seq second).Path))) _ _
          (post.register.prod Reference)
          (Classical.decEq
            (Store post × (model.HiddenState × (History × (first.seq second).Path))))
          nested update :=
    ExecutionState.executionState_mapClassical_congr _ rfl
  have filtered :
      observe (@ExecutionState.mapClassical
        (Store post × (model.HiddenState × ((History × first.Path) × second.Path)))
        (Store post × (model.HiddenState × (History × (first.seq second).Path))) _ _
        (post.register.prod Reference)
        (Classical.decEq
          (Store post × (model.HiddenState × (History × (first.seq second).Path))))
        nested update) =
        (nested.filterClassical
          (fun record => record.1 = stored ∧ predicate record.2.2.1.1)).quantumMarginal.matrix :=
    mapped_filter_matrix
      (C := Store post × (model.HiddenState × ((History × first.Path) × second.Path)))
      (D := Store post × (model.HiddenState × (History × (first.seq second).Path)))
      (R := post.register.prod Reference) nested update
      (fun record => record.1 = stored ∧ predicate record.2.2.1)
      (mapDecision := Classical.decEq
        (Store post × (model.HiddenState × (History × (first.seq second).Path))))
  exact executed.trans ((congrArg observe regrouped).trans filtered)

/-- The actual identity instruction retains the same full Store and earlier-history selection. -/
lemma id_store_history_matrix {model : ExecutionModel}
    {environment : model.Environment} {allowAllocation : Bool}
    {ctx : RuntimeCtx model.kind} {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (stored : Store ctx) (predicate : History → Prop) :
    (((Circuit.id (allowAllocation := allowAllocation) (model := model) ctx).execute environment
      Reference state).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      (state.filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2)).quantumMarginal.matrix := by
  rw [Circuit.execute_id]
  exact mapped_filter_matrix state
    (fun record => (record.1, (record.2.1, (record.2.2, ()))))
    (fun record => record.1 = stored ∧ predicate record.2.2.1)
    (mapDecision := inferInstance)

end

end HistoryMatrices
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
