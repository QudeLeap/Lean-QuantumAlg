/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Context.Embedding.Sequence
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Observation
import all QuantumAlg.Core.Execution.Observe.Reference
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.State.Promise.Reindex
import all QuantumAlg.Core.Execution.Restart

/-!
# A fixed physical reset seed through a classical public frame

The child is executed once by native ContextEmbedding. Every frame cell,
hidden service value, incoming history and actual path survives in the exact
block equation. The frame's quantum coordinates join the arbitrary external
Reference; no product-state assumption, conditioning or normalization occurs.

The final corollary needs only structural facts: the frame has zero quantum
wires and both physical layouts have no borrowed quantum wires. These are
properties of the placement, not assumptions on an admitted caller state.

-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.EmbeddingRestart

noncomputable section

open QuantumAlg QuantumAlg.Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} {localCtx caller : RuntimeCtx
  model.kind}
  {allowAllocation : Bool}

private def executionRecords (placement : ContextEmbedding localCtx caller)
    (code : Circuit model localCtx localCtx false) (History : Type) :
    (Store localCtx × (model.HiddenState ×
      ((Store placement.frame × History) × code.Path))) ≃
    (Store localCtx × (Store placement.frame ×
      (model.HiddenState × (History × code.Path)))) where
  toFun record := (record.1, (record.2.2.1.1,
    (record.2.1, (record.2.2.1.2, record.2.2.2))))
  invFun record := (record.1, (record.2.2.1,
    ((record.2.1, record.2.2.2.1), record.2.2.2.2)))
  left_inv := by rintro ⟨store, hidden, ⟨frame, history⟩, path⟩; rfl
  right_inv := by rintro ⟨store, frame, hidden, history, path⟩; rfl

/-- The complete embedded record is exactly one child record in the full frame/reference basis. -/
lemma execute_block (placement : ContextEmbedding localCtx caller)
    (code : Circuit model localCtx localCtx false) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History))
    (record : Store caller × (model.HiddenState × (History × code.Path))) :
    (((Circuit.embed (allowAllocation := allowAllocation) placement code).execute environment
      Reference state).block record).reindex (placement.referenceBasis Reference) =
      (code.execute environment (placement.frame.register.prod Reference)
        ((placement.split state).mapHistory
          (fun value => (value.2.1, (value.1, value.2.2))))).block
        ((executionRecords placement code History).symm
          (placement.record (model.HiddenState × (History × code.Path)) record)) := by
  let output := code.execute environment (placement.frame.register.prod Reference)
    ((placement.split state).mapHistory (fun value => (value.2.1, (value.1, value.2.2))))
  let actual := (Circuit.embed (allowAllocation := allowAllocation) placement code).execute
    environment Reference state
  have executed : actual = placement.join
      (output.mapClassical (executionRecords placement code History)) := by
    refine (Circuit.execute_embed_history placement code environment Reference state).trans ?_
    apply congrArg placement.join
    unfold State.mapHistory
    exact ExecutionState.executionState_mapClassical_congr_decision output _
      (executionRecords placement code History) (fun _ => rfl) _ _
  have splitEq : placement.split actual =
      output.mapClassical (executionRecords placement code History) :=
    (congrArg (fun value : State caller Reference
      (model.HiddenState × (History × code.Path)) => placement.split value) executed).trans
        (placement.contextEmbedding_split_join _)
  calc
    (actual.block record).reindex (placement.referenceBasis Reference) =
        (placement.split actual).block
          (placement.record (model.HiddenState × (History × code.Path)) record) := by
      apply DensityOperator.ext
      ext row column
      have entry := placement.contextEmbedding_split_entry
        (History := model.HiddenState × (History × code.Path)) actual
        (placement.record (model.HiddenState × (History × code.Path)) record) row column
      simpa only [DensityOperator.reindex_entry, Equiv.symm_apply_apply] using entry.symm
    _ = _ := (congrArg (fun value => value.block
        (placement.record (model.HiddenState × (History × code.Path)) record)) splitEq).trans
      (ExecutionState.coordinate_mapClassical_block output
        (executionRecords placement code History) _)

private lemma observe_reindex (placement : ContextEmbedding localCtx caller)
    (selected : Finset (Fin localCtx.systemCount)) (Reference : Register)
    (state : DensityOperator (caller.register.prod Reference)) :
    (DensityOperator.observeSelection caller.quantumLayout (placement.selection selected)
      Reference state).reindex (placement.selectedBasis selected).symm =
    DensityOperator.observeSelection localCtx.quantumLayout selected
      (placement.frame.register.prod Reference)
      (state.reindex (placement.referenceBasis Reference)) := by
  have joint := congrArg DensityOperator.marginalLeft
    (placement.contextEmbedding_observeSelectionWithReference selected Reference state)
  rw [DensityOperator.marginalLeft_reindex_local] at joint
  refine joint.trans ?_
  apply DensityOperator.ext
  ext row column
  let observed := DensityOperator.observeSelectionWithReference localCtx.quantumLayout selected
    (placement.frame.register.prod Reference)
    (state.reindex (placement.referenceBasis Reference))
  have products := (Register.prodIndexEquiv placement.frame.register Reference).sum_comp
    (fun pair : (placement.frame.register.prod Reference).Index =>
      observed.matrix (row, pair) (column, pair))
  have ordered := (Finset.sum_comm (f := fun reference : Reference.Index =>
    fun frame : placement.frame.register.Index =>
      observed.matrix (row, (frame, reference)) (column, (frame, reference)))).trans
    ((Fintype.sum_prod_type (fun pair : placement.frame.register.Index × Reference.Index =>
      observed.matrix (row, pair) (column, pair))).symm.trans products)
  simpa only [observed, DensityOperator.observeSelection, DensityOperator.marginalLeft_matrix,
    DensityOperator.reindex_entry, ExecutionState.referenceFrameBasis,
    Equiv.coe_fn_symm_mk] using ordered

private lemma reindex_ket {R S : Register} (basis : R.Index ≃ S.Index) (seed : S.Index) :
    (NormalizedVector.ket seed).reindex basis.symm =
      NormalizedVector.ket (basis.symm seed) := by
  apply NormalizedVector.ext
  intro index
  simp only [NormalizedVector.reindex_apply, NormalizedVector.ket_apply, Equiv.symm_symm]
  simp only [← Equiv.eq_symm_apply]

/-- An embedded selected seed holds at every full record, with arbitrary input correlations. -/
lemma selected_seed (placement : ContextEmbedding localCtx caller)
    (code : Circuit model localCtx localCtx false)
    (seed : localCtx.quantumLayout.SelectedBasis localCtx.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt code environment seed)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History))
    (record : Store caller × (model.HiddenState × (History × code.Path))) :
    (StatePromise.pure (NormalizedVector.ket
      (placement.selectedBasis localCtx.borrowedSelectionᶜ seed))).Holds
      (DensityOperator.observeSelection caller.quantumLayout
        (placement.selection localCtx.borrowedSelectionᶜ) Reference
        (((Circuit.embed (allowAllocation := allowAllocation) placement code).execute environment
          Reference state).block record)) := by
  let sourceInput := (placement.split state).mapHistory
    (fun value => (value.2.1, (value.1, value.2.2)))
  let sourceRecord := (executionRecords placement code History).symm
    (placement.record (model.HiddenState × (History × code.Path)) record)
  have original := fixed (placement.frame.register.prod Reference) sourceInput sourceRecord
  have block := execute_block (environment := environment) (allowAllocation := allowAllocation)
    placement code Reference state record
  rw [← block] at original
  have observed := observe_reindex placement localCtx.borrowedSelectionᶜ Reference
    (((Circuit.embed (allowAllocation := allowAllocation) placement code).execute environment
      Reference state).block record)
  apply (StatePromise.statePromise_reindex_holds_iff
    (placement.selectedBasis localCtx.borrowedSelectionᶜ).symm _ _).mp
  simpa only [StatePromise.reindex, reindex_ket, Equiv.symm_apply_apply, observed] using original

private lemma selection_univ (placement : ContextEmbedding localCtx caller)
    (empty : placement.frame.systemCount = 0) : placement.selection Finset.univ = Finset.univ := by
  ext wire
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨original, rfl⟩ := placement.positions.surjective wire
  cases original with
  | inl index => exact Finset.mem_map.mpr ⟨index, Finset.mem_univ _, rfl⟩
  | inr index => have impossible := index.isLt; omega

private lemma selectedBasis_restrict (placement : ContextEmbedding localCtx caller)
    (selected : Finset (Fin localCtx.systemCount))
    (seed : localCtx.register.Index) (frame : placement.frame.register.Index) :
    placement.selectedBasis selected
      (localCtx.quantumLayout.restrictSelectedBasis selected seed) =
    caller.quantumLayout.restrictSelectedBasis (placement.selection selected)
      (placement.basis.symm (seed, frame)) := by
  funext position
  obtain ⟨index, rfl⟩ := (placement.selectedPositions selected).surjective position
  apply Fin.ext
  exact (placement.contextEmbedding_selectedBasis_value selected
    (localCtx.quantumLayout.restrictSelectedBasis selected seed) index).trans
      (placement.contextEmbedding_join_local_value seed frame index.val).symm

/-- A classical frame preserves the same independently specified physical reset label. -/
lemma reinitializedAt (placement : ContextEmbedding localCtx caller)
    (code : Circuit model localCtx localCtx false) (label : localCtx.register.Index)
    (fixed : Circuit.ReinitializedAt code environment
      (localCtx.quantumLayout.restrictSelectedBasis localCtx.borrowedSelectionᶜ label))
    (localOwned : localCtx.borrowedQuantumWires = [])
    (callerOwned : caller.borrowedQuantumWires = [])
    (frameEmpty : placement.frame.systemCount = 0) :
    Circuit.ReinitializedAt (Circuit.embed (allowAllocation := allowAllocation) placement code)
      environment
      (caller.quantumLayout.restrictSelectedBasis caller.borrowedSelectionᶜ
        (placement.basis.symm (label, placement.frame.quantumLayout.zeroLabel))) := by
  have owned : placement.selection localCtx.borrowedSelectionᶜ = caller.borrowedSelectionᶜ := by
    have localAll : localCtx.borrowedSelectionᶜ = Finset.univ := by
      simp [RuntimeCtx.borrowedSelection, localOwned]
    have callerAll : caller.borrowedSelectionᶜ = Finset.univ := by
      simp [RuntimeCtx.borrowedSelection, callerOwned]
    rw [localAll, callerAll]
    exact selection_univ placement frameEmpty
  unfold Circuit.ReinitializedAt
  intro Reference History _ state record
  rw [← owned, ← selectedBasis_restrict]
  exact selected_seed placement code _ fixed Reference state record

end

end ExecutionContract.EmbeddingRestart
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
