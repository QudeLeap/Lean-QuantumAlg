/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Context.Embedding.References
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Circuit.Reference
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Identity placement of the original context-preserving child

The empty placement frame has one classical value and one quantum basis
value. The actual split and join preserve every caller cell and wire. Reference
naturality and mathematical-history naturality therefore identify execution
of the original child through identity placement with its own execution.
This is a law of the existing interpreter, not a new circuit translation.
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ContextEmbedding

variable {kind : ProblemKind}

private instance emptyStoreUnique : Unique (Store (RuntimeCtx.empty (kind := kind))) where
  default := ⟨()⟩
  uniq value := by
    cases value
    rfl

local instance identityFrameStoreUnique (ctx : RuntimeCtx kind) :
    Unique (Store (identity ctx).frame) := by
  change Unique (Store (RuntimeCtx.empty (kind := kind)))
  exact emptyStoreUnique

local instance identityFrameBasisUnique (ctx : RuntimeCtx kind) :
    Unique (identity ctx).frame.register.Index := by
  change Unique (RuntimeCtx.empty (kind := kind)).register.Index
  exact {
    default := fun index => Fin.elim0 index
    uniq := fun value => by
      funext index
      exact Fin.elim0 index }

/-- Identity placement selects the original physical position, not just an equal dimension. -/
lemma identity_position (ctx : RuntimeCtx kind) (index : Fin ctx.systemCount) :
    (identity ctx).position index = index := by
  apply ctx.quantumLayout.identityInjective
  exact congrArg QuantumWire.identity ((identity ctx).contextEmbedding_position_wire index)

/-- Joining identity placement keeps every original local quantum coordinate. -/
lemma identity_join_basis (ctx : RuntimeCtx kind) (localValue : ctx.register.Index)
    (frame : (identity ctx).frame.register.Index) :
    (identity ctx).basis.symm (localValue, frame) = localValue := by
  funext index
  apply Fin.ext
  have actual := (identity ctx).contextEmbedding_join_local_value localValue frame index
  exact (congrArg (fun position : Fin ctx.systemCount =>
    ((identity ctx).basis.symm (localValue, frame) position).val)
      (identity_position ctx index)).symm.trans actual

/-- Joining identity placement keeps every real caller cell. -/
lemma identity_join_store (ctx : RuntimeCtx kind) (localValue : Store ctx)
    (frame : Store (identity ctx).frame) :
    (identity ctx).store.symm (localValue, frame) = localValue := by
  apply Store.store_eq_of_storage_reads
  intro shape ref
  have placed : (identity ctx).input (.storage ref) = CInputRef.storage ref := by
    apply congrArg CInputRef.storage
    apply CStorageRef.storageRef_eq_of_key
    rfl
  have actual := (identity ctx).contextEmbedding_input_read localValue frame (.storage ref)
  rw [placed] at actual
  exact actual

private lemma identity_basis_first (ctx : RuntimeCtx kind) (value : ctx.register.Index) :
    ((identity ctx).basis value).1 = value := by
  exact (identity_join_basis ctx _ _).symm.trans
    ((identity ctx).basis.symm_apply_apply value)

private lemma identity_store_first (ctx : RuntimeCtx kind) (value : Store ctx) :
    ((identity ctx).store value).1 = value := by
  exact (identity_join_store ctx _ _).symm.trans
    ((identity ctx).store.symm_apply_apply value)

/-- The empty actual frame only adds its unique basis label beside the external reference. -/
def identityReference (ctx : RuntimeCtx kind) (Reference : Register) :
    Reference.Index ≃ ((identity ctx).frame.register.prod Reference).Index where
  toFun value := (default, value)
  invFun value := value.2
  left_inv _ := rfl
  right_inv _value := Prod.ext (Subsingleton.elim _ _) rfl

private lemma identity_referenceBasis (ctx : RuntimeCtx kind) (Reference : Register) :
    (identity ctx).referenceBasis Reference =
      (Equiv.refl ctx.register.Index).prodCongr (identityReference ctx Reference) := by
  ext value
  apply Prod.ext
  · exact identity_basis_first ctx value.1
  · exact Prod.ext (Subsingleton.elim _ _) rfl

private lemma identity_record (ctx : RuntimeCtx kind) (History : Type)
    (value : Store ctx × History) :
    (identity ctx).record History value = (value.1, (default, value.2)) := by
  exact Prod.ext (identity_store_first ctx value.1)
    (Prod.ext (Subsingleton.elim _ _) rfl)

/-- The split input to an identity call is only a reference and history coordinate extension. -/
lemma identity_split_service {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ((identity ctx).split state).mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))) =
      (state.mapHistory (fun record => (record.1,
        ((default : Store (identity ctx).frame), record.2)))).reindex
          (S := ctx.register.prod ((identity ctx).frame.register.prod Reference))
          ((Equiv.refl ctx.register.Index).prodCongr (identityReference ctx Reference)) := by
  unfold split
  rw [identity_referenceBasis]
  refine (ExecutionState.reference_map _ inferInstance _ _ _).trans ?_
  apply congrArg (fun result : State ctx Reference
      (model.HiddenState × (Store (identity ctx).frame × History)) => result.reindex
    (S := ctx.register.prod ((identity ctx).frame.register.prod Reference))
    ((Equiv.refl ctx.register.Index).prodCongr (identityReference ctx Reference)))
  refine (ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance) state _ _).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext value
  simp only [Function.comp_apply, identity_record]

end ContextEmbedding

namespace Circuit

attribute [local instance] ContextEmbedding.identityFrameStoreUnique
  ContextEmbedding.identityFrameBasisUnique

/-- Identity placement runs the same original child, with its actual stores, paths and reference. -/
lemma execute_identity_embed {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {allowAllocation : Bool} (body : Circuit model ctx ctx false)
    (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.identity ctx) body).execute environment Reference state =
        body.execute environment Reference state := by
  rw [circuit_execute_embed, ContextEmbedding.identity_split_service,
    execute_referenceReindex, execute_mapHistory]
  refine (congrArg (ContextEmbedding.join (ContextEmbedding.identity ctx)) ?_).trans
    ((ContextEmbedding.identity ctx).contextEmbedding_join_split
      (body.execute environment Reference state))
  unfold ContextEmbedding.split State.mapHistory
  rw [ContextEmbedding.identity_referenceBasis]
  refine (ExecutionState.reference_map _ inferInstance _ _ _).trans ?_
  apply congrArg (fun result : State ctx Reference
      (Store (ContextEmbedding.identity ctx).frame ×
        (model.HiddenState × (History × body.Path))) => result.reindex
    (S := ctx.register.prod ((ContextEmbedding.identity ctx).frame.register.prod Reference))
    ((Equiv.refl ctx.register.Index).prodCongr
      (ContextEmbedding.identityReference ctx Reference)))
  refine (ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance) (body.execute environment Reference state) _ _).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext value
  simp only [Function.comp_apply, ContextEmbedding.identity_record]

end Circuit

end

end QuantumAlg
