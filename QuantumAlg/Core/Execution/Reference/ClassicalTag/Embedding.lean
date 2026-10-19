/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Operations
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.State.Coordinates

/-!
# Complete reference-tag blocks through physical framing

The frame's quantum systems remain in the reference and its full store
remains in history. Reordering the reference tag changes no physical system
or stored value. These identities permit nested physical embeddings in the
actual circuit tag bridge.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference Tag : Register}
  {H : Type} [Fintype H]

/-- Put the external tag before the untouched frame within the child's reference. -/
def splitReferenceTag (state : State caller (Tag.prod Reference) H) :
    State localCtx (Tag.prod (placement.frame.register.prod Reference))
      (Store placement.frame × H) :=
  (placement.split state).reindex
    ((Equiv.refl localCtx.register.Index).prodCongr
      (State.referenceTagBasis (ctx := placement.frame)
        (Reference := Reference) (Tag := Tag)))

/-- Undo just the frame/tag reference order before restoring the caller coordinates. -/
def joinReferenceTag
    (state : State localCtx (Tag.prod (placement.frame.register.prod Reference))
      (Store placement.frame × H)) : State caller (Tag.prod Reference) H :=
  placement.join (state.reindex
    ((Equiv.refl localCtx.register.Index).prodCongr
      (State.referenceTagBasis (ctx := placement.frame)
        (Reference := Reference) (Tag := Tag)).symm))

/-- Rejoining retains the exact full block selected by the physical placement. -/
lemma join_referenceTag_entry
    (state : State localCtx (placement.frame.register.prod Reference)
      (Store placement.frame × H)) (label : Store caller × H)
    (row column : (caller.register.prod Reference).Index) :
    ((placement.join state).block label).matrix row column =
      (state.block (placement.record H label)).matrix
        (placement.referenceBasis Reference row) (placement.referenceBasis Reference column) := by
  rw [join, ExecutionState.reindex_block_entry, ExecutionState.coordinate_mapClassical_block]
  rfl

/-- Decoding commutes with the complete physical split and retains the frame store. -/
lemma decodeReferenceTag_split (state : State caller (Tag.prod Reference) H) :
    State.decodeReferenceTag (placement.splitReferenceTag state) =
      (placement.split (State.decodeReferenceTag state)).mapHistory
        (Equiv.prodAssoc (Store placement.frame) H Tag.Index).symm := by
  apply ExecutionState.ext
  rintro ⟨localStore, ⟨frameStore, history⟩, tag⟩
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, frameRow, leftRef⟩
  rcases column with ⟨column, frameColumn, rightRef⟩
  rw [State.decodeReferenceTag_entry, splitReferenceTag,
    ExecutionState.reindex_block_entry, contextEmbedding_split_entry,
    State.mapHistory_equiv_entry, contextEmbedding_split_entry]
  change
    (state.block (placement.store.symm (localStore, frameStore), history)).matrix
        (placement.basis.symm (row, frameRow), (tag, leftRef))
        (placement.basis.symm (column, frameColumn), (tag, rightRef)) =
      ((State.decodeReferenceTag state).block
        (placement.store.symm (localStore, frameStore), (history, tag))).matrix
          (placement.basis.symm (row, frameRow), leftRef)
          (placement.basis.symm (column, frameColumn), rightRef)
  rw [State.decodeReferenceTag_entry]

/-- Rejoining commutes with tag decoding and restores the full original caller store. -/
lemma decodeReferenceTag_join
    (state : State localCtx (Tag.prod (placement.frame.register.prod Reference))
      (Store placement.frame × H)) :
    State.decodeReferenceTag (placement.joinReferenceTag state) =
      placement.join ((State.decodeReferenceTag state).mapHistory
        (Equiv.prodAssoc (Store placement.frame) H Tag.Index)) := by
  apply ExecutionState.ext
  rintro ⟨store, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, leftRef⟩
  rcases column with ⟨column, rightRef⟩
  rw [State.decodeReferenceTag_entry, joinReferenceTag, join_referenceTag_entry,
    ExecutionState.reindex_block_entry, join_referenceTag_entry,
    State.mapHistory_equiv_entry]
  change
    (state.block ((placement.store store).1, ((placement.store store).2, history))).matrix
        ((placement.basis row).1, (tag, ((placement.basis row).2, leftRef)))
        ((placement.basis column).1, (tag, ((placement.basis column).2, rightRef))) =
      ((State.decodeReferenceTag state).block
        ((placement.store store).1, (((placement.store store).2, history), tag))).matrix
          ((placement.basis row).1, ((placement.basis row).2, leftRef))
          ((placement.basis column).1, ((placement.basis column).2, rightRef))
  rw [State.decodeReferenceTag_entry]

end

end QuantumAlg.ContextEmbedding
