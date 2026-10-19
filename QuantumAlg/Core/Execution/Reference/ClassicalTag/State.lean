/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.ClassicalTag
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Exchange a mathematical history label with an external reference tag

The live register and every store cell retain their original coordinates.
Only the location of a finite spectator label changes. The entry laws keep
all original quantum and external-reference coherences within each tag.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {H : Type} [Fintype H]

/-- Move the tag in front of the live register while retaining the old reference. -/
def referenceTagBasis :
    (ctx.register.prod (Tag.prod Reference)).Index ≃
      (Tag.prod (ctx.register.prod Reference)).Index where
  toFun value := (value.2.1, (value.1, value.2.2))
  invFun value := (value.2.1, (value.1, value.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Read the untouched external tag into mathematical history, without normalization. -/
def decodeReferenceTag (state : State ctx (Tag.prod Reference) H) :
    State ctx Reference (H × Tag.Index) :=
  (ExecutionState.decodeClassicalTag
    (state.reindex
      (referenceTagBasis (ctx := ctx) (Reference := Reference) (Tag := Tag)))).mapClassical
      (Equiv.prodAssoc (Store ctx) H Tag.Index)

/-- Represent a history label by orthogonal blocks of the external tag register. -/
def encodeReferenceTag (state : State ctx Reference (H × Tag.Index)) :
    State ctx (Tag.prod Reference) H :=
  (ExecutionState.encodeClassicalTag
    (state.mapClassical (Equiv.prodAssoc (Store ctx) H Tag.Index).symm)).reindex
      (referenceTagBasis (ctx := ctx) (Reference := Reference) (Tag := Tag)).symm

/-- The tag observation keeps the full total mass. -/
lemma decodeReferenceTag_mass (state : State ctx (Tag.prod Reference) H) :
    (decodeReferenceTag state).mass = state.mass :=
  (ExecutionState.mapClassical_mass _ _).trans
    ((ExecutionState.decodeClassicalTag_mass _).trans
      (ExecutionState.reindex_mass _ _))

/-- Moving a classical spectator to the reference keeps the full total mass. -/
lemma encodeReferenceTag_mass (state : State ctx Reference (H × Tag.Index)) :
    (encodeReferenceTag state).mass = state.mass :=
  (ExecutionState.reindex_mass _ _).trans
    ((ExecutionState.encodeClassicalTag_mass _).trans
      (ExecutionState.mapClassical_mass _ _))

/-- The complete old-reference matrix is the actual diagonal tag block. -/
lemma decodeReferenceTag_entry (state : State ctx (Tag.prod Reference) H)
    (store : Store ctx) (history : H) (tag : Tag.Index)
    (row column : (ctx.register.prod Reference).Index) :
    ((decodeReferenceTag state).block (store, (history, tag))).matrix row column =
      (state.block (store, history)).matrix
        (row.1, (tag, row.2)) (column.1, (tag, column.2)) := by
  rw [decodeReferenceTag, ExecutionState.coordinate_mapClassical_block]
  rw [ExecutionState.decodeClassicalTag_entry, ExecutionState.reindex_block_entry]
  rfl

/-- Each tag block is exactly the original joint store, history and quantum-reference block. -/
lemma encodeReferenceTag_entry (state : State ctx Reference (H × Tag.Index))
    (store : Store ctx) (history : H) (leftTag rightTag : Tag.Index)
    (row column : (ctx.register.prod Reference).Index) :
    ((encodeReferenceTag state).block (store, history)).matrix
        (row.1, (leftTag, row.2)) (column.1, (rightTag, column.2)) =
      if leftTag = rightTag then
        (state.block (store, (history, leftTag))).matrix row column else 0 := by
  rw [encodeReferenceTag, ExecutionState.reindex_block_entry]
  change ((ExecutionState.encodeClassicalTag
      (state.mapClassical (Equiv.prodAssoc (Store ctx) H Tag.Index).symm)).block
      (store, history)).matrix (leftTag, row) (rightTag, column) = _
  rw [ExecutionState.encodeClassicalTag_entry,
    ExecutionState.coordinate_mapClassical_block]
  rfl

/-- Moving a classical history tag to the reference and back restores every full block. -/
lemma decode_encodeReferenceTag (state : State ctx Reference (H × Tag.Index)) :
    decodeReferenceTag (encodeReferenceTag state) = state := by
  apply ExecutionState.ext
  rintro ⟨store, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeReferenceTag_entry, encodeReferenceTag_entry]
  simp

/-- An arbitrary history map retains the separate external tag and every complete store block. -/
lemma decodeReferenceTag_mapHistory {K : Type} [Fintype K]
    (state : State ctx (Tag.prod Reference) H) (update : H → K) :
    decodeReferenceTag (state.mapHistory update) =
      (decodeReferenceTag state).mapHistory (fun history => (update history.1, history.2)) := by
  apply ExecutionState.ext
  rintro ⟨store, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeReferenceTag_entry]
  simp only [mapHistory, ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
    Matrix.ite_apply, Matrix.zero_apply, Fintype.sum_prod_type, Prod.mk.injEq,
    decodeReferenceTag_entry]
  apply Finset.sum_congr rfl
  intro originalStore _
  apply Finset.sum_congr rfl
  intro originalHistory _
  by_cases sameStore : originalStore = store <;>
    by_cases sameHistory : update originalHistory = history <;>
      simp [sameStore, sameHistory]

/-- Changing only the old reference basis commutes with the actual diagonal tag observation. -/
lemma decodeReferenceTag_reference {Other : Register}
    (state : State ctx (Tag.prod Reference) H) (basis : Reference.Index ≃ Other.Index) :
    decodeReferenceTag
        (state.reindex (S := ctx.register.prod (Tag.prod Other))
          ((Equiv.refl ctx.register.Index).prodCongr
            ((Equiv.refl Tag.Index).prodCongr basis))) =
      (decodeReferenceTag state).reindex (S := ctx.register.prod Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis) := by
  apply ExecutionState.ext
  rintro ⟨store, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeReferenceTag_entry, ExecutionState.reindex_block_entry,
    ExecutionState.reindex_block_entry, decodeReferenceTag_entry]
  rfl

end

end QuantumAlg.Execution.State
