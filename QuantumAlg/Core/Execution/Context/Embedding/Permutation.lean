/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.State
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Context.Embedding.Sequence

/-!
# Exact native execution in the original permuted entry order

The empty complement contributes no live storage or quantum system. The same
physical-wire values and complete finite store identify its split and join
with identity placement followed by the existing entry permutation. Native
execution therefore preserves the original child, every classical history,
and the arbitrary full reference; no circuit syntax is translated.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma permutation_join_basis {kind : ProblemKind}
    {source destination : RuntimeCtx kind}
    (same : source.entries.Perm destination.entries) (value : source.register.Index)
    (frame : (ContextEmbedding.alongPermutation same).frame.register.Index) :
    (ContextEmbedding.alongPermutation same).basis.symm (value, frame) =
      ContextPermutation.basis same
        ((ContextEmbedding.identity source).basis.symm (value, frame)) := by
  have joined : (ContextEmbedding.alongPermutation same).basis.symm (value, frame) =
      ContextPermutation.basis same value := by
    funext targetIndex
    obtain ⟨index, rfl⟩ := (ContextPermutation.positions same).surjective targetIndex
    apply Fin.ext
    have position : (ContextEmbedding.alongPermutation same).position index =
        ContextPermutation.positions same index := by
      apply destination.quantumLayout.identityInjective
      have embedded :=
        (ContextEmbedding.alongPermutation same).contextEmbedding_position_wire index
      change destination.quantumLayout.wire
        ((ContextEmbedding.alongPermutation same).position index) =
          source.quantumLayout.wire index at embedded
      exact (congrArg QuantumWire.identity embedded).trans
        (congrArg QuantumWire.identity (ContextPermutation.positions_wire same index)).symm
    have original :=
      (ContextEmbedding.alongPermutation same).contextEmbedding_join_local_value value frame index
    rw [position] at original
    exact original.trans (ContextPermutation.basis_value same value index).symm
  exact joined.trans (congrArg (ContextPermutation.basis same)
    (ContextEmbedding.identity_join_basis source value frame).symm)


private lemma permutation_join_store {kind : ProblemKind}
    {source destination : RuntimeCtx kind}
    (same : source.entries.Perm destination.entries) (value : Store source)
    (frame : Store (ContextEmbedding.alongPermutation same).frame) :
    (ContextEmbedding.alongPermutation same).store.symm (value, frame) =
      ContextPermutation.store same
        ((ContextEmbedding.identity source).store.symm (value, frame)) := by
  have joined : (ContextEmbedding.alongPermutation same).store.symm (value, frame) =
      ContextPermutation.store same value := by
    apply Store.store_eq_of_storage_reads
    intro shape ref
    obtain ⟨original, rfl⟩ := ContextPermutation.storage_surjective same ref
    have reference :
        (ContextEmbedding.alongPermutation same).input (.storage original) =
          CInputRef.storage (ContextPermutation.storage same original) := by
      apply congrArg CInputRef.storage
      apply CStorageRef.storageRef_eq_of_key
      rfl
    have read := (ContextEmbedding.alongPermutation same).contextEmbedding_input_read
      value frame (.storage original)
    rw [reference] at read
    exact read.trans (ContextPermutation.store_read_storage same value original).symm
  exact joined.trans (congrArg (ContextPermutation.store same)
    (ContextEmbedding.identity_join_store source value frame).symm)


private lemma permutation_referenceBasis {kind : ProblemKind}
    {source destination : RuntimeCtx kind}
    (same : source.entries.Perm destination.entries) (Reference : Register) :
    (ContextEmbedding.alongPermutation same).referenceBasis Reference =
      (ContextPermutation.referenceBasis same Reference).symm.trans
        ((ContextEmbedding.identity source).referenceBasis Reference) := by
  have inverse : ((ContextEmbedding.alongPermutation same).referenceBasis Reference).symm =
      ((ContextEmbedding.identity source).referenceBasis Reference).symm.trans
        (ContextPermutation.referenceBasis same Reference) := by
    apply Equiv.ext
    rintro ⟨value, frame, reference⟩
    exact Prod.ext (permutation_join_basis same value frame) rfl
  exact congrArg Equiv.symm inverse

private lemma permutation_record {kind : ProblemKind}
    {source destination : RuntimeCtx kind}
    (same : source.entries.Perm destination.entries) (History : Type) :
    (ContextEmbedding.alongPermutation same).record History =
      (ContextPermutation.recordEquiv same History).symm.trans
        ((ContextEmbedding.identity source).record History) := by
  have inverse : ((ContextEmbedding.alongPermutation same).record History).symm =
      ((ContextEmbedding.identity source).record History).symm.trans
        (ContextPermutation.recordEquiv same History) := by
    apply Equiv.ext
    rintro ⟨value, frame, history⟩
    exact Prod.ext (permutation_join_store same value frame) rfl
  exact congrArg Equiv.symm inverse

private lemma embedding_join_entry {kind : ProblemKind}
    {source destination : RuntimeCtx kind}
    (placement : ContextEmbedding source destination) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State source (Register.prod placement.frame.register Reference)
      (Store placement.frame × History)) (label : Store destination × History)
    (row column : (Register.prod destination.register Reference).Index) :
    ((placement.join state).block label).matrix row column =
      (state.block (placement.record History label)).matrix
        (placement.referenceBasis Reference row) (placement.referenceBasis Reference column) := by
  exact ExecutionState.coordinate_transport_entry state (placement.record History).symm
    (placement.referenceBasis Reference).symm label row column

private lemma permutation_join {kind : ProblemKind}
    {source destination : RuntimeCtx kind}
    (same : source.entries.Perm destination.entries) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State source
      (Register.prod (ContextEmbedding.alongPermutation same).frame.register Reference)
      (Store (ContextEmbedding.alongPermutation same).frame × History)) :
    (ContextEmbedding.alongPermutation same).join state =
      ContextPermutation.state same ((ContextEmbedding.identity source).join state) := by
  let placement := ContextEmbedding.alongPermutation same
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  ext row column
  have original := embedding_join_entry (Reference := Reference) placement state label row column
  have transported := ContextPermutation.state_entry same
    ((ContextEmbedding.identity source).join state) label row column
  have identity := embedding_join_entry (Reference := Reference)
    (ContextEmbedding.identity source) state
    ((ContextPermutation.recordEquiv same History).symm label)
    ((ContextPermutation.referenceBasis same Reference).symm row)
    ((ContextPermutation.referenceBasis same Reference).symm column)
  have labels := congrArg
    (fun coordinates : (Store destination × History) ≃
        (Store source × (Store placement.frame × History)) => coordinates label)
    (permutation_record same History)
  have rows := congrArg
    (fun coordinates : (Register.prod destination.register Reference).Index ≃
        (Register.prod source.register (Register.prod placement.frame.register Reference)).Index =>
      coordinates row) (permutation_referenceBasis same Reference)
  have columns := congrArg
    (fun coordinates : (Register.prod destination.register Reference).Index ≃
        (Register.prod source.register (Register.prod placement.frame.register Reference)).Index =>
      coordinates column) (permutation_referenceBasis same Reference)
  have entries := (congrArg (fun stored =>
    (state.block stored).matrix (placement.referenceBasis Reference row)
      (placement.referenceBasis Reference column)) labels).trans
        (congrArg₂ (fun first second =>
          (state.block ((ContextEmbedding.identity source).record History
            ((ContextPermutation.recordEquiv same History).symm label))).matrix
              first second) rows columns)
  exact original.trans (entries.trans (transported.trans identity).symm)


private lemma permutation_split {kind : ProblemKind}
    {source destination : RuntimeCtx kind}
    (same : source.entries.Perm destination.entries) {Reference : Register}
    {History : Type} [Fintype History] (state : State source Reference History) :
    (ContextEmbedding.alongPermutation same).split (ContextPermutation.state same state) =
      (ContextEmbedding.identity source).split state := by
  let placement := ContextEmbedding.alongPermutation same
  have injective : Function.Injective
      (placement.join (Reference := Reference) (History := History)) := by
    intro first second equal
    have inverse := congrArg placement.split equal
    simpa only [ContextEmbedding.contextEmbedding_split_join] using inverse
  have actual := placement.contextEmbedding_join_split (ContextPermutation.state same state)
  have original := (permutation_join (Reference := Reference) same
    ((ContextEmbedding.identity source).split state)).trans
    (congrArg (ContextPermutation.state same)
      ((ContextEmbedding.identity source).contextEmbedding_join_split state))
  exact injective (actual.trans original.symm)

/-- A native permutation placement preserves the complete original child execution. -/
lemma permutation_embed_execute {model : ExecutionModel} {allowAllocation : Bool}
    {source destination : RuntimeCtx model.kind}
    (same : source.entries.Perm destination.entries)
    (code : Circuit model source source false)
    (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State source Reference (model.HiddenState × History)) :
    (Circuit.embed (allowAllocation := allowAllocation) (ContextEmbedding.alongPermutation same)
      code).execute environment Reference (ContextPermutation.state same state) =
        ContextPermutation.state same (code.execute environment Reference state) := by
  let placement := ContextEmbedding.alongPermutation same
  have actual := Circuit.execute_embed_history (allowAllocation := allowAllocation)
    placement code environment Reference (ContextPermutation.state same state)
  have split := permutation_split same state
  have replaced := congrArg
    (fun input : State source (Register.prod placement.frame.register Reference)
        (Store placement.frame × (model.HiddenState × History)) =>
      placement.join
        ((code.execute environment (Register.prod placement.frame.register Reference)
          (input.mapHistory (fun record => (record.2.1, (record.1, record.2.2))))).mapHistory
            (fun record => (record.2.1.1, (record.1, (record.2.1.2, record.2.2)))))) split
  have identity := Circuit.execute_embed_history (allowAllocation := allowAllocation)
    (ContextEmbedding.identity source) code environment Reference state
  have original := identity.symm.trans
    (Circuit.execute_identity_embed (allowAllocation := allowAllocation) code environment
      Reference state)
  exact actual.trans (replaced.trans
    ((permutation_join (Reference := Reference) same _).trans
      (congrArg (ContextPermutation.state same) original)))


end

end QuantumAlg.Circuit
