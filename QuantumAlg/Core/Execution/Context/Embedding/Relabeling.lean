/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.State
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Context.Embedding.Sequence

/-!
# Exact native execution in injectively relabeled coordinates

The empty complement contributes no live storage or quantum system. Each
physical wire and complete finite store follows the prescribed injective maps.
The split and join agree with identity placement followed by this coordinate
change, preserving the original child, every history and the full reference.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma relabeling_join_basis {kind : ProblemKind}
    {source : RuntimeCtx kind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (value : source.register.Index)
    (frame : (ContextEmbedding.alongRelabeling source keys physical).frame.register.Index) :
    (ContextEmbedding.alongRelabeling source keys physical).basis.symm (value, frame) =
      ContextRelabeling.basis source keys physical
        ((ContextEmbedding.identity source).basis.symm (value, frame)) := by
  have joined : (ContextEmbedding.alongRelabeling source keys physical).basis.symm (value, frame) =
      ContextRelabeling.basis source keys physical value := by
    funext targetIndex
    obtain ⟨index, rfl⟩ := (ContextRelabeling.positions source keys physical).surjective targetIndex
    apply Fin.ext
    have position : (ContextEmbedding.alongRelabeling source keys physical).position index =
        ContextRelabeling.positions source keys physical index := by
      apply (source.relabel keys physical).quantumLayout.identityInjective
      have embedded :=
        (ContextEmbedding.alongRelabeling source keys physical).contextEmbedding_position_wire index
      exact (congrArg QuantumWire.identity embedded).trans
        (congrArg QuantumWire.identity
          (ContextRelabeling.positions_wire source keys physical index)).symm
    have original :=
      (ContextEmbedding.alongRelabeling source keys physical).contextEmbedding_join_local_value
        value frame index
    rw [position] at original
    exact original.trans (ContextRelabeling.basis_value source keys physical value index).symm
  exact joined.trans (congrArg (ContextRelabeling.basis source keys physical)
    (ContextEmbedding.identity_join_basis source value frame).symm)


private lemma relabeling_join_store {kind : ProblemKind}
    {source : RuntimeCtx kind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) (value : Store source)
    (frame : Store (ContextEmbedding.alongRelabeling source keys physical).frame) :
    (ContextEmbedding.alongRelabeling source keys physical).store.symm (value, frame) =
      ContextRelabeling.storeEquiv keys physical source
        ((ContextEmbedding.identity source).store.symm (value, frame)) := by
  have joined : (ContextEmbedding.alongRelabeling source keys physical).store.symm (value, frame) =
      ContextRelabeling.storeEquiv keys physical source value := by
    apply (ContextRelabeling.storeEquiv keys physical source).symm.injective
    rw [(ContextRelabeling.storeEquiv keys physical source).symm_apply_apply]
    apply Store.store_eq_of_storage_reads
    intro shape ref
    have readback := ContextRelabeling.store_read_storage keys physical
      ((ContextRelabeling.storeEquiv keys physical source).symm
        ((ContextEmbedding.alongRelabeling source keys physical).store.symm (value, frame))) ref
    rw [(ContextRelabeling.storeEquiv keys physical source).apply_symm_apply] at readback
    have reference :
        (ContextEmbedding.alongRelabeling source keys physical).input (.storage ref) =
          CInputRef.storage (ContextRelabeling.storage keys physical ref) := by
      apply congrArg CInputRef.storage
      apply CStorageRef.storageRef_eq_of_key
      rfl
    have read :=
      (ContextEmbedding.alongRelabeling source keys physical).contextEmbedding_input_read
        value frame (.storage ref)
    rw [reference] at read
    exact readback.symm.trans read
  exact joined.trans (congrArg (ContextRelabeling.storeEquiv keys physical source)
    (ContextEmbedding.identity_join_store source value frame).symm)


private lemma relabeling_referenceBasis {kind : ProblemKind}
    {source : RuntimeCtx kind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) (Reference : Register) :
    (ContextEmbedding.alongRelabeling source keys physical).referenceBasis Reference =
      (ContextRelabeling.referenceBasis (source := source) keys physical Reference).symm.trans
        ((ContextEmbedding.identity source).referenceBasis Reference) := by
  have inverse :
      ((ContextEmbedding.alongRelabeling source keys physical).referenceBasis Reference).symm =
        ((ContextEmbedding.identity source).referenceBasis Reference).symm.trans
          (ContextRelabeling.referenceBasis (source := source) keys physical Reference) := by
    apply Equiv.ext
    rintro ⟨value, frame, reference⟩
    exact Prod.ext (relabeling_join_basis keys physical value frame) rfl
  exact congrArg Equiv.symm inverse

private lemma relabeling_record {kind : ProblemKind}
    {source : RuntimeCtx kind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) (History : Type) :
    (ContextEmbedding.alongRelabeling source keys physical).record History =
      (ContextRelabeling.recordEquiv (source := source) keys physical History).symm.trans
        ((ContextEmbedding.identity source).record History) := by
  have inverse :
      ((ContextEmbedding.alongRelabeling source keys physical).record History).symm =
        ((ContextEmbedding.identity source).record History).symm.trans
          (ContextRelabeling.recordEquiv (source := source) keys physical History) := by
    apply Equiv.ext
    rintro ⟨value, frame, history⟩
    exact Prod.ext (relabeling_join_store keys physical value frame) rfl
  exact congrArg Equiv.symm inverse

private lemma relabeling_join_entry {kind : ProblemKind}
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

private lemma relabeling_join {kind : ProblemKind}
    {source : RuntimeCtx kind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State source
      (Register.prod
        (ContextEmbedding.alongRelabeling source keys physical).frame.register Reference)
      (Store (ContextEmbedding.alongRelabeling source keys physical).frame × History)) :
    (ContextEmbedding.alongRelabeling source keys physical).join state =
      ContextRelabeling.state keys physical ((ContextEmbedding.identity source).join state) := by
  let placement := ContextEmbedding.alongRelabeling source keys physical
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  ext row column
  have original := relabeling_join_entry (Reference := Reference) placement state label row column
  have transported := ContextRelabeling.state_entry keys physical
    ((ContextEmbedding.identity source).join state) label row column
  have identity := relabeling_join_entry (Reference := Reference)
    (ContextEmbedding.identity source) state
    ((ContextRelabeling.recordEquiv keys physical History).symm label)
    ((ContextRelabeling.referenceBasis keys physical Reference).symm row)
    ((ContextRelabeling.referenceBasis keys physical Reference).symm column)
  have labels := congrArg
    (fun coordinates : (Store (source.relabel keys physical) × History) ≃
        (Store source × (Store placement.frame × History)) => coordinates label)
    (relabeling_record keys physical History)
  have rows := congrArg
    (fun coordinates : (Register.prod (source.relabel keys physical).register Reference).Index ≃
        (Register.prod source.register (Register.prod placement.frame.register Reference)).Index =>
      coordinates row) (relabeling_referenceBasis keys physical Reference)
  have columns := congrArg
    (fun coordinates : (Register.prod (source.relabel keys physical).register Reference).Index ≃
        (Register.prod source.register (Register.prod placement.frame.register Reference)).Index =>
      coordinates column) (relabeling_referenceBasis keys physical Reference)
  have entries := (congrArg (fun stored =>
    (state.block stored).matrix (placement.referenceBasis Reference row)
      (placement.referenceBasis Reference column)) labels).trans
        (congrArg₂ (fun first second =>
          (state.block ((ContextEmbedding.identity source).record History
            ((ContextRelabeling.recordEquiv keys physical History).symm label))).matrix
              first second) rows columns)
  exact original.trans (entries.trans (transported.trans identity).symm)


private lemma relabeling_split {kind : ProblemKind}
    {source : RuntimeCtx kind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) {Reference : Register}
    {History : Type} [Fintype History] (state : State source Reference History) :
    (ContextEmbedding.alongRelabeling source keys physical).split
        (ContextRelabeling.state keys physical state) =
      (ContextEmbedding.identity source).split state := by
  let placement := ContextEmbedding.alongRelabeling source keys physical
  have injective : Function.Injective
      (placement.join (Reference := Reference) (History := History)) := by
    intro first second equal
    have inverse := congrArg placement.split equal
    simpa only [ContextEmbedding.contextEmbedding_split_join] using inverse
  have actual := placement.contextEmbedding_join_split
    (ContextRelabeling.state keys physical state)
  have original := (relabeling_join (Reference := Reference) keys physical
    ((ContextEmbedding.identity source).split state)).trans
    (congrArg (ContextRelabeling.state keys physical)
      ((ContextEmbedding.identity source).contextEmbedding_join_split state))
  exact injective (actual.trans original.symm)

/-- Native relabeling preserves the complete child execution in the prescribed coordinates. -/
lemma relabeling_embed_execute {model : ExecutionModel} {allowAllocation : Bool}
    {source : RuntimeCtx model.kind}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (code : Circuit model source source false)
    (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State source Reference (model.HiddenState × History)) :
    (Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.alongRelabeling source keys physical) code).execute environment Reference
        (ContextRelabeling.state keys physical state) =
      ContextRelabeling.state keys physical (code.execute environment Reference state) := by
  let placement := ContextEmbedding.alongRelabeling source keys physical
  have actual := Circuit.execute_embed_history (allowAllocation := allowAllocation)
    placement code environment Reference (ContextRelabeling.state keys physical state)
  have split := relabeling_split keys physical state
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
    ((relabeling_join (Reference := Reference) keys physical _).trans
      (congrArg (ContextRelabeling.state keys physical) original)))


end

end QuantumAlg.Circuit
