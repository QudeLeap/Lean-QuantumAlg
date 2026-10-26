/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context.OwnedLayoutView
public import QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Base.Accounting.Context.OwnedLayoutView
import all QuantumAlg.Core.Execution.Context.Permutation.References
import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Core.Execution.State.Coordinate.Transport

/-!
# Complete state coordinates of an owned-layout view

Only presence markers change their grouping. Every actual classical cell keeps
its value, and quantum coordinates follow equality of the entire ordered wire
list. The inverse restores the original grouping jointly with any reference.
-/

namespace QuantumAlg.OwnedLayoutView

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {original viewed : RuntimeCtx .quantum} (view : OwnedLayoutView original viewed)

/-- The identical classical cell as seen from inside the scope. -/
public def storage {shape : CShape} (ref : CStorageRef original shape) :
    CStorageRef viewed shape :=
  ⟨ref.key, ref.role, ContextPermutation.slotOfMem
    ((view.storage_mem_iff ref.key ref.role shape).mp ref.present)⟩

/-- The identical classical cell as seen after restoring the grouping. -/
public def storageBack {shape : CShape} (ref : CStorageRef viewed shape) :
    CStorageRef original shape :=
  ⟨ref.key, ref.role, ContextPermutation.slotOfMem
    ((view.storage_mem_iff ref.key ref.role shape).mpr ref.present)⟩

private def storeForward (store : Store original) : Store viewed :=
  Store.ofValues viewed fun key role shape present =>
    store.read (.storage ⟨key, role, ContextPermutation.slotOfMem
      ((view.storage_mem_iff key role shape).mpr present)⟩)

private def storeBackward (store : Store viewed) : Store original :=
  Store.ofValues original fun key role shape present =>
    store.read (.storage ⟨key, role, ContextPermutation.slotOfMem
      ((view.storage_mem_iff key role shape).mp present)⟩)

private lemma storeForward_read (store : Store original) {shape : CShape}
    (ref : CStorageRef viewed shape) :
    (storeForward view store).read (.storage ref) =
      store.read (.storage (view.storageBack ref)) := by
  rw [storeForward, Store.read_ofValues]
  congr 2

private lemma storeBackward_read (store : Store viewed) {shape : CShape}
    (ref : CStorageRef original shape) :
    (storeBackward view store).read (.storage ref) =
      store.read (.storage (view.storage ref)) := by
  rw [storeBackward, Store.read_ofValues]
  congr 2

/-- All classical values, with quantum presence markers regrouped bijectively. -/
public def store : Store original ≃ Store viewed where
  toFun := storeForward view
  invFun := storeBackward view
  left_inv state := by
    apply Store.store_eq_of_storage_reads
    intro shape ref
    rw [storeBackward_read, storeForward_read]
    congr 2
    exact CStorageRef.storageRef_eq_of_key _ _ rfl
  right_inv state := by
    apply Store.store_eq_of_storage_reads
    intro shape ref
    rw [storeForward_read, storeBackward_read]
    congr 2
    exact CStorageRef.storageRef_eq_of_key _ _ rfl

/-- Each existing classical value is preserved, including its key and role. -/
public lemma store_read (state : Store original) {shape : CShape}
    (ref : CStorageRef original shape) :
    (view.store state).read (.storage (view.storage ref)) = state.read (.storage ref) := by
  rw [store, Equiv.coe_fn_mk, storeForward_read]
  congr 2
  exact CStorageRef.storageRef_eq_of_key _ _ rfl

/-- Exact coordinate equality of the full quantum register, keeping the reference untouched. -/
public def referenceBasis (Reference : Register) :
    (original.register.prod Reference).Index ≃ (viewed.register.prod Reference).Index :=
  (Equiv.cast (congrArg Register.Index view.register_eq)).prodCongr
    (Equiv.refl Reference.Index)

/-- The actual store and all mathematical history labels remain bijective. -/
public def record (History : Type) :
    (Store original × History) ≃ (Store viewed × History) :=
  view.store.prodCongr (Equiv.refl History)

variable {Reference : Register} {H : Type} [Fintype H]

/-- Expose the scoped grouping while preserving every complete state block. -/
public def split (state : State original Reference H) : State viewed Reference H :=
  (state.mapClassical (view.record H)).reindex (view.referenceBasis Reference)

/-- Restore the original entry grouping after a context-preserving child. -/
public def join (state : State viewed Reference H) : State original Reference H :=
  (state.mapClassical (view.record H).symm).reindex (view.referenceBasis Reference).symm

/-- Restoring a view recovers the identical complete classical-quantum-reference state. -/
public lemma join_split (state : State original Reference H) :
    view.join (view.split state) = state :=
  ExecutionState.coordinate_transport_inverse state (view.record H) (view.referenceBasis Reference)

/-- Every scoped state also survives the reverse coordinate round trip. -/
public lemma split_join (state : State viewed Reference H) :
    view.split (view.join state) = state := by
  simpa only [split, join, Equiv.symm_symm] using ExecutionState.coordinate_transport_inverse state
    (view.record H).symm (view.referenceBasis Reference).symm

/-- Equality of scoped coordinates reflects equality of the complete original states. -/
public lemma split_injective : Function.Injective
    (view.split (Reference := Reference) (H := H)) :=
  Function.LeftInverse.injective view.join_split

/-- No branch weight is changed on entering the view. -/
public lemma split_mass (state : State original Reference H) :
    (view.split state).mass = state.mass :=
  (ExecutionState.reindex_mass _ _).trans (ExecutionState.mapClassical_mass _ _)

/-- No branch weight is changed on restoring the original grouping. -/
public lemma join_mass (state : State viewed Reference H) :
    (view.join state).mass = state.mass :=
  (ExecutionState.reindex_mass _ _).trans (ExecutionState.mapClassical_mass _ _)

/-- Each matrix entry, including arbitrary external-reference coherences, is retained. -/
public lemma split_entry (state : State original Reference H) (label : Store viewed × H)
    (row column : (viewed.register.prod Reference).Index) :
    ((view.split state).block label).matrix row column =
      (state.block ((view.record H).symm label)).matrix
        ((view.referenceBasis Reference).symm row)
        ((view.referenceBasis Reference).symm column) :=
  ExecutionState.coordinate_transport_entry state (view.record H) (view.referenceBasis Reference)
    label row column

end

end QuantumAlg.OwnedLayoutView
