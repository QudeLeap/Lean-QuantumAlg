/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.State
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Supported observations of the existing persistent cells

The complete state coordinates retain each actual cell as history. The
original interpreter cannot change that history, even when its classical
and quantum inputs are correlated and its blocks are subnormalized.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem mapped_positive {A B : Type} [Fintype A] [Fintype B] {R : Register}
    (decision : DecidableEq B) (state : ExecutionState A R) (update : A → B) (value : B) :
    0 < ((@ExecutionState.mapClassical A B _ _ R decision state update).block value).mass ↔
      ∃ original, update original = value ∧ 0 < (state.block original).mass := by
  cases Subsingleton.elim decision (Classical.decEq B)
  exact ExecutionState.mapClassical_block_mass_pos_iff state update value

private theorem mapped_block {A B : Type} [Fintype A] [Fintype B] {R : Register}
    (decision : DecidableEq B) (state : ExecutionState A R) (labels : A ≃ B) (value : B) :
    (@ExecutionState.mapClassical A B _ _ R decision state labels).block value =
      state.block (labels.symm value) := by
  cases Subsingleton.elim decision (Classical.decEq B)
  exact ExecutionState.coordinate_mapClassical_block state labels value

private theorem history_supported {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (Reference : Register) {H D : Type} [Fintype H] [Finite D]
    (state : State pre Reference H) (read : H → D) (wanted : D)
    (holds : ∀ entry, 0 < (state.block entry).mass → read entry.2 = wanted)
    (result : Store post × (H × code.Path))
    (positive : 0 < ((code.execute Reference state).block result).mass) :
    read result.2.1 = wanted := by
  let : Fintype D := Fintype.ofFinite D
  have same : state.mapHistory (fun _ => wanted) = state.mapHistory read := by
    apply ExecutionState.mapClassical_eq_of_support
    intro entry present
    exact congrArg (Prod.mk entry.1) (holds entry present).symm
  have executed := congrArg (code.execute Reference) same
  rw [Circuit.execute_mapHistory, Circuit.execute_mapHistory] at executed
  have mapped : 0 < (((code.execute Reference state).mapHistory
      (fun record => (read record.1, record.2))).block
        (result.1, (read result.2.1, result.2.2))).mass :=
    (mapped_positive _ _ _ _).mpr ⟨result, rfl, positive⟩
  rw [← executed] at mapped
  obtain ⟨original, equality, _⟩ :=
    (mapped_positive _ _ _ _).mp mapped
  exact (congrArg (fun entry => entry.2.1) equality).symm

private def retainedStores (ctx : RuntimeCtx kind) (shape : CShape) :
    Store (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh) ≃
      Store ctx × Store (Circuit.retainedLocalFrame (kind := kind) ctx.canonicalFreshKey shape) :=
  (ContextPermutation.storeEquiv (Circuit.retainedLocalPermutation ctx ctx.canonicalFreshKey
    shape ctx.canonicalFreshKey_fresh)).symm.trans
      (ContextUnion.storeEquiv (Circuit.retainedLocalDisjoint ctx ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh))

private theorem retainedStores_join (shape : CShape)
    (store : Store (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh)) :
    ContextPermutation.store (Circuit.retainedLocalPermutation ctx ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh)
      (ContextUnion.join (Circuit.retainedLocalDisjoint ctx ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh)
        (retainedStores ctx shape store).1 (retainedStores ctx shape store).2) = store :=
  (retainedStores ctx shape).symm_apply_apply store

private theorem retainedStores_read_left (shape : CShape)
    (store : Store (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh))
    {valueShape : CShape} (input : CWriteRef ctx valueShape) :
    (retainedStores ctx shape store).1.read (.storage input.toCStorageRef) =
      store.read (.storage (input.underRetained ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh).toCStorageRef) := by
  let separate := Circuit.retainedLocalDisjoint ctx ctx.canonicalFreshKey shape
    ctx.canonicalFreshKey_fresh
  let same := Circuit.retainedLocalPermutation ctx ctx.canonicalFreshKey shape
    ctx.canonicalFreshKey_fresh
  have refs : ContextPermutation.storage same (ContextUnion.storageLeft separate
      input.toCStorageRef) = (input.underRetained ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh).toCStorageRef :=
    CStorageRef.storageRef_eq_of_key _ _ rfl
  conv_rhs => rw [← retainedStores_join shape store, ← refs,
    ContextPermutation.store_read_storage]
  exact (ContextUnion.contextUnion_read_join_left separate _ _
    (.storage input.toCStorageRef)).symm

private theorem retainedStores_read_head (shape : CShape)
    (store : Store (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh)) :
    (retainedStores ctx shape store).2.cells.1 =
      store.read (.storage (CWriteRef.retainedHead ctx ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh).toCStorageRef) := by
  let separate := Circuit.retainedLocalDisjoint ctx ctx.canonicalFreshKey shape
    ctx.canonicalFreshKey_fresh
  let same := Circuit.retainedLocalPermutation ctx ctx.canonicalFreshKey shape
    ctx.canonicalFreshKey_fresh
  let head := CWriteRef.retainedHead (RuntimeCtx.empty : RuntimeCtx kind)
    ctx.canonicalFreshKey shape (by simp [RuntimeCtx.keys])
  have refs : ContextPermutation.storage same (ContextUnion.storageRight separate
      head.toCStorageRef) = (CWriteRef.retainedHead ctx ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh).toCStorageRef :=
    CStorageRef.storageRef_eq_of_key _ _ rfl
  conv_rhs => rw [← retainedStores_join shape store, ← refs,
    ContextPermutation.store_read_storage]
  exact (ContextUnion.contextUnion_read_join_right separate _ _
    (.storage head.toCStorageRef)).symm

private theorem retainedStores_mass (shape : CShape) {Reference : Register}
    {H : Type} [Fintype H]
    (state : State (ctx.addRetained ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh) Reference H)
    (store : Store (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh))
    (history : H) :
    ((Circuit.underRetainedSplitState ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh
      state).block ((retainedStores ctx shape store).1,
        ((retainedStores ctx shape store).2, history))).mass =
      (state.block (store, history)).mass := by
  unfold Circuit.underRetainedSplitState ContextUnion.splitState Circuit.retainedUnionState
  rw [ExecutionState.reindex_block_mass, ExecutionState.coordinate_mapClassical_block,
    ExecutionState.reindex_block_mass, ExecutionState.coordinate_mapClassical_block]
  congr 2
  exact congrArg (fun original => (original, history))
    ((retainedStores ctx shape).symm_apply_apply store)

private def originalStores (ctx : RuntimeCtx kind) : Store ctx ≃ Store ctx × Unit where
  toFun store := (store, ())
  invFun pair := pair.1
  left_inv _ := rfl
  right_inv pair := by cases pair.2; rfl

private def retainStores {base outer : RuntimeCtx kind} {H : Type}
    (prior : Store outer ≃ Store base × H) (shape : CShape) :
    Store (outer.addRetained outer.canonicalFreshKey shape outer.canonicalFreshKey_fresh) ≃
      Store base × (H × Store (Circuit.retainedLocalFrame (kind := kind)
        outer.canonicalFreshKey shape)) :=
  (retainedStores outer shape).trans
    ((prior.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))

private def RetainedCoordinates.HasStores {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History) : Prop :=
  ∀ {Reference : Register} {H : Type} [Fintype H] (state : State outer Reference H)
    (store : Store outer) (history : H),
    ((coordinates.splitState state).block ((labels store).1, ((labels store).2, history))).mass =
      (state.block (store, history)).mass

private theorem originalStores_mass : (originalCoordinates ctx).HasStores (originalStores ctx) := by
  unfold RetainedCoordinates.HasStores
  intro Reference H _ state store history
  let labels : (Store ctx × H) ≃ (Store ctx × (Unit × H)) :=
    { toFun := fun entry => (entry.1, ((), entry.2))
      invFun := fun entry => (entry.1, entry.2.2)
      left_inv := fun _ => rfl
      right_inv := fun entry => by cases entry.2.1; rfl }
  exact congrArg DensityOperator.mass (mapped_block _ state labels (store, ((), history)))

private theorem retainStores_mass {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer) (labels : Store outer ≃ Store base × prior.History)
    (natural : prior.HasStores labels) (shape : CShape) :
    (retainCoordinates prior shape).HasStores (retainStores labels shape) := by
  unfold RetainedCoordinates.HasStores
  intro Reference H _ state store history
  let split := retainedStores outer shape store
  let association : (Store base × (prior.History ×
      (Store (Circuit.retainedLocalFrame (kind := kind) outer.canonicalFreshKey shape) × H))) ≃
        Store base × ((prior.History × Store (Circuit.retainedLocalFrame (kind := kind)
          outer.canonicalFreshKey shape)) × H) :=
    (Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _).symm
  have aligned :
      (((retainCoordinates prior shape).splitState state).block
        (((retainStores labels shape) store).1,
          ((retainStores labels shape) store).2, history)).mass =
        ((prior.splitState (Circuit.underRetainedSplitState outer.canonicalFreshKey shape
          outer.canonicalFreshKey_fresh state)).block
            ((labels split.1).1, ((labels split.1).2, (split.2, history)))).mass := by
    exact congrArg DensityOperator.mass (mapped_block _
      (prior.splitState (Circuit.underRetainedSplitState outer.canonicalFreshKey shape
        outer.canonicalFreshKey_fresh state)) association
      ((labels split.1).1, (((labels split.1).2, split.2), history)))
  exact aligned.trans ((natural _ split.1 (split.2, history)).trans
    (retainedStores_mass shape state store history))

private def persistentStores (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    Store (persistentCtx ctx width scalarWidth) ≃
      Store ctx × persistentLocalHistory ctx width scalarWidth :=
  let accepted := retainStores (originalStores ctx) .bit
  let selected := retainStores accepted (.unsignedWord scalarWidth)
  let inverse := retainStores selected .bit
  let candidate := retainStores inverse (.unsignedWord scalarWidth)
  let reconstruction := retainStores candidate .bit
  let verified := retainStores reconstruction .bit
  retainStores verified (PointShape width)

private theorem persistentStores_mass (width scalarWidth : Nat) :
    (persistentCoordinates ctx width scalarWidth).HasStores
      (persistentStores ctx width scalarWidth) := by
  have accepted := @retainStores_mass _ _ _ (originalCoordinates ctx) (originalStores ctx)
    (@originalStores_mass kind ctx) .bit
  have selected := @retainStores_mass _ _ _ _ _ accepted (.unsignedWord scalarWidth)
  have inverse := @retainStores_mass _ _ _ _ _ selected .bit
  have candidate := @retainStores_mass _ _ _ _ _ inverse (.unsignedWord scalarWidth)
  have reconstruction := @retainStores_mass _ _ _ _ _ candidate .bit
  have verified := @retainStores_mass _ _ _ _ _ reconstruction .bit
  have scalar := @retainStores_mass _ _ _ _ _ verified (PointShape width)
  exact @scalar

private def savedLatches (width scalarWidth : Nat)
    (history : persistentLocalHistory ctx width scalarWidth) :
    Bool × (CShape.unsignedWord scalarWidth).Value :=
  (history.1.1.1.1.1.1.2.cells.1.toBool, history.1.1.1.1.1.2.cells.1)

private theorem persistentStores_latches (width scalarWidth : Nat)
    (store : Store (persistentCtx ctx width scalarWidth)) :
    savedLatches width scalarWidth (persistentStores ctx width scalarWidth store).2 =
      ((store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
        store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) := by
  apply Prod.ext
  · change _ = (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool
    unfold persistentAccepted
    erw [← retainedStores_read_left, ← retainedStores_read_left, ← retainedStores_read_left,
      ← retainedStores_read_left, ← retainedStores_read_left, ← retainedStores_read_left,
      ← retainedStores_read_head]
    rfl
  · change _ = store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)
    unfold persistentSelected
    erw [← retainedStores_read_left, ← retainedStores_read_left, ← retainedStores_read_left,
      ← retainedStores_read_left, ← retainedStores_read_left, ← retainedStores_read_head]
    rfl

private theorem coordinate_supported {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History)
    (masses : coordinates.HasStores labels) {Reference : Register} {H : Type} [Fintype H]
    (state : State outer Reference H) (predicate : coordinates.History → Prop)
    (holds : ∀ entry, 0 < (state.block entry).mass → predicate (labels entry.1).2)
    (result : Store base × (coordinates.History × H))
    (positive : 0 < ((coordinates.splitState state).block result).mass) :
    predicate result.2.1 := by
  let original := labels.symm (result.1, result.2.1)
  have same : labels original = (result.1, result.2.1) := labels.apply_symm_apply _
  have mass := masses state original result.2.2
  rw [same] at mass
  have input := holds (original, result.2.2) (by simpa only [← mass] using positive)
  simpa only [same] using input

private theorem retained_observation_supported {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History)
    (masses : coordinates.HasStores labels)
    (code : Circuit base base) (extended : Circuit outer outer) (path : code.Path ≃ extended.Path)
    (natural : coordinates.Executes code extended path)
    {D : Type} [Finite D] (read : coordinates.History → D) (wanted : D)
    {Reference : Register} {H : Type} [Fintype H] (state : State outer Reference H)
    (holds : ∀ entry, 0 < (state.block entry).mass → read (labels entry.1).2 = wanted)
    (result : Store outer × (H × extended.Path))
    (positive : 0 < ((extended.execute Reference state).block result).mass) :
    read (labels result.1).2 = wanted := by
  let split := coordinates.splitState state
  have splitHolds : ∀ entry, 0 < (split.block entry).mass → read entry.2.1 = wanted := by
    intro entry present
    exact coordinate_supported coordinates labels masses state
      (fun history => read history = wanted)
      holds entry present
  let saved := labels result.1
  have positiveSplit : 0 < ((coordinates.splitState (extended.execute Reference state)).block
      (saved.1, (saved.2, result.2))).mass :=
    lt_of_lt_of_eq positive (masses (extended.execute Reference state) result.1 result.2).symm
  rw [natural] at positiveSplit
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positiveSplit
  have kept := history_supported code (coordinates.reference Reference) split
    (fun history => read history.1) wanted splitHolds original present
  have savedSame : original.2.1.1 = saved.2 := congrArg (fun entry => entry.2.1) equality
  rw [savedSame] at kept
  exact kept

/-- Actual local sampling preserves any common stored acceptance bit and selected word. -/
theorem underPersistent_latches_supported
    (code : Circuit ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (wanted : Bool × (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) = wanted)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (H × (underPersistent code supported width scalarWidth).Path))
    (positive : 0 < (((underPersistent code supported width scalarWidth).execute
      Reference state).block result).mass) :
    ((result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) =
        wanted := by
  have kept := retained_observation_supported (persistentCoordinates ctx width scalarWidth)
    (persistentStores ctx width scalarWidth) (@persistentStores_mass kind ctx width scalarWidth)
    code (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth)
    (@persistentCoordinates_execute kind ctx code supported width scalarWidth)
    (savedLatches width scalarWidth) wanted state
    (fun original positive => (persistentStores_latches width scalarWidth original.1).trans
      (holds original positive)) result positive
  exact (persistentStores_latches width scalarWidth result.1).symm.trans kept

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
