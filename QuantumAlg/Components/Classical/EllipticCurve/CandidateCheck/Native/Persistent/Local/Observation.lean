/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.State
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.Classical.BasisSupport
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

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

/-- Any finite read of the unchanged input history stays fixed on supported
records of an actual circuit, including correlated quantum-reference blocks. -/
theorem history_supported {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (Reference : Register)
    {H D : Type} [Fintype H] [Finite D]
    (state : State pre Reference (model.HiddenState × H)) (read : H → D) (wanted : D)
    (holds : ∀ entry, 0 < (state.block entry).mass → read entry.2.2 = wanted)
    (result : Store post × (model.HiddenState × (H × code.Path)))
    (positive : 0 < ((code.execute Reference state).block result).mass) :
    read result.2.2.1 = wanted := by
  let : Fintype D := Fintype.ofFinite D
  have same : state.mapHistory (fun record => (record.1, wanted)) =
      state.mapHistory (fun record => (record.1, read record.2)) := by
    have firstBridge : state.mapHistory (fun record => (record.1, wanted)) =
        state.mapClassical (fun entry => (entry.1, (entry.2.1, wanted))) := by
      unfold State.mapHistory
      exact ExecutionState.executionState_mapClassical_congr_decision state
        _ _ (fun _ => rfl) _ _
    have secondBridge : state.mapHistory (fun record => (record.1, read record.2)) =
        state.mapClassical (fun entry => (entry.1, (entry.2.1, read entry.2.2))) := by
      unfold State.mapHistory
      exact ExecutionState.executionState_mapClassical_congr_decision state
        _ _ (fun _ => rfl) _ _
    have core := ExecutionState.mapClassical_eq_of_support state
      (fun entry => (entry.1, (entry.2.1, wanted)))
      (fun entry => (entry.1, (entry.2.1, read entry.2.2)))
      (by
        intro entry present
        exact congrArg (Prod.mk entry.1)
          (Prod.ext rfl (holds entry present).symm))
    exact firstBridge.trans (core.trans secondBridge.symm)
  have executed := congrArg (code.execute Reference) same
  rw [Circuit.execute_mapHistory code Reference state (fun _ : H => wanted),
    Circuit.execute_mapHistory code Reference state read] at executed
  have mapped : 0 < (((code.execute Reference state).mapHistory
      (fun record => (record.1, (read record.2.1, record.2.2)))).block
        (result.1, (result.2.1, (read result.2.2.1, result.2.2.2)))).mass :=
    (mapped_positive _ _ _ _).mpr ⟨result, rfl, positive⟩
  rw [← executed] at mapped
  obtain ⟨original, equality, _⟩ :=
    (mapped_positive _ _ _ _).mp mapped
  exact (congrArg (fun entry => entry.2.2.1) equality).symm

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
    {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh) Reference (Hidden × H))
    (store : Store (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh))
    (hidden : Hidden) (history : H) :
    ((Circuit.underRetainedSplitState ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh
      state).block ((retainedStores ctx shape store).1,
        (hidden, ((retainedStores ctx shape store).2, history)))).mass =
      (state.block (store, (hidden, history))).mass := by
  unfold Circuit.underRetainedSplitState ContextUnion.splitServiceState
  rw [show (((ContextUnion.splitState ctx
      (Circuit.retainedLocalFrame (kind := kind) ctx.canonicalFreshKey shape)
      (Circuit.retainedLocalDisjoint ctx ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh)
      (Circuit.retainedUnionState ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh state)).mapHistory
        (ContextUnion.serviceHistory
          (Circuit.retainedLocalFrame (kind := kind) ctx.canonicalFreshKey shape)
          Hidden H)).block
        ((retainedStores ctx shape store).1,
          (hidden, ((retainedStores ctx shape store).2, history)))).mass =
      ((ContextUnion.splitState ctx
        (Circuit.retainedLocalFrame (kind := kind) ctx.canonicalFreshKey shape)
        (Circuit.retainedLocalDisjoint ctx ctx.canonicalFreshKey shape
          ctx.canonicalFreshKey_fresh)
        (Circuit.retainedUnionState ctx.canonicalFreshKey shape
          ctx.canonicalFreshKey_fresh state)).block
          ((retainedStores ctx shape store).1,
            ((retainedStores ctx shape store).2, (hidden, history)))).mass from
    congrArg DensityOperator.mass (mapped_block _ _
      ((Equiv.refl _).prodCongr
        (ContextUnion.serviceHistory
          (Circuit.retainedLocalFrame (kind := kind) ctx.canonicalFreshKey shape)
          Hidden H)) _)]
  unfold ContextUnion.splitState Circuit.retainedUnionState
  rw [ExecutionState.reindex_block_mass]
  simp only [ExecutionState.coordinate_mapClassical_block]
  rw [ExecutionState.reindex_block_mass]
  simp only [ExecutionState.coordinate_mapClassical_block]
  congr 2
  exact congrArg (fun original => (original, (hidden, history)))
    ((retainedStores ctx shape).symm_apply_apply store)

/-- Exact block transport keeps every quantum and external-reference matrix
entry, not just the probability mass used by event bounds. -/
private theorem retainedStores_block (shape : CShape) {Reference : Register}
    {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (ctx.addRetained ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh) Reference (Hidden × H))
    (store : Store (ctx.addRetained ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh)) (hidden : Hidden) (history : H) :
    (Circuit.underRetainedSplitState ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh state).block
        ((retainedStores ctx shape store).1,
          (hidden, ((retainedStores ctx shape store).2, history))) =
      (state.block (store, (hidden, history))).reindex
        (Circuit.underRetainedSplitBasis ctx.canonicalFreshKey shape
          ctx.canonicalFreshKey_fresh Reference) := by
  apply DensityOperator.ext
  ext row column
  rw [Circuit.underRetainedSplitState_entry, DensityOperator.reindex_entry]
  have sameRecord :
      (Circuit.underRetainedSplitRecords ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh Hidden H).symm
          ((retainedStores ctx shape store).1,
            (hidden, ((retainedStores ctx shape store).2, history))) =
        (store, (hidden, history)) := by
    simp [Circuit.underRetainedSplitRecords, retainedStores,
      ContextUnion.serviceHistory, ContextPermutation.recordEquiv,
      ContextUnion.recordEquiv]
  rw [sameRecord]

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
  ∀ {Reference : Register} {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State outer Reference (Hidden × H))
    (store : Store outer) (hidden : Hidden) (history : H),
    ((coordinates.splitState state).block
      ((labels store).1, (hidden, ((labels store).2, history)))).mass =
      (state.block (store, (hidden, history))).mass

private theorem originalStores_mass : (originalCoordinates ctx).HasStores (originalStores ctx) := by
  unfold RetainedCoordinates.HasStores
  intro Reference Hidden H _ _ state store hidden history
  let labels : (Store ctx × (Hidden × H)) ≃ (Store ctx × (Hidden × (Unit × H))) :=
    { toFun := fun entry => (entry.1, (entry.2.1, ((), entry.2.2)))
      invFun := fun entry => (entry.1, (entry.2.1, entry.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun entry => by cases entry.2.2.1; rfl }
  exact congrArg DensityOperator.mass
    (mapped_block _ state labels (store, (hidden, ((), history))))

private theorem retainStores_mass {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer) (labels : Store outer ≃ Store base × prior.History)
    (natural : prior.HasStores labels) (shape : CShape) :
    (retainCoordinates prior shape).HasStores (retainStores labels shape) := by
  unfold RetainedCoordinates.HasStores
  intro Reference Hidden H _ _ state store hidden history
  let split := retainedStores outer shape store
  let association : (Store base × (Hidden × (prior.History ×
      (Store (Circuit.retainedLocalFrame (kind := kind) outer.canonicalFreshKey shape) × H)))) ≃
        Store base × (Hidden × ((prior.History × Store
          (Circuit.retainedLocalFrame (kind := kind)
            outer.canonicalFreshKey shape)) × H)) :=
    (Equiv.refl _).prodCongr
      ((Equiv.refl Hidden).prodCongr (Equiv.prodAssoc _ _ _).symm)
  have aligned :
      (((retainCoordinates prior shape).splitState state).block
        (((retainStores labels shape) store).1,
          (hidden, ((retainStores labels shape) store).2, history))).mass =
        ((prior.splitState (Circuit.underRetainedSplitState outer.canonicalFreshKey shape
          outer.canonicalFreshKey_fresh state)).block
            ((labels split.1).1,
              (hidden, ((labels split.1).2, (split.2, history))))).mass := by
    exact congrArg DensityOperator.mass (mapped_block _
      (prior.splitState (Circuit.underRetainedSplitState outer.canonicalFreshKey shape
        outer.canonicalFreshKey_fresh state)) association
      ((labels split.1).1, (hidden, (((labels split.1).2, split.2), history))))
  exact aligned.trans ((natural _ split.1 hidden (split.2, history)).trans
    (retainedStores_mass shape state store hidden history))

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

private def originalBasis (base : RuntimeCtx kind) (Reference : Register) :
    (base.register.prod Reference).Index ≃
      (base.register.prod ((originalCoordinates base).reference Reference)).Index :=
  Equiv.refl _

private def retainBasis {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer)
    (basis : (Reference : Register) →
      (outer.register.prod Reference).Index ≃
        (base.register.prod (prior.reference Reference)).Index)
    (shape : CShape) (Reference : Register) :
    ((outer.addRetained outer.canonicalFreshKey shape outer.canonicalFreshKey_fresh).register.prod
      Reference).Index ≃
    (base.register.prod ((retainCoordinates prior shape).reference Reference)).Index :=
  (Circuit.underRetainedSplitBasis outer.canonicalFreshKey shape
    outer.canonicalFreshKey_fresh Reference).trans
      (basis ((Circuit.retainedLocalFrame (kind := kind)
        outer.canonicalFreshKey shape).register.prod Reference))

private def RetainedCoordinates.BasisFirst {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (basis : (Reference : Register) →
      (outer.register.prod Reference).Index ≃
        (base.register.prod (coordinates.reference Reference)).Index) : Prop :=
  ∀ (Reference : Register) (input : (outer.register.prod Reference).Index),
    HEq (basis Reference input).1 input.1

private theorem originalBasis_first :
    (originalCoordinates ctx).BasisFirst (originalBasis ctx) := by
  intro Reference input
  rfl

private theorem retainBasis_first {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer)
    (basis : (Reference : Register) →
      (outer.register.prod Reference).Index ≃
        (base.register.prod (prior.reference Reference)).Index)
    (preserves : prior.BasisFirst basis) (shape : CShape) :
    (retainCoordinates prior shape).BasisFirst (retainBasis prior basis shape) := by
  intro Reference input
  let intermediate := Circuit.underRetainedSplitBasis outer.canonicalFreshKey shape
    outer.canonicalFreshKey_fresh Reference input
  exact (preserves _ intermediate).trans
    (heq_of_eq (Circuit.underRetainedSplitBasis_left outer.canonicalFreshKey shape
      outer.canonicalFreshKey_fresh Reference input))

private def RetainedCoordinates.BasisData {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer) : Type 1 :=
  { basis : (Reference : Register) →
      (outer.register.prod Reference).Index ≃
        (base.register.prod (coordinates.reference Reference)).Index //
    coordinates.BasisFirst basis }

private def originalBasisData : (originalCoordinates ctx).BasisData :=
  ⟨originalBasis ctx, originalBasis_first⟩

private def retainBasisData {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer) (data : prior.BasisData) (shape : CShape) :
    (retainCoordinates prior shape).BasisData :=
  ⟨retainBasis prior data.val shape,
    retainBasis_first prior data.val data.property shape⟩

private def RetainedCoordinates.HasBlocks {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History)
    (basis : (Reference : Register) →
      (outer.register.prod Reference).Index ≃
        (base.register.prod (coordinates.reference Reference)).Index) : Prop :=
  ∀ {Reference : Register} {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State outer Reference (Hidden × H))
    (store : Store outer) (hidden : Hidden) (history : H),
    (coordinates.splitState state).block
        ((labels store).1, (hidden, ((labels store).2, history))) =
      (state.block (store, (hidden, history))).reindex (basis Reference)

private theorem originalStores_blocks :
    (originalCoordinates ctx).HasBlocks (originalStores ctx) (originalBasis ctx) := by
  intro Reference Hidden H _ _ state store hidden history
  let labels : (Store ctx × (Hidden × H)) ≃ (Store ctx × (Hidden × (Unit × H))) :=
    { toFun := fun entry => (entry.1, (entry.2.1, ((), entry.2.2)))
      invFun := fun entry => (entry.1, (entry.2.1, entry.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun entry => by cases entry.2.2.1; rfl }
  calc
    _ = state.block (store, (hidden, history)) :=
      mapped_block _ state labels (store, (hidden, ((), history)))
    _ = _ := (DensityOperator.reindex_refl _).symm

private theorem retainStores_blocks {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × prior.History)
    (basis : (Reference : Register) →
      (outer.register.prod Reference).Index ≃
        (base.register.prod (prior.reference Reference)).Index)
    (natural : prior.HasBlocks labels basis) (shape : CShape) :
    (retainCoordinates prior shape).HasBlocks (retainStores labels shape)
      (retainBasis prior basis shape) := by
  intro Reference Hidden H _ _ state store hidden history
  let split := retainedStores outer shape store
  let frame := Circuit.retainedLocalFrame (kind := kind) outer.canonicalFreshKey shape
  let intermediate := Circuit.underRetainedSplitState outer.canonicalFreshKey shape
    outer.canonicalFreshKey_fresh state
  let association : (Store base × (Hidden × (prior.History × (Store frame × H)))) ≃
        Store base × (Hidden × ((prior.History × Store frame) × H)) :=
    (Equiv.refl _).prodCongr
      ((Equiv.refl Hidden).prodCongr (Equiv.prodAssoc _ _ _).symm)
  have aligned :
      ((retainCoordinates prior shape).splitState state).block
          (((retainStores labels shape) store).1,
            (hidden, ((retainStores labels shape) store).2, history)) =
        (prior.splitState intermediate).block
          ((labels split.1).1, (hidden, ((labels split.1).2, (split.2, history)))) := by
    exact mapped_block _ (prior.splitState intermediate) association
      ((labels split.1).1, (hidden, (((labels split.1).2, split.2), history)))
  have carried :
      (intermediate.block (split.1, (hidden, (split.2, history)))).reindex
          (basis (frame.register.prod Reference)) =
        ((state.block (store, (hidden, history))).reindex
          (Circuit.underRetainedSplitBasis outer.canonicalFreshKey shape
            outer.canonicalFreshKey_fresh Reference)).reindex
              (basis (frame.register.prod Reference)) := by
    exact congrArg (fun density => density.reindex (basis (frame.register.prod Reference)))
      (retainedStores_block shape state store hidden history)
  have priorStep := natural intermediate split.1 hidden (split.2, history)
  have firstTwo := aligned.trans priorStep
  have firstThree := firstTwo.trans carried
  exact firstThree.trans (DensityOperator.reindex_trans _ _ _)

private structure RetainedCoordinates.CompleteData {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer) where
  labels : Store outer ≃ Store base × coordinates.History
  basisData : coordinates.BasisData
  blocks : coordinates.HasBlocks labels basisData.val

private def originalCompleteData : (originalCoordinates ctx).CompleteData where
  labels := originalStores ctx
  basisData := originalBasisData
  blocks := originalStores_blocks

private def retainCompleteData {base outer : RuntimeCtx kind}
    (prior : RetainedCoordinates base outer) (data : prior.CompleteData) (shape : CShape) :
    (retainCoordinates prior shape).CompleteData where
  labels := retainStores data.labels shape
  basisData := retainBasisData prior data.basisData shape
  blocks := retainStores_blocks prior data.labels data.basisData.val data.blocks shape

private def persistentCompleteData (width scalarWidth : Nat) :
    (persistentCoordinates ctx width scalarWidth).CompleteData :=
  let accepted := retainCompleteData (originalCoordinates ctx) originalCompleteData .bit
  let selected := retainCompleteData _ accepted (.unsignedWord scalarWidth)
  let inverse := retainCompleteData _ selected .bit
  let candidate := retainCompleteData _ inverse (.unsignedWord scalarWidth)
  let reconstruction := retainCompleteData _ candidate .bit
  let verified := retainCompleteData _ reconstruction .bit
  retainCompleteData _ verified (PointShape width)

/-- The exact seven-cell quantum coordinates, including the unchanged
external reference and the zero-wire retained frames. -/
def persistentLocalBasis (width scalarWidth : Nat) (Reference : Register) :
    ((persistentCtx ctx width scalarWidth).register.prod Reference).Index ≃
      (ctx.register.prod (persistentLocalReference ctx width scalarWidth Reference)).Index :=
  (persistentCompleteData width scalarWidth).basisData.val Reference

/-- Every complete seven-cell basis coordinate change leaves the physical
quantum-wire basis unchanged. -/
theorem persistentLocalBasis_left (width scalarWidth : Nat) (Reference : Register)
    (input : ((persistentCtx ctx width scalarWidth).register.prod Reference).Index) :
    (persistentLocalBasis width scalarWidth Reference input).1 = input.1 := by
  exact eq_of_heq
    ((persistentCompleteData width scalarWidth).basisData.property Reference input)

private theorem persistentStores_blocks (width scalarWidth : Nat) :
    (persistentCoordinates ctx width scalarWidth).HasBlocks
      (persistentStores ctx width scalarWidth) (persistentLocalBasis width scalarWidth) := by
  exact (persistentCompleteData width scalarWidth).blocks

/-- Splitting the seven actual persistent cells preserves every complete
stored density block by one exact quantum-basis equivalence. -/
theorem underPersistentSplitState_block (width scalarWidth : Nat)
    {Reference : Register} {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Hidden × H))
    (store : Store (persistentCtx ctx width scalarWidth)) (hidden : Hidden) (history : H) :
    (underPersistentSplitState width scalarWidth state).block
        (((persistentStores ctx width scalarWidth) store).1,
          (hidden, (((persistentStores ctx width scalarWidth) store).2, history))) =
      (state.block (store, (hidden, history))).reindex
        (persistentLocalBasis width scalarWidth Reference) :=
  persistentStores_blocks width scalarWidth state store hidden history

/-- The complete split label for one actual persistent Store, hidden service
state and caller history. -/
def persistentOutputRecord (width scalarWidth : Nat)
    {Hidden H : Type}
    (store : Store (persistentCtx ctx width scalarWidth))
    (hidden : Hidden) (history : H) :
    Store ctx × (Hidden × (persistentLocalHistory ctx width scalarWidth × H)) :=
  (((persistentStores ctx width scalarWidth) store).1,
    (hidden, (((persistentStores ctx width scalarWidth) store).2, history)))

/-- The public split-record interface retains the entire joint density block. -/
theorem underPersistentSplitState_block_at (width scalarWidth : Nat)
    {Reference : Register} {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Hidden × H))
    (store : Store (persistentCtx ctx width scalarWidth)) (hidden : Hidden) (history : H) :
    (underPersistentSplitState width scalarWidth state).block
        (persistentOutputRecord width scalarWidth store hidden history) =
      (state.block (store, (hidden, history))).reindex
        (persistentLocalBasis width scalarWidth Reference) :=
  underPersistentSplitState_block width scalarWidth state store hidden history

/-- Splitting the seven retained classical cells into reference and history
coordinates preserves support on every original quantum wire. -/
theorem underPersistentSplitState_basisSupport (width scalarWidth : Nat)
    {Reference : Register} {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Hidden × H))
    (label : ctx.register.Index)
    (supported : ∀ basis, basis.1 ≠ label →
      state.quantumMarginal.matrix basis basis = 0)
    (basis : (ctx.register.prod
      (persistentLocalReference ctx width scalarWidth Reference)).Index)
    (outside : basis.1 ≠ label) :
    (underPersistentSplitState width scalarWidth state).quantumMarginal.matrix basis basis =
      0 := by
  change (∑ output, ((underPersistentSplitState width scalarWidth state).block output).matrix)
    basis basis = 0
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro output _
  rcases output with ⟨baseStore, hidden, retained, history⟩
  let originalStore :=
    (persistentStores ctx width scalarWidth).symm (baseStore, retained)
  let originalBasis := (persistentLocalBasis width scalarWidth Reference).symm basis
  have outsideOriginal : originalBasis.1 ≠ label := by
    intro same
    apply outside
    have aligned := persistentLocalBasis_left width scalarWidth Reference originalBasis
    simp only [originalBasis, Equiv.apply_symm_apply] at aligned
    exact aligned.trans same
  have zero := ExecutionState.block_diagonal_zero state originalBasis
    (supported originalBasis outsideOriginal) (originalStore, (hidden, history))
  have blockEq :
      (underPersistentSplitState width scalarWidth state).block
        (baseStore, (hidden, (retained, history))) =
      (state.block (originalStore, (hidden, history))).reindex
        (persistentLocalBasis width scalarWidth Reference) := by
    have actual := underPersistentSplitState_block width scalarWidth state
      originalStore hidden history
    simpa only [originalStore, Equiv.apply_symm_apply] using actual
  rw [blockEq, DensityOperator.reindex_entry]
  simpa only [originalBasis] using zero

private def RetainedCoordinates.executionRecords {model : ExecutionModel}
    {base outer : RuntimeCtx model.kind} (coordinates : RetainedCoordinates base outer)
    (code : Circuit model base base) (extended : Circuit model outer outer)
    (path : code.Path ≃ extended.Path) (H : Type) :
    (Store base × (model.HiddenState ×
      ((coordinates.History × H) × code.Path))) ≃
    (Store base × (model.HiddenState ×
      (coordinates.History × (H × extended.Path)))) :=
  (Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr
    ((Equiv.prodAssoc _ _ _).trans
      ((Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr
        path))))

private theorem RetainedCoordinates.executedState_block {model : ExecutionModel}
    {base outer : RuntimeCtx model.kind} (coordinates : RetainedCoordinates base outer)
    (code : Circuit model base base) (extended : Circuit model outer outer)
    (path : code.Path ≃ extended.Path)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State outer Reference (model.HiddenState × H))
    (record : Store base × (model.HiddenState ×
      (coordinates.History × (H × extended.Path)))) :
    (coordinates.executedState code extended path state).block record =
      (code.execute (coordinates.reference Reference)
        (coordinates.splitState state)).block
          ((coordinates.executionRecords code extended path H).symm record) := by
  let update :
      (Store base × (model.HiddenState × ((coordinates.History × H) × code.Path))) →
      (Store base × (model.HiddenState ×
        (coordinates.History × (H × extended.Path)))) :=
    fun value => (value.1, (value.2.1,
      (value.2.2.1.1, (value.2.2.1.2, path value.2.2.2))))
  have sameMap : update = coordinates.executionRecords code extended path H := by
    funext original
    rcases original with ⟨store, hidden, ⟨retained, history⟩, originalPath⟩
    rfl
  let output := code.execute (coordinates.reference Reference) (coordinates.splitState state)
  have sameState :
      (coordinates.executedState code extended path state) =
        output.mapClassical (coordinates.executionRecords code extended path H) := by
    unfold RetainedCoordinates.executedState State.mapHistory
    exact ExecutionState.executionState_mapClassical_congr_decision output
      update (coordinates.executionRecords code extended path H)
      (fun original => congrFun sameMap original) _ _
  rw [sameState]
  exact mapped_block _ output (coordinates.executionRecords code extended path H) record

/-- Relabel the original local path together with the retained-cell history;
no physical or reference register is discarded. -/
def underPersistentExecutionRecords {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (code : Circuit model ctx ctx)
    (supported : code.IsLocal) (width scalarWidth : Nat) (H : Type) :
    (Store ctx × (model.HiddenState ×
      ((persistentLocalHistory ctx width scalarWidth × H) × code.Path))) ≃
    (Store ctx × (model.HiddenState ×
      (persistentLocalHistory ctx width scalarWidth ×
        (H × (underPersistent code supported width scalarWidth).Path)))) :=
  (persistentCoordinates ctx width scalarWidth).executionRecords code
    (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth) H

/-- The split execution uses exactly the original local circuit block at the
equivalent path, including the unchanged hidden state and retained history. -/
theorem underPersistentExecutionState_block {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (code : Circuit model ctx ctx)
    (supported : code.IsLocal) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × H))
    (record : Store ctx × (model.HiddenState ×
      (persistentLocalHistory ctx width scalarWidth ×
        (H × (underPersistent code supported width scalarWidth).Path)))) :
    (underPersistentExecutionState code supported width scalarWidth state).block record =
      (code.execute (persistentLocalReference ctx width scalarWidth Reference)
        (underPersistentSplitState width scalarWidth state)).block
          ((underPersistentExecutionRecords code supported width scalarWidth H).symm record) := by
  exact (persistentCoordinates ctx width scalarWidth).executedState_block code
    (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth) state record

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
    (masses : coordinates.HasStores labels) {Reference : Register}
    {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State outer Reference (Hidden × H))
    (predicate : coordinates.History → Prop)
    (holds : ∀ entry, 0 < (state.block entry).mass → predicate (labels entry.1).2)
    (result : Store base × (Hidden × (coordinates.History × H)))
    (positive : 0 < ((coordinates.splitState state).block result).mass) :
    predicate result.2.2.1 := by
  let original := labels.symm (result.1, result.2.2.1)
  have same : labels original = (result.1, result.2.2.1) := labels.apply_symm_apply _
  have mass := masses state original result.2.1 result.2.2.2
  rw [same] at mass
  have input := holds (original, (result.2.1, result.2.2.2))
    (by simpa only [← mass] using positive)
  simpa only [same] using input

private theorem retained_observation_supported {model : ExecutionModel}
    {base outer : RuntimeCtx model.kind}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History)
    (masses : coordinates.HasStores labels)
    (code : Circuit model base base) (extended : Circuit model outer outer)
    (path : code.Path ≃ extended.Path)
    (natural : coordinates.Executes code extended path)
    {D : Type} [Finite D] (read : coordinates.History → D) (wanted : D)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State outer Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass → read (labels entry.1).2 = wanted)
    (result : Store outer × (model.HiddenState × (H × extended.Path)))
    (positive : 0 < ((extended.execute Reference state).block result).mass) :
    read (labels result.1).2 = wanted := by
  let split := coordinates.splitState state
  have splitHolds : ∀ entry, 0 < (split.block entry).mass →
      read entry.2.2.1 = wanted := by
    intro entry present
    exact coordinate_supported coordinates labels masses state
      (fun history => read history = wanted)
      holds entry present
  let saved := labels result.1
  have positiveSplit : 0 < ((coordinates.splitState (extended.execute Reference state)).block
      (saved.1, (result.2.1, (saved.2, result.2.2)))).mass :=
    lt_of_lt_of_eq positive (masses (extended.execute Reference state)
      result.1 result.2.1 result.2.2).symm
  rw [natural] at positiveSplit
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positiveSplit
  have kept := history_supported code (coordinates.reference Reference) split
    (fun history => read history.1) wanted splitHolds original present
  have savedSame : original.2.2.1.1 = saved.2 :=
    congrArg (fun entry => entry.2.2.1) equality
  rw [savedSame] at kept
  exact kept

/-- Actual local sampling preserves any common stored acceptance bit and selected word. -/
theorem underPersistent_latches_supported
    {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (code : Circuit model ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (wanted : Bool × (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) = wanted)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (underPersistent code supported width scalarWidth).Path)))
    (positive : 0 < (((underPersistent code supported width scalarWidth).execute
      Reference state).block result).mass) :
    ((result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) =
        wanted := by
  have kept := retained_observation_supported (persistentCoordinates ctx width scalarWidth)
    (persistentStores ctx width scalarWidth)
    (@persistentStores_mass model.kind ctx width scalarWidth)
    code (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth)
    (@persistentCoordinates_execute model ctx code supported width scalarWidth)
    (savedLatches width scalarWidth) wanted state
    (fun original positive => (persistentStores_latches width scalarWidth original.1).trans
      (holds original positive)) result positive
  exact (persistentStores_latches width scalarWidth result.1).symm.trans kept

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
