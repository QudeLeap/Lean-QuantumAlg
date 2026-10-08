/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Observation
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Actual original-input events beside the seven persistent cells

The exact Store coordinates preserve every structural input read and each
full block's mass. Events on those original reads therefore agree before
and after the seven-cell coordinate split. Applying the existing complete
execution equation gives the event of the same actual local code, with all
existing cell values, histories and reference correlations retained.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem retainedStores_read_input (shape : CShape)
    (store : Store (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh))
    {valueShape : CShape} (input : CInputRef ctx valueShape) :
    (retainedStores ctx shape store).1.read input =
      store.read (input.underRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh) := by
  induction input with
  | storage ref =>
      change (retainedStores ctx shape store).1.read (.storage ref) =
        store.read (.storage (ref.underRetained ctx.canonicalFreshKey shape
          ctx.canonicalFreshKey_fresh))
      let separate := Circuit.retainedLocalDisjoint ctx ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh
      let same := Circuit.retainedLocalPermutation ctx ctx.canonicalFreshKey shape
        ctx.canonicalFreshKey_fresh
      have refs : ContextPermutation.storage same (ContextUnion.storageLeft separate ref) =
          ref.underRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh :=
        CStorageRef.storageRef_eq_of_key _ _ rfl
      conv_rhs => rw [← retainedStores_join shape store, ← refs,
        ContextPermutation.store_read_storage]
      exact (ContextUnion.contextUnion_read_join_left separate _ _ (.storage ref)).symm
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

private theorem retainStores_read {base outer : RuntimeCtx kind} {History : Type}
    (labels : Store outer ≃ Store base × History) {valueShape : CShape}
    (input : CInputRef base valueShape) (lifted : CInputRef outer valueShape)
    (reads : ∀ store, (labels store).1.read input = store.read lifted) (shape : CShape)
    (store : Store (outer.addRetained outer.canonicalFreshKey shape
      outer.canonicalFreshKey_fresh)) :
    (retainStores labels shape store).1.read input =
      store.read (lifted.underRetained outer.canonicalFreshKey shape
        outer.canonicalFreshKey_fresh) :=
  (reads (retainedStores outer shape store).1).trans (retainedStores_read_input shape store lifted)

private theorem persistentStores_read_input (width scalarWidth : Nat)
    {shape : CShape} (input : CInputRef ctx shape)
    (store : Store (persistentCtx ctx width scalarWidth)) :
    (persistentStores ctx width scalarWidth store).1.read input =
      store.read (persistentInput width scalarWidth input) := by
  have original (before : Store ctx) : (originalStores ctx before).1.read input =
      before.read input := rfl
  have accepted := @retainStores_read _ _ _ _ (originalStores ctx) _ input input original .bit
  have selected := @retainStores_read _ _ _ _ _ _ input _ accepted (.unsignedWord scalarWidth)
  have inverse := @retainStores_read _ _ _ _ _ _ input _ selected .bit
  have candidate := @retainStores_read _ _ _ _ _ _ input _ inverse (.unsignedWord scalarWidth)
  have reconstruction := @retainStores_read _ _ _ _ _ _ input _ candidate .bit
  have verified := @retainStores_read _ _ _ _ _ _ input _ reconstruction .bit
  have scalar := @retainStores_read _ _ _ _ _ _ input _ verified (PointShape width)
  exact scalar store

private def coordinateRecords {base outer : RuntimeCtx kind} {Hidden : Type}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History) (History : Type) :
    (Store outer × (Hidden × History)) ≃
      (Store base × (Hidden × (coordinates.History × History))) where
  toFun record :=
    ((labels record.1).1, (record.2.1, ((labels record.1).2, record.2.2)))
  invFun record :=
    (labels.symm (record.1, record.2.2.1), (record.2.1, record.2.2.2))
  left_inv record := by
    cases record with
    | mk store history =>
        change (labels.symm (labels store), history) = (store, history)
        rw [Equiv.symm_apply_apply]
  right_inv record := by
    cases record with
    | mk store history =>
        simp only [Equiv.apply_symm_apply]

private theorem coordinate_mass {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History)
    (masses : coordinates.HasStores labels) {Reference : Register}
    {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State outer Reference (Hidden × History)) :
    (coordinates.splitState state).mass = state.mass := by
  unfold ExecutionState.mass
  rw [← (coordinateRecords coordinates labels History).sum_comp]
  exact Finset.sum_congr rfl
    (fun record _ => masses state record.1 record.2.1 record.2.2)

private theorem event_indicator_weight {R : Register} (selected : Bool)
    (state : DensityOperator R) :
    (if selected = true then Effect.one R else Effect.zero R).weight state =
      if selected = true then state.mass else 0 := by
  split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero]

private theorem coordinate_eventWeight {base outer : RuntimeCtx kind}
    (coordinates : RetainedCoordinates base outer)
    (labels : Store outer ≃ Store base × coordinates.History)
    (masses : coordinates.HasStores labels)
    (originalRead : Store base → Bool) (actualRead : Store outer → Bool)
    (reads : ∀ store, originalRead (labels store).1 = actualRead store)
    {Reference : Register} {Hidden History : Type}
    [Fintype Hidden] [Fintype History]
    (state : State outer Reference (Hidden × History)) :
    state.effectWeight (fun record => if actualRead record.1 = true then
        Effect.one (outer.register.prod Reference)
      else Effect.zero (outer.register.prod Reference)) =
      (coordinates.splitState state).effectWeight (fun record =>
        if originalRead record.1 = true then
          Effect.one (base.register.prod (coordinates.reference Reference))
        else Effect.zero (base.register.prod (coordinates.reference Reference))) := by
  symm
  simp only [ExecutionState.effectWeight, event_indicator_weight]
  rw [← (coordinateRecords coordinates labels History).sum_comp]
  apply Finset.sum_congr rfl
  intro record _
  change (if originalRead (labels record.1).1 = true then
    ((coordinates.splitState state).block ((labels record.1).1,
      (record.2.1, ((labels record.1).2, record.2.2)))).mass else 0) = _
  rw [reads, masses]

private theorem executedState_eventWeight {model : ExecutionModel}
    {base outer : RuntimeCtx model.kind}
    (coordinates : RetainedCoordinates base outer)
    (code : Circuit model base base) (extended : Circuit model outer outer)
    (path : code.Path ≃ extended.Path)
    {shape : CShape} (input : CInputRef base shape) (event : shape.Value → Bool)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State outer Reference (model.HiddenState × History)) :
    (coordinates.executedState code extended path state).effectWeight (fun record =>
      if event (record.1.read input) = true then
        Effect.one (base.register.prod (coordinates.reference Reference))
      else Effect.zero (base.register.prod (coordinates.reference Reference))) =
      (code.execute (coordinates.reference Reference) (coordinates.splitState state)).effectWeight
        (fun record => if event (record.1.read input) = true then
          Effect.one (base.register.prod (coordinates.reference Reference))
        else Effect.zero (base.register.prod (coordinates.reference Reference))) := by
  unfold RetainedCoordinates.executedState
  rw [State.effectWeight_mapHistory]

/-- Exact seven-cell coordinates retain the complete mass of the original state. -/
theorem underPersistentSplitState_mass (width scalarWidth : Nat)
    {Reference : Register} {Hidden History : Type}
    [Fintype Hidden] [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Hidden × History)) :
    (underPersistentSplitState width scalarWidth state).mass = state.mass :=
  coordinate_mass (persistentCoordinates ctx width scalarWidth)
    (persistentStores ctx width scalarWidth) (@persistentStores_mass kind ctx width scalarWidth)
    state

/-- An event reads the same original input in the full persistent Store coordinates. -/
theorem underPersistentSplitState_eventWeight (width scalarWidth : Nat)
    {Reference : Register} {Hidden History : Type}
    [Fintype Hidden] [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Hidden × History))
    {shape : CShape} (input : CInputRef ctx shape) (event : shape.Value → Bool) :
    state.effectWeight (fun record =>
      if event (record.1.read (persistentInput width scalarWidth input)) = true then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      (underPersistentSplitState width scalarWidth state).effectWeight (fun record =>
        if event (record.1.read input) = true then
          Effect.one (ctx.register.prod (persistentLocalReference ctx width scalarWidth Reference))
        else Effect.zero
          (ctx.register.prod (persistentLocalReference ctx width scalarWidth Reference))) :=
  coordinate_eventWeight (persistentCoordinates ctx width scalarWidth)
    (persistentStores ctx width scalarWidth) (@persistentStores_mass kind ctx width scalarWidth)
    (fun store => event (store.read input))
    (fun store => event (store.read (persistentInput width scalarWidth input)))
    (fun store => congrArg event (persistentStores_read_input width scalarWidth input store)) state

/-- Actual extended local execution preserves original-read events in full split coordinates. -/
theorem underPersistent_eventWeight {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (code : Circuit model ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × History))
    {shape : CShape} (input : CInputRef ctx shape) (event : shape.Value → Bool) :
    ((underPersistent code supported width scalarWidth).execute Reference state).effectWeight
      (fun record =>
        if event (record.1.read (persistentInput width scalarWidth input)) = true then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      (code.execute (persistentLocalReference ctx width scalarWidth Reference)
        (underPersistentSplitState width scalarWidth state)).effectWeight (fun record =>
          if event (record.1.read input) = true then
            Effect.one
              (ctx.register.prod (persistentLocalReference ctx width scalarWidth Reference))
          else Effect.zero
            (ctx.register.prod (persistentLocalReference ctx width scalarWidth Reference))) := by
  have split := underPersistentSplitState_eventWeight width scalarWidth
    ((underPersistent code supported width scalarWidth).execute Reference state) input event
  rw [underPersistent_execute] at split
  exact split.trans (executedState_eventWeight (persistentCoordinates ctx width scalarWidth)
    code (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth) input event state)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
