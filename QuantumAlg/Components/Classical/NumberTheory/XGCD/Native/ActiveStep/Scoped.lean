/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Semantics.Signed
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Initialization.State.Transport
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Correctness
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store

/-!
# Actual scoped extended-Euclidean update records

The four scratch cells are allocated and released by the existing circuit.
Their separation follows from that allocation, while the same actual record
describes every quantum-reference block, path, returned state and caller read.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma stateFree_transport {inner : RuntimeCtx kind}
    (transport : Transport ctx inner) (cells : Cells ctx (stateShapes width))
    {shape : CShape} (input : CInputRef ctx shape)
    (free : ∀ index : Fin (stateShapes width).length,
      (cellAt cells index).ref.key ∉ input.storageKeys) :
    ∀ index : Fin (stateShapes width).length,
      (cellAt (transportCells transport cells) index).ref.key ∉
        (transport.liftInput input).storageKeys := by
  intro index
  rw [workspaceCells_cellAt_transportCells_ref, transport.liftWrite_key,
    transport.liftInput_storageKeys]
  exact free index

/-- One actual scoped record supplies execution, caller framing, signed state and activity. -/
lemma xgcdNativeScopedActive_actualRecord {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (scopedActive
      (model := model) cells zero).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (scopedActive (model := model) cells zero).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          (∀ index : Fin 7, stateKey cells index ∉ other.storageKeys) →
            ((record before).1.1).read other = before.1.read other) ∧
        (ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (PureXGCD.executionCoefficientWidth width)
          (PureXGCD.step (storedState cells before.1)).firstLeftCoefficient →
        ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (PureXGCD.executionCoefficientWidth width)
          (PureXGCD.step (storedState cells before.1)).firstRightCoefficient →
          storedState cells (record before).1.1 = PureXGCD.step (storedState cells before.1)) ∧
        ((before.1.read zero).toNat = 0 →
          (((record before).1.1).read (GCD.cellRead (activeCell cells))).toBool =
            decide ((storedState cells (record before).1.1).first ≠ 0)) := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      (∀ index : Fin 7, stateKey cells index ∉ other.storageKeys) →
        after.read other = before.read other) ∧
    (ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
      (PureXGCD.executionCoefficientWidth width)
      (PureXGCD.step (storedState cells before)).firstLeftCoefficient →
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
      (PureXGCD.executionCoefficientWidth width)
      (PureXGCD.step (storedState cells before)).firstRightCoefficient →
      storedState cells after = PureXGCD.step (storedState cells before)) ∧
    ((before.read zero).toNat = 0 →
      (after.read (GCD.cellRead (activeCell cells))).toBool =
        decide ((storedState cells after).first ≠ 0))
  refine withCells_actualRecord_post (environment := environment) ctx (activeScratchShapes width)
    (fun scratch _ transport _ =>
      activeBody (model := model) (transportCells transport cells) scratch (transport.liftInput
        zero)) Post ?_
  intro inner scratch scratchDistinct transport separated
  let lifted := transportCells transport cells
  let liftedZero := transport.liftInput zero
  have liftedDistinct := workspaceCells_transportCells_distinct transport cells distinct
  have cross := crossSeparated_of_nested transport cells scratch separated
  have liftedStateZero := stateFree_transport transport cells zero stateZero
  have scratchZero : ∀ index : Fin 4, (cellAt scratch index).ref.key ∉
      liftedZero.storageKeys := fun index =>
    Cells.workspaceCells_cellAt_transport_avoids scratch transport separated zero index
  refine ⟨fun before =>
    let result := activeBodyStep (model := model) lifted scratch liftedZero before.1
    ((result.1, before.2), result.2), ?_, ?_⟩
  · intro reference history _ state
    exact (xgcdNativeActiveBody_execute (model := model) lifted scratch liftedZero reference
      state).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · rintro source ⟨before, hidden⟩ reads
    let final := activeBodyStore lifted scratch liftedZero before
    let target := transport.restrict final
    have returned : transport.ReadsAs target final :=
      transport.workspaceTransport_restrict_readsAs final
    have inputState : storedState lifted before = storedState cells source :=
      xgcdNativeState_transport (width := width) transport cells source before reads
    have outputState : storedState lifted final = storedState cells target :=
      xgcdNativeState_transport (width := width) transport cells target final returned
    refine ⟨target, ⟨?_, ?_, ?_⟩, returned⟩
    · intro shape other free
      refine (returned other).symm.trans ((xgcdNativeActiveBody_read_other
        lifted scratch liftedZero (transport.liftInput other)
        (stateFree_transport transport cells other free)
        (fun index => Cells.workspaceCells_cellAt_transport_avoids
          scratch transport separated other index) before).trans (reads other))
    · intro leftRange rightRange
      have innerLeft : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (PureXGCD.executionCoefficientWidth width)
          (PureXGCD.step (storedState lifted before)).firstLeftCoefficient := by
        rw [inputState]
        exact leftRange
      have innerRight : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (PureXGCD.executionCoefficientWidth width)
          (PureXGCD.step (storedState lifted before)).firstRightCoefficient := by
        rw [inputState]
        exact rightRange
      have actual := xgcdNativeActiveBody_state (ctx := inner) (width := width)
        lifted liftedDistinct scratch scratchDistinct cross liftedZero liftedStateZero scratchZero
        before innerLeft innerRight
      exact outputState.symm.trans (actual.trans (congrArg PureXGCD.step inputState))
    · intro zeroValue
      have zeroRead : before.read liftedZero = source.read zero := reads zero
      have actual := xgcdNativeActiveBody_activity (ctx := inner) (width := width)
        lifted liftedDistinct scratch scratchDistinct cross liftedZero liftedStateZero scratchZero
        before (by rw [zeroRead]; exact zeroValue)
      have activeRead := xgcdNativeState_activity_transport transport cells target final returned
      exact (congrArg CShape.Value.toBool activeRead).symm.trans
        (actual.trans (congrArg
          (fun state : PureXGCD.State => decide (state.first ≠ 0)) outputState))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
