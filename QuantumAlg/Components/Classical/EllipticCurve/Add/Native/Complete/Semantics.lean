/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Generic.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Placement
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Dispatch.Semantics

/-!
# Actual complete native point-addition state

All original cases execute real native programs after actual classification.
Every internal allocation and release belongs to that execution. Its full
quantum-reference interpretation returns exactly one caller point write,
including malformed raw encodings and every legal result alias.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Exact finite nominal result of each original complete branch. -/
def additionCaseValue (spec : CurveSpec width) (selected : Case)
    (left right : CShape.Value (PointShape width)) : CShape.Value (PointShape width) :=
  match selected with
  | .leftInfinity => right
  | .rightInfinity => left
  | .vertical => .ellipticCurvePoint true 0 0
  | .doubling => doublingOutputValue spec (CShape.unpackEllipticCurvePoint width left)
  | .generic => genericOutputValue spec.field (CShape.unpackEllipticCurvePoint width left)
      (CShape.unpackEllipticCurvePoint width right)

/-- The original complete raw classification selects this total finite point result. -/
def additionOutputValue (spec : CurveSpec width)
    (left right : CShape.Value (PointShape width)) : CShape.Value (PointShape width) :=
  additionCaseValue spec (classifyValues left right) left right

/-- Each actual original arm contributes its own complete Store and native selected path. -/
def additionArmRecord (spec : CurveSpec width) (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width)) :
    ∀ selected, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (additionArm spec classifier output selected).Path
  | .leftInfinity => Circuit.preserveHiddenRecord (fun store =>
      (repackStore (classifierRead classifier.rightRaw) output store,
        (BitWord.instructionStep (execution := model)
          (repackOp (classifierRead classifier.rightRaw) output) store).2))
  | .rightInfinity => Circuit.preserveHiddenRecord (fun store =>
      (repackStore (classifierRead classifier.leftRaw) output store,
        (BitWord.instructionStep (execution := model)
          (repackOp (classifierRead classifier.leftRaw) output) store).2))
  | .vertical => Circuit.preserveHiddenRecord (infinityStep output)
  | .doubling => doublingIntoStep spec (classifierRead classifier.leftRaw) output
  | .generic => genericIntoStep spec.field (classifierRead classifier.leftRaw)
      (classifierRead classifier.rightRaw) output

/-- Every actual complete arm preserves the complete quantum-reference blocks and history. -/
theorem additionArm_execute (spec : CurveSpec width) (classifier : Classifier ctx width)
    (output : CWriteRef ctx (PointShape width)) (selected : Case) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (additionArm spec classifier output selected).execute Reference state =
      state.mapClassical (fun entry =>
        let result := additionArmRecord spec classifier output selected (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  cases selected with
  | leftInfinity =>
      refine (repackRawInto_execute _ _ Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | rightInfinity =>
      refine (repackRawInto_execute _ _ Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | vertical =>
      refine (infinityInto_execute output Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | doubling => exact doublingInto_execute _ _ _ Reference state
  | generic => exact genericInto_execute _ _ _ _ Reference state

/-- Actual snapshots give each selected original arm's exact sole destination write. -/
theorem additionArmRecord_ready_store (spec : CurveSpec width)
    (classifier : Classifier ctx width) (output : CWriteRef ctx (PointShape width))
    (selected : Case) (store : Store ctx) (hidden : model.HiddenState)
    (left right : CShape.Value (PointShape width))
    (ready : classifier.Ready store left right) :
    (additionArmRecord spec classifier output selected (store, hidden)).1.1 =
      store.write output (additionCaseValue spec selected left right) := by
  cases selected with
  | leftInfinity =>
      change store.write output (CShape.packEllipticCurvePoint width
        (store.read (classifierRead classifier.rightRaw))) = _
      rw [ready.rightRaw, CShape.packEllipticCurvePoint_unpackEllipticCurvePoint]
      rfl
  | rightInfinity =>
      change store.write output (CShape.packEllipticCurvePoint width
        (store.read (classifierRead classifier.leftRaw))) = _
      rw [ready.leftRaw, CShape.packEllipticCurvePoint_unpackEllipticCurvePoint]
      rfl
  | vertical => exact infinityStep_store output store
  | doubling =>
      change (doublingIntoStep spec (classifierRead classifier.leftRaw) output
        (store, hidden)).1.1 = _
      rw [doublingIntoStep_store, ready.leftRaw]
      rfl
  | generic =>
      change (genericIntoStep spec.field (classifierRead classifier.leftRaw)
        (classifierRead classifier.rightRaw) output (store, hidden)).1.1 = _
      rw [genericIntoStep_store, ready.leftRaw, ready.rightRaw]
      rfl

/-- Complete actual classification, branch execution and cleanup require no caller workspace. -/
theorem addInto_completeRecord (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width)) (output : CWriteRef ctx (PointShape width)) :
    ∃ record : Store ctx × model.HiddenState →
        (Store ctx × model.HiddenState) × (addInto spec left right output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (addInto spec left right output).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (record before).1.1 = before.1.write output
          (additionOutputValue spec (before.1.read left) (before.1.read right)) := by
  apply withClassification_actualRecord_post left right
    (fun classifier transport =>
      dispatch classifier (additionArm spec classifier (transport.liftWrite output)))
    (fun source target => target = source.write output
      (additionOutputValue spec (source.read left) (source.read right)))
  intro inner classifier transport
  refine ⟨dispatchRecord classifier (additionArm spec classifier (transport.liftWrite output))
    (additionArmRecord spec classifier (transport.liftWrite output)),
    dispatch_execute classifier _ _
      (additionArm_execute spec classifier (transport.liftWrite output)), ?_⟩
  intro source before reads ready
  refine ⟨source.write output (additionOutputValue spec (source.read left) (source.read right)),
    rfl, ?_⟩
  rw [dispatchRecord_ready_store _ _ _ _ _ _ ready,
    additionArmRecord_ready_store _ _ _ _ _ _ _ _ ready]
  exact Transport.workspaceTransport_readsAs_write transport reads output
    (additionOutputValue spec (source.read left) (source.read right))

/-- Actual complete-addition path and full caller Store, including every original complete case. -/
def addIntoStep (spec : CurveSpec width) (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width)) :
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (addInto spec left right output).Path :=
  Classical.choose (addInto_completeRecord spec left right output)

/-- Actual total addition retains every quantum-reference block and original history. -/
theorem addInto_execute (spec : CurveSpec width) (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (addInto spec left right output).execute Reference state = state.mapClassical (fun entry =>
      let result := addIntoStep spec left right output (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  (Classical.choose_spec (addInto_completeRecord spec left right output)).1 Reference state

/-- All actual internal work is released, leaving precisely the original finite output write. -/
theorem addIntoStep_store (spec : CurveSpec width) (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx)
    (hidden : model.HiddenState) :
    (addIntoStep spec left right output (store, hidden)).1.1 =
      store.write output (additionOutputValue spec (store.read left) (store.read right)) :=
  (Classical.choose_spec (addInto_completeRecord spec left right output)).2 (store, hidden)

/-- Every structural caller read outside the chosen actual destination remains bitwise unchanged. -/
theorem addInto_preserves_read (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width)) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) (hidden : model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : output.key ∉ observed.storageKeys) :
    (addIntoStep spec left right output (store, hidden)).1.1.read observed =
      store.read observed := by
  rw [addIntoStep_store]
  exact Store.read_write_of_not_mem_storageKeys store output _ observed separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
