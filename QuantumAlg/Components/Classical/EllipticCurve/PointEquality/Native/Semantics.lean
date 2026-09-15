/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Correctness
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Complete actual-state semantics of native point equality

All intermediate values are read from the executing Store. The lexical cells
are fresh and distinct by construction. The final state retains the original
quantum register, arbitrary external reference and actual instruction history.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Record the actual store update of each of the original eight native stages. -/
def stageRecord (left right : CInputRef ctx (PointShape width)) (scratch : Scratch ctx width)
    (output : CWriteRef ctx .bit) (index : Fin 8) :
    Store ctx → Store ctx × (stage left right scratch output index).Path := by
  refine Fin.cases
    (fun store => (store.applyOp (unpackLeft left scratch), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (unpackRight right scratch), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (tagXor scratch), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (tagNot scratch), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (equalX scratch), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (equalY scratch), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (coordinateAnd scratch), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (outputAnd scratch output), ()))
    (fun index => ?_) index
  exact Fin.elim0 index

/-- Each recorded stage is its actual complete state interpretation. -/
theorem stage_execute (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (output : CWriteRef ctx .bit) (index : Fin 8)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (stage left right scratch output index).execute Reference state =
      state.mapClassical (fun entry =>
        ((stageRecord left right scratch output index entry.1).1,
          (entry.2, (stageRecord left right scratch output index entry.1).2))) := by
  fin_cases index <;>
    refine (Circuit.execute_classical_mapClassical _ Reference state).trans ?_
  all_goals
    congr 1
    exact Subsingleton.elim _ _

/-- The actual sequence record retains the real intermediate stores and native paths. -/
def coreRecord (left right : CInputRef ctx (PointShape width)) (scratch : Scratch ctx width)
    (output : CWriteRef ctx .bit) : Store ctx → Store ctx × (core left right scratch output).Path :=
  Circuit.forRangeRecord 8 (stage left right scratch output)
    (stageRecord left right scratch output)

/-- All eight native instructions compose on complete quantum-reference blocks. -/
theorem core_execute (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (output : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (core left right scratch output).execute Reference state =
      state.mapClassical (fun entry =>
        ((coreRecord left right scratch output entry.1).1,
          (entry.2, (coreRecord left right scratch output entry.1).2))) :=
  Circuit.execute_forRangeRecord 8 (stage left right scratch output)
    (stageRecord left right scratch output) (stage_execute left right scratch output)
    Reference state

/-- The chronological Store after the seven internal workspace writes. -/
def scratchStore (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (store : Store ctx) : Store ctx :=
  let store1 := store.applyOp (unpackLeft left scratch)
  let store2 := store1.applyOp (unpackRight right scratch)
  let store3 := store2.applyOp (tagXor scratch)
  let store4 := store3.applyOp (tagNot scratch)
  let store5 := store4.applyOp (equalX scratch)
  let store6 := store5.applyOp (equalY scratch)
  let store7 := store6.applyOp (coordinateAnd scratch)
  store7

/-- The complete sequence ends with the actual destination write. -/
theorem coreRecord_store (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (output : CWriteRef ctx .bit) (store : Store ctx) :
    (coreRecord left right scratch output store).1 =
      (scratchStore left right scratch store).applyOp (outputAnd scratch output) := by
  rfl

/-- The physical identities of the original five scratch cells. -/
def Scratch.keys (scratch : Scratch ctx width) : List StorageKey :=
  [scratch.leftRaw.key, scratch.rightRaw.key, scratch.tag.key, scratch.x.key, scratch.y.key]

/-- The exact separation needed by the general same-context core. -/
structure Separation (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) : Prop where
  distinct : scratch.keys.Nodup
  left : ∀ key ∈ scratch.keys, key ∉ left.storageKeys
  right : ∀ key ∈ scratch.keys, key ∉ right.storageKeys

private theorem scratchStore_preserves (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape)
    (separated : ∀ key ∈ scratch.keys, key ∉ input.storageKeys) :
    (scratchStore left right scratch store).read input = store.read input := by
  have l := separated scratch.leftRaw.key (by simp [Scratch.keys])
  have r := separated scratch.rightRaw.key (by simp [Scratch.keys])
  have t := separated scratch.tag.key (by simp [Scratch.keys])
  have x := separated scratch.x.key (by simp [Scratch.keys])
  have y := separated scratch.y.key (by simp [Scratch.keys])
  unfold scratchStore
  repeat rw [Store.read_applyOp_of_not_mem_storageKeys]
  all_goals first | rfl | exact l | exact r | exact t | exact x | exact y

private theorem read_product (store : Store ctx) {first second : CShape}
    (left : CInputRef ctx first) (right : CInputRef ctx second) :
    store.read (.product left right) = .product (store.read left) (store.read right) := rfl

private theorem read_first (store : Store ctx) {first second : CShape}
    (input : CInputRef ctx (.product first second)) :
    store.read (.first input) = (store.read input).first := rfl

private theorem read_second (store : Store ctx) {first second : CShape}
    (input : CInputRef ctx (.product first second)) :
    store.read (.second input) = (store.read input).second := rfl

private theorem read_written (store : Store ctx) {shape : CShape}
    (output : CWriteRef ctx shape) (value : CShape.Value shape) :
    (store.write output value).read (read output) = value :=
  Store.read_write_same store output value

private theorem read_other (store : Store ctx) {first second : CShape}
    (output : CWriteRef ctx first) (input : CWriteRef ctx second)
    (value : CShape.Value first) (different : output.key ≠ input.key) :
    (store.write output value).read (read input) = store.read (read input) :=
  Store.read_write_other store output input.toCStorageRef value different

/-- The original native workspace stages compute precisely the full nominal point equality. -/
theorem scratchStore_comparison (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (separated : Separation left right scratch)
    (store : Store ctx) :
    (outputAnd scratch (scratch.tag)).eval
      ((scratchStore left right scratch store).read (outputAnd scratch scratch.tag).inputRef) =
      .bit (pointEqual (store.read left) (store.read right)) := by
  have distinct :
      (scratch.leftRaw.key ≠ scratch.rightRaw.key ∧ scratch.leftRaw.key ≠ scratch.tag.key ∧
        scratch.leftRaw.key ≠ scratch.x.key ∧ scratch.leftRaw.key ≠ scratch.y.key) ∧
      (scratch.rightRaw.key ≠ scratch.tag.key ∧ scratch.rightRaw.key ≠ scratch.x.key ∧
        scratch.rightRaw.key ≠ scratch.y.key) ∧
      (scratch.tag.key ≠ scratch.x.key ∧ scratch.tag.key ≠ scratch.y.key) ∧
      scratch.x.key ≠ scratch.y.key := by
    simpa [Scratch.keys] using separated.distinct
  rcases distinct with ⟨⟨lr, lt, lx, _ly⟩, ⟨⟨rt, rx, _ry⟩, ⟨⟨tx, ty⟩, xy⟩⟩⟩
  have leftRight : scratch.leftRaw.key ∉ right.storageKeys :=
    separated.right scratch.leftRaw.key (by simp [Scratch.keys])
  have sourceRight := Store.read_applyOp_of_not_mem_storageKeys store
    (unpackLeft left scratch) right leftRight
  simp only [Store.applyOp, unpackLeft, ClassicalOp.outputRef, ClassicalOp.inputRef,
    ClassicalOp.eval_unpackEllipticCurvePoint] at sourceRight
  have rlRead := fun current value => read_other current scratch.rightRaw scratch.leftRaw value
    (Ne.symm lr)
  have tlRead := fun current value => read_other current scratch.tag scratch.leftRaw value
    (Ne.symm lt)
  have trRead := fun current value => read_other current scratch.tag scratch.rightRaw value
    (Ne.symm rt)
  have xlRead := fun current value => read_other current scratch.x scratch.leftRaw value
    (Ne.symm lx)
  have xrRead := fun current value => read_other current scratch.x scratch.rightRaw value
    (Ne.symm rx)
  have xtRead := fun current value => read_other current scratch.x scratch.tag value (Ne.symm tx)
  have ytRead := fun current value => read_other current scratch.y scratch.tag value (Ne.symm ty)
  have yxRead := fun current value => read_other current scratch.y scratch.x value (Ne.symm xy)
  simp only [outputAnd, ClassicalOp.eval_bit, ClassicalOp.inputRef, scratchStore,
    Store.applyOp, unpackLeft, unpackRight, tagXor, tagNot, equalX, equalY, coordinateAnd,
    ClassicalOp.outputRef, read_product, read_first, read_second,
    ClassicalOp.eval_unpackEllipticCurvePoint, ClassicalOp.eval_wordBinary, read_written,
    rlRead, tlRead, trRead, xlRead, xrRead, xtRead, ytRead, yxRead, sourceRight]
  cases store.read left with
  | ellipticCurvePoint leftTag leftX leftY =>
    cases store.read right with
    | ellipticCurvePoint rightTag rightX rightY =>
      cases leftTag <;> cases rightTag <;>
        simp [pointEqual, decodeCode, CShape.unpackEllipticCurvePoint, Resource.BitOpcode.eval,
          Resource.WordBinaryOpcode.eval, CShape.Value.first, CShape.Value.second,
          CShape.Value.toNat, Fin.ext_iff]

private theorem scratchOfCells_keys (cells : Cells ctx (scratchShapes width)) :
    (scratchOfCells cells).keys = cells.keys := by
  cases cells with
  | cons left rest =>
    cases rest with
    | cons right rest =>
      cases rest with
      | cons tag rest =>
        cases rest with
        | cons x rest =>
          cases rest with
          | cons y rest =>
            cases rest
            rfl

/-- Real lexical allocation discharges the general core's complete input separation. -/
theorem scratchOfCells_separation {outer : RuntimeCtx kind}
    (left right : CInputRef outer (PointShape width))
    (cells : Cells ctx (scratchShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    Separation (transport.liftInput left) (transport.liftInput right) (scratchOfCells cells) := by
  constructor
  · rw [scratchOfCells_keys]
    exact Cells.workspaceCells_distinct_keys_nodup cells distinct
  · intro key member
    rw [scratchOfCells_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      member left
  · intro key member
    rw [scratchOfCells_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      member right

private theorem scratchStore_readsAs {outer : RuntimeCtx kind}
    (left right : CInputRef outer (PointShape width))
    (cells : Cells ctx (scratchShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (source : Store outer) (before : Store ctx)
    (reads : transport.ReadsAs source before) :
    transport.ReadsAs source
      (scratchStore (transport.liftInput left) (transport.liftInput right)
        (scratchOfCells cells) before) := by
  intro shape input
  refine (scratchStore_preserves _ _ _ _ (transport.liftInput input) ?_).trans (reads input)
  intro key member
  rw [scratchOfCells_keys] at member
  exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated member input

/-- The actual allocated comparator changes only its destination in the complete caller store. -/
theorem compareInto_actualRecord (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) :
    ∃ step : Store ctx → Store ctx × (compareInto left right output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (compareInto left right output).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, (step before).1 =
        before.write output (.bit (pointEqual (before.read left) (before.read right))) := by
  apply withCells_actualRecord_post ctx (scratchShapes width)
    (fun cells _ transport _ => core (transport.liftInput left) (transport.liftInput right)
      (scratchOfCells cells) (transport.liftWrite output))
    (fun source target => target =
      source.write output (.bit (pointEqual (source.read left) (source.read right))))
  intro inner cells distinct transport separated
  refine ⟨coreRecord _ _ _ _, core_execute _ _ _ _, ?_⟩
  intro source before reads
  refine ⟨source.write output (.bit (pointEqual (source.read left) (source.read right))), rfl, ?_⟩
  have comparison := scratchStore_comparison (transport.liftInput left)
    (transport.liftInput right) (scratchOfCells cells)
    (scratchOfCells_separation left right cells distinct transport separated) before
  rw [reads left, reads right] at comparison
  rw [coreRecord_store, Store.applyOp]
  change transport.ReadsAs _
    ((scratchStore _ _ _ before).write (transport.liftWrite output) _)
  have sameValue : (outputAnd (scratchOfCells cells) (transport.liftWrite output)).eval
      ((scratchStore (transport.liftInput left) (transport.liftInput right)
        (scratchOfCells cells) before).read
          (outputAnd (scratchOfCells cells) (transport.liftWrite output)).inputRef) =
      .bit (pointEqual (source.read left) (source.read right)) := comparison
  rw [sameValue]
  intro shape input
  exact transport.workspaceTransport_readsAs_write
    (scratchStore_readsAs left right cells transport separated source before reads) output
    (.bit (pointEqual (source.read left) (source.read right))) input

/-- The chosen record is certified by the actual comparator's full interpreter equation. -/
def compareStep (left right : CInputRef ctx (PointShape width)) (output : CWriteRef ctx .bit) :
    Store ctx → Store ctx × (compareInto left right output).Path :=
  Classical.choose (compareInto_actualRecord left right output)

/-- Native comparison preserves all quantum-reference blocks and the real finite history. -/
theorem compareInto_execute (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (compareInto left right output).execute Reference state = state.mapClassical (fun entry =>
      ((compareStep left right output entry.1).1,
        (entry.2, (compareStep left right output entry.1).2))) :=
  (Classical.choose_spec (compareInto_actualRecord left right output)).1 Reference state

/-- The returned caller store is its original value with the comparison destination written. -/
theorem compareStep_store (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (before : Store ctx) :
    (compareStep left right output before).1 =
      before.write output (.bit (pointEqual (before.read left) (before.read right))) :=
  (Classical.choose_spec (compareInto_actualRecord left right output)).2 before

/-- Every initial store receives exactly the original complete point-comparison Boolean. -/
theorem compareInto_read_output (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (before : Store ctx) :
    (compareStep left right output before).1.read (read output) =
      .bit (pointEqual (before.read left) (before.read right)) := by
  rw [compareStep_store]
  exact Store.read_write_same before output _

/-- On represented points, the actual output bit accepts exactly semantic point equality. -/
theorem compareInto_accepts_iff (spec : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (left right : CInputRef ctx (PointShape width)) (output : CWriteRef ctx .bit)
    (before : Store ctx) (leftPoint rightPoint : Pure.Point spec)
    (leftRep : PointRepresents spec (before.read left) leftPoint)
    (rightRep : PointRepresents spec (before.read right) rightPoint) :
    (compareStep left right output before).1.read (read output) = .bit true ↔
      leftPoint = rightPoint := by
  rw [compareInto_read_output]
  simp only [CShape.Value.bit.injEq, pointEqual_eq_true_iff]
  constructor
  · intro encodedEqual
    have equal := congrArg
      (fun encoded => ClassicalAlgorithms.EllipticCurve.decode spec (decodeCode encoded))
      encodedEqual
    rw [leftRep, rightRep] at equal
    exact Option.some.inj equal
  · intro pointsEqual
    subst rightPoint
    have leftCode := ClassicalAlgorithms.EllipticCurve.encode_eq_of_decode_eq_some
      spec (decodeCode (before.read left)) leftPoint leftRep
    have rightCode := ClassicalAlgorithms.EllipticCurve.encode_eq_of_decode_eq_some
      spec (decodeCode (before.read right)) leftPoint rightRep
    have encodedEqual := congrArg encodeCode (leftCode.symm.trans rightCode)
    simpa only [encodeCode_decodeCode] using encodedEqual

/-- A structural caller input disjoint from the destination remains bitwise unchanged. -/
theorem compareInto_preserves_read (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (before : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : output.key ∉ input.storageKeys) :
    (compareStep left right output before).1.read input = before.read input := by
  rw [compareStep_store]
  exact Store.read_write_of_not_mem_storageKeys before output _ input separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality.Native
