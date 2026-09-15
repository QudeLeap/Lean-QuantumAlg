/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual complete-addition classifier state

The classifier equations refer to its real chronological Store writes and
complete reference-preserving execution. Internal allocation establishes the
zero word and all storage separation used by the local computation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual store update and native path of one classifier instruction. -/
def classifierStageRecord (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (index : Fin 5) :
    Store ctx → Store ctx × (classifierStage left right classifier index).Path := by
  refine Fin.cases
    (fun store => (store.applyOp (classifierUnpackLeft left classifier), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (classifierUnpackRight right classifier), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (classifierEqualX classifier), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (classifierEqualY classifier), ()))
    (fun index => ?_) index
  refine Fin.cases
    (fun store => (store.applyOp (classifierZeroY classifier), ()))
    (fun index => ?_) index
  exact Fin.elim0 index

/-- Every classifier stage preserves all complete quantum-reference blocks and prior history. -/
theorem classifierStage_execute (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (index : Fin 5) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (classifierStage left right classifier index).execute Reference state =
      state.mapClassical (fun entry =>
        ((classifierStageRecord left right classifier index entry.1).1,
          (entry.2, (classifierStageRecord left right classifier index entry.1).2))) := by
  fin_cases index <;>
    refine (Circuit.execute_classical_mapClassical _ Reference state).trans ?_
  all_goals
    congr 1
    exact Subsingleton.elim _ _

/-- The exact record of the original five-instruction classifier. -/
def classifierRecord (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) :
    Store ctx → Store ctx × (classifierBody left right classifier).Path :=
  Circuit.forRangeRecord 5 (classifierStage left right classifier)
    (classifierStageRecord left right classifier)

/-- The complete classifier interpreter is its actual deterministic classical update. -/
theorem classifierBody_execute (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (classifierBody left right classifier).execute Reference state =
      state.mapClassical (fun entry =>
        ((classifierRecord left right classifier entry.1).1,
          (entry.2, (classifierRecord left right classifier entry.1).2))) :=
  Circuit.execute_forRangeRecord 5 (classifierStage left right classifier)
    (classifierStageRecord left right classifier) (classifierStage_execute left right classifier)
    Reference state

/-- The exact chronological Store after the original five native instructions. -/
def classifierStore (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (store : Store ctx) : Store ctx :=
  let store1 := store.applyOp (classifierUnpackLeft left classifier)
  let store2 := store1.applyOp (classifierUnpackRight right classifier)
  let store3 := store2.applyOp (classifierEqualX classifier)
  let store4 := store3.applyOp (classifierEqualY classifier)
  store4.applyOp (classifierZeroY classifier)

/-- The interpreter record returns precisely the five actual native Store updates. -/
theorem classifierRecord_store (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (store : Store ctx) :
    (classifierRecord left right classifier store).1 =
      classifierStore left right classifier store :=
  rfl

/-- The actual identities of all classifier cells, including the allocated zero word. -/
def Classifier.keys (classifier : Classifier ctx width) : List StorageKey :=
  [classifier.leftRaw.key, classifier.rightRaw.key, classifier.xEqual.key,
    classifier.yEqual.key, classifier.zero.key, classifier.yZero.key]

/-- Separation needed only by the arbitrary same-context internal classifier. -/
structure Classifier.Separation (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) : Prop where
  distinct : classifier.keys.Nodup
  left : ∀ key ∈ classifier.keys, key ∉ left.storageKeys
  right : ∀ key ∈ classifier.keys, key ∉ right.storageKeys

/-- The complete actual values consumed by the original affine branch tree. -/
structure Classifier.Ready (classifier : Classifier ctx width) (store : Store ctx)
    (left right : CShape.Value (PointShape width)) : Prop where
  leftRaw : store.read (classifierRead classifier.leftRaw) =
    CShape.unpackEllipticCurvePoint width left
  rightRaw : store.read (classifierRead classifier.rightRaw) =
    CShape.unpackEllipticCurvePoint width right
  xEqual : store.read (classifierRead classifier.xEqual) =
    .bit (decide (left.ellipticCurvePointX = right.ellipticCurvePointX))
  yEqual : store.read (classifierRead classifier.yEqual) =
    .bit (decide (left.ellipticCurvePointY = right.ellipticCurvePointY))
  yZero : store.read (classifierRead classifier.yZero) =
    .bit (decide (left.ellipticCurvePointY = 0))

private theorem classifierStore_preserves (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape)
    (separated : ∀ key ∈ classifier.keys, key ∉ input.storageKeys) :
    (classifierStore left right classifier store).read input = store.read input := by
  have l := separated classifier.leftRaw.key (by simp [Classifier.keys])
  have r := separated classifier.rightRaw.key (by simp [Classifier.keys])
  have x := separated classifier.xEqual.key (by simp [Classifier.keys])
  have y := separated classifier.yEqual.key (by simp [Classifier.keys])
  have z := separated classifier.yZero.key (by simp [Classifier.keys])
  unfold classifierStore
  repeat rw [Store.read_applyOp_of_not_mem_storageKeys]
  all_goals first | rfl | exact l | exact r | exact x | exact y | exact z

private theorem read_product (store : Store ctx) {first second : CShape}
    (left : CInputRef ctx first) (right : CInputRef ctx second) :
    store.read (.product left right) = .product (store.read left) (store.read right) := rfl

private theorem read_first (store : Store ctx) {first second : CShape}
    (input : CInputRef ctx (.product first second)) :
    store.read (.first input) = (store.read input).first := rfl

private theorem read_second (store : Store ctx) {first second : CShape}
    (input : CInputRef ctx (.product first second)) :
    store.read (.second input) = (store.read input).second := rfl

private theorem read_op_other (store : Store ctx) {input output observed : CShape}
    (op : ClassicalOp input output ctx ctx) (ref : CWriteRef ctx observed)
    (different : op.outputRef.key ≠ ref.key) :
    (store.applyOp op).read (classifierRead ref) = store.read (classifierRead ref) :=
  Store.read_write_other store op.outputRef ref.toCStorageRef _ different

private theorem unpack_x_toNat (value : CShape.Value (PointShape width)) :
    (CShape.unpackEllipticCurvePoint width value).second.first.toNat =
      value.ellipticCurvePointX.val := by
  cases value
  rfl

private theorem unpack_y_toNat (value : CShape.Value (PointShape width)) :
    (CShape.unpackEllipticCurvePoint width value).second.second.toNat =
      value.ellipticCurvePointY.val := by
  cases value
  rfl

private theorem zeroWord_toNat :
    (CShape.Value.unsignedWord (0 : Fin (2 ^ width))).toNat = 0 := by
  change (0 : Fin (2 ^ width)).val = 0
  exact Fin.val_zero _

/-- Five real instructions establish all original predicates from the internal zero word. -/
theorem classifierBody_ready (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) (separated : classifier.Separation left right)
    (store : Store ctx) (zero : store.read (classifierRead classifier.zero) = .unsignedWord 0) :
    classifier.Ready (classifierStore left right classifier store)
      (store.read left) (store.read right) := by
  have distinct :
      (classifier.leftRaw.key ≠ classifier.rightRaw.key ∧
        classifier.leftRaw.key ≠ classifier.xEqual.key ∧
        classifier.leftRaw.key ≠ classifier.yEqual.key ∧
        classifier.leftRaw.key ≠ classifier.zero.key ∧
        classifier.leftRaw.key ≠ classifier.yZero.key) ∧
      (classifier.rightRaw.key ≠ classifier.xEqual.key ∧
        classifier.rightRaw.key ≠ classifier.yEqual.key ∧
        classifier.rightRaw.key ≠ classifier.zero.key ∧
        classifier.rightRaw.key ≠ classifier.yZero.key) ∧
      (classifier.xEqual.key ≠ classifier.yEqual.key ∧
        classifier.xEqual.key ≠ classifier.zero.key ∧
        classifier.xEqual.key ≠ classifier.yZero.key) ∧
      (classifier.yEqual.key ≠ classifier.zero.key ∧
        classifier.yEqual.key ≠ classifier.yZero.key) ∧
      classifier.zero.key ≠ classifier.yZero.key := by
    simpa [Classifier.keys] using separated.distinct
  rcases distinct with
    ⟨⟨lr, lx, ly, lz, lv⟩, ⟨⟨rx, ry, rz, rv⟩, ⟨⟨xy, xz, xv⟩, ⟨⟨yz, yv⟩, zv⟩⟩⟩⟩
  have leftRight : classifier.leftRaw.key ∉ right.storageKeys :=
    separated.right classifier.leftRaw.key (by simp [Classifier.keys])
  have sourceRight := Store.read_applyOp_of_not_mem_storageKeys store
    (classifierUnpackLeft left classifier) right leftRight
  have rightRaw_leftRaw := fun current =>
    read_op_other current (classifierUnpackRight right classifier) classifier.leftRaw (Ne.symm lr)
  have xEqual_leftRaw := fun current =>
    read_op_other current (classifierEqualX classifier) classifier.leftRaw (Ne.symm lx)
  have yEqual_leftRaw := fun current =>
    read_op_other current (classifierEqualY classifier) classifier.leftRaw (Ne.symm ly)
  have yZero_leftRaw := fun current =>
    read_op_other current (classifierZeroY classifier) classifier.leftRaw (Ne.symm lv)
  have xEqual_rightRaw := fun current =>
    read_op_other current (classifierEqualX classifier) classifier.rightRaw (Ne.symm rx)
  have yEqual_rightRaw := fun current =>
    read_op_other current (classifierEqualY classifier) classifier.rightRaw (Ne.symm ry)
  have yZero_rightRaw := fun current =>
    read_op_other current (classifierZeroY classifier) classifier.rightRaw (Ne.symm rv)
  have yEqual_xEqual := fun current =>
    read_op_other current (classifierEqualY classifier) classifier.xEqual (Ne.symm xy)
  have yZero_xEqual := fun current =>
    read_op_other current (classifierZeroY classifier) classifier.xEqual (Ne.symm xv)
  have yZero_yEqual := fun current =>
    read_op_other current (classifierZeroY classifier) classifier.yEqual (Ne.symm yv)
  have leftRaw_zero := fun current =>
    read_op_other current (classifierUnpackLeft left classifier) classifier.zero (lz)
  have rightRaw_zero := fun current =>
    read_op_other current (classifierUnpackRight right classifier) classifier.zero (rz)
  have xEqual_zero := fun current =>
    read_op_other current (classifierEqualX classifier) classifier.zero (xz)
  have yEqual_zero := fun current =>
    read_op_other current (classifierEqualY classifier) classifier.zero (yz)
  have leftWrite : ∀ current : Store ctx,
      (current.applyOp (classifierUnpackLeft left classifier)).read
        (classifierRead classifier.leftRaw) =
          CShape.unpackEllipticCurvePoint width (current.read left) := fun current =>
    Store.read_applyOp_output current (classifierUnpackLeft left classifier)
  have rightWrite : ∀ current : Store ctx,
      (current.applyOp (classifierUnpackRight right classifier)).read
        (classifierRead classifier.rightRaw) =
          CShape.unpackEllipticCurvePoint width (current.read right) := fun current =>
    Store.read_applyOp_output current (classifierUnpackRight right classifier)
  have xWrite : ∀ current : Store ctx,
      (current.applyOp (classifierEqualX classifier)).read (classifierRead classifier.xEqual) =
        .bit (decide ((current.read (classifierRead classifier.leftRaw)).second.first.toNat =
          (current.read (classifierRead classifier.rightRaw)).second.first.toNat)) := fun current =>
    Store.read_applyOp_output current (classifierEqualX classifier)
  have yWrite : ∀ current : Store ctx,
      (current.applyOp (classifierEqualY classifier)).read (classifierRead classifier.yEqual) =
        .bit (decide ((current.read (classifierRead classifier.leftRaw)).second.second.toNat =
          (current.read (classifierRead classifier.rightRaw)).second.second.toNat)) :=
    fun current => Store.read_applyOp_output current (classifierEqualY classifier)
  have zeroWrite : ∀ current : Store ctx,
      (current.applyOp (classifierZeroY classifier)).read (classifierRead classifier.yZero) =
        .bit (decide ((current.read (classifierRead classifier.leftRaw)).second.second.toNat =
          (current.read (classifierRead classifier.zero)).toNat)) := fun current =>
    Store.read_applyOp_output current (classifierZeroY classifier)
  constructor <;>
    simp only [classifierStore, rightRaw_leftRaw, xEqual_leftRaw, yEqual_leftRaw,
      yZero_leftRaw, xEqual_rightRaw, yEqual_rightRaw, yZero_rightRaw,
      yEqual_xEqual, yZero_xEqual, yZero_yEqual, leftRaw_zero, rightRaw_zero,
      xEqual_zero, yEqual_zero, leftWrite, rightWrite, xWrite, yWrite, zeroWrite, sourceRight, zero]
  all_goals
    simp only [unpack_x_toNat, unpack_y_toNat, zeroWord_toNat, Fin.ext_iff, Fin.val_zero]


end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
