/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Dispatch

/-!
# Complete state equations of actual complete-addition dispatch

The original nested branches select one supplied actual circuit using only
stored classifier bits. Component execution equations compose with the actual
selected sigma path and retain every quantum-reference matrix block.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {width : Nat}

private def classifierBranchBodyRecord (whenTrue whenFalse : Circuit model ctx ctx)
    (trueRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenTrue.Path)
    (falseRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenFalse.Path)
    (value : CShape.Value .bit) :
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (if value.toBool then whenTrue else whenFalse).Path :=
  match value with
  | .bit true => trueRecord
  | .bit false => falseRecord

private def classifierBranchRecord (input : CInputRef ctx .bit)
    (whenTrue whenFalse : Circuit model ctx ctx)
    (trueRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenTrue.Path)
    (falseRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenFalse.Path)
    (entry : Store ctx × model.HiddenState) :
    (Store ctx × model.HiddenState) ×
      (classifierBranch (model := model) input whenTrue whenFalse).Path :=
  let value := entry.1.read input
  let result := classifierBranchBodyRecord whenTrue whenFalse trueRecord falseRecord value entry
  (result.1, ⟨value, result.2⟩)

private theorem classifierBranchBodyRecord_store (whenTrue whenFalse : Circuit model ctx ctx)
    (trueRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenTrue.Path)
    (falseRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenFalse.Path)
    (value : CShape.Value .bit) (entry : Store ctx × model.HiddenState) :
    (classifierBranchBodyRecord whenTrue whenFalse trueRecord falseRecord value entry).1.1 =
      if value.toBool then (trueRecord entry).1.1 else (falseRecord entry).1.1 := by
  cases value with
  | bit flag => cases flag <;> rfl

private theorem classifierBranchRecord_store (input : CInputRef ctx .bit)
    (whenTrue whenFalse : Circuit model ctx ctx)
    (trueRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenTrue.Path)
    (falseRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenFalse.Path)
    (entry : Store ctx × model.HiddenState) :
    (classifierBranchRecord input whenTrue whenFalse trueRecord falseRecord entry).1.1 =
      if (entry.1.read input).toBool then (trueRecord entry).1.1
      else (falseRecord entry).1.1 := by
  exact classifierBranchBodyRecord_store whenTrue whenFalse trueRecord falseRecord
    (entry.1.read input) entry

private theorem classifierBranchRecord_execute (input : CInputRef ctx .bit)
    (whenTrue whenFalse : Circuit model ctx ctx)
    (trueRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenTrue.Path)
    (falseRecord : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × whenFalse.Path)
    (trueEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      whenTrue.execute Reference state = state.mapClassical (fun entry =>
        let result := trueRecord (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (falseEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      whenFalse.execute Reference state = state.mapClassical (fun entry =>
        let result := falseRecord (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (classifierBranch (model := model) input whenTrue whenFalse).execute Reference state =
      state.mapClassical (fun entry =>
        let result := classifierBranchRecord input whenTrue whenFalse
          trueRecord falseRecord (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_branch_mapClassical input
    (fun value => if value.toBool then whenTrue else whenFalse)
    (classifierBranchBodyRecord whenTrue whenFalse trueRecord falseRecord)
  intro value reference history _ initial
  cases value with
  | bit flag =>
    cases flag
    · exact falseEquation reference initial
    · exact trueEquation reference initial

/-- The actual nested branches record their real selected arm and every real predicate value. -/
def dispatchRecord (classifier : Classifier ctx width) (arms : Case → Circuit model ctx ctx)
    (records : ∀ selected, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (arms selected).Path) :
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (dispatch classifier arms).Path :=
  classifierBranchRecord (.first (classifierRead classifier.leftRaw)) (arms .leftInfinity) _
    (records .leftInfinity)
    (classifierBranchRecord (.first (classifierRead classifier.rightRaw)) (arms .rightInfinity) _
      (records .rightInfinity)
      (classifierBranchRecord (classifierRead classifier.xEqual) _ (arms .generic)
        (classifierBranchRecord (classifierRead classifier.yEqual) _ (arms .vertical)
          (classifierBranchRecord (classifierRead classifier.yZero)
            (arms .vertical) (arms .doubling) (records .vertical) (records .doubling))
          (records .vertical)) (records .generic)))

/-- Actual full-state arm equations give the complete actual branch-tree execution. -/
theorem dispatch_execute (classifier : Classifier ctx width)
    (arms : Case → Circuit model ctx ctx)
    (records : ∀ selected, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (arms selected).Path)
    (equations : ∀ selected (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (arms selected).execute Reference state = state.mapClassical (fun entry =>
        let result := records selected (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (dispatch (model := model) classifier arms).execute Reference state =
      state.mapClassical (fun entry =>
      let result := dispatchRecord classifier arms records (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  unfold dispatch dispatchRecord
  apply classifierBranchRecord_execute
  · exact equations .leftInfinity
  · intro reference history _ initial
    apply classifierBranchRecord_execute
    · exact equations .rightInfinity
    · intro reference' history' _ initial'
      apply classifierBranchRecord_execute
      · intro reference'' history'' _ initial''
        apply classifierBranchRecord_execute
        · intro reference''' history''' _ initial'''
          exact classifierBranchRecord_execute _ _ _ _ _
            (equations .vertical) (equations .doubling) reference''' initial'''
        · exact equations .vertical
      · exact equations .generic

private theorem completeSelector_store (selectedStore : Case → Store ctx)
    (leftInfinity rightInfinity xEqual yEqual yZero : Bool) :
    (if leftInfinity then selectedStore .leftInfinity
      else if rightInfinity then selectedStore .rightInfinity
      else if xEqual then
        if yEqual then
          if yZero then selectedStore .vertical else selectedStore .doubling
        else selectedStore .vertical
      else selectedStore .generic) =
    selectedStore (if leftInfinity then .leftInfinity
      else if rightInfinity then .rightInfinity
      else if xEqual then
        if yEqual then if yZero then .vertical else .doubling else .vertical
      else .generic) := by
  cases leftInfinity <;> cases rightInfinity <;> cases xEqual <;> cases yEqual <;>
    cases yZero <;> rfl

/-- The final store is exactly the chosen actual arm's result on the incoming store. -/
theorem dispatchRecord_store (classifier : Classifier ctx width)
    (arms : Case → Circuit model ctx ctx)
    (records : ∀ selected, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (arms selected).Path)
    (entry : Store ctx × model.HiddenState) :
    (dispatchRecord classifier arms records entry).1.1 =
      (records (classifyStored classifier entry.1) entry).1.1 := by
  simp only [dispatchRecord, classifierBranchRecord_store]
  exact completeSelector_store (fun selected => (records selected entry).1.1) _ _ _ _ _

/-- Actual classification supplies the original complete case without a caller branch promise. -/
theorem dispatchRecord_ready_store (classifier : Classifier ctx width)
    (arms : Case → Circuit model ctx ctx)
    (records : ∀ selected, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (arms selected).Path)
    (entry : Store ctx × model.HiddenState)
    (left right : CShape.Value (PointShape width)) (ready : classifier.Ready entry.1 left right) :
    (dispatchRecord classifier arms records entry).1.1 =
      (records (classifyValues left right) entry).1.1 := by
  rw [dispatchRecord_store, classifyStored_eq_classifyValues classifier entry.1 left right ready]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
