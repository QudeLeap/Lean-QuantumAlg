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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def classifierBranchBodyRecord (whenTrue whenFalse : Circuit ctx ctx)
    (trueRecord : Store ctx → Store ctx × whenTrue.Path)
    (falseRecord : Store ctx → Store ctx × whenFalse.Path)
    (value : CShape.Value .bit) :
    Store ctx → Store ctx × (if value.toBool then whenTrue else whenFalse).Path :=
  match value with
  | .bit true => trueRecord
  | .bit false => falseRecord

private def classifierBranchRecord (input : CInputRef ctx .bit)
    (whenTrue whenFalse : Circuit ctx ctx)
    (trueRecord : Store ctx → Store ctx × whenTrue.Path)
    (falseRecord : Store ctx → Store ctx × whenFalse.Path) (store : Store ctx) :
    Store ctx × (classifierBranch input whenTrue whenFalse).Path :=
  let value := store.read input
  let result := classifierBranchBodyRecord whenTrue whenFalse trueRecord falseRecord value store
  (result.1, ⟨value, result.2⟩)

private theorem classifierBranchBodyRecord_store (whenTrue whenFalse : Circuit ctx ctx)
    (trueRecord : Store ctx → Store ctx × whenTrue.Path)
    (falseRecord : Store ctx → Store ctx × whenFalse.Path)
    (value : CShape.Value .bit) (store : Store ctx) :
    (classifierBranchBodyRecord whenTrue whenFalse trueRecord falseRecord value store).1 =
      if value.toBool then (trueRecord store).1 else (falseRecord store).1 := by
  cases value with
  | bit flag => cases flag <;> rfl

private theorem classifierBranchRecord_store (input : CInputRef ctx .bit)
    (whenTrue whenFalse : Circuit ctx ctx)
    (trueRecord : Store ctx → Store ctx × whenTrue.Path)
    (falseRecord : Store ctx → Store ctx × whenFalse.Path) (store : Store ctx) :
    (classifierBranchRecord input whenTrue whenFalse trueRecord falseRecord store).1 =
      if (store.read input).toBool then (trueRecord store).1 else (falseRecord store).1 := by
  exact classifierBranchBodyRecord_store whenTrue whenFalse trueRecord falseRecord
    (store.read input) store

private theorem classifierBranchRecord_execute (input : CInputRef ctx .bit)
    (whenTrue whenFalse : Circuit ctx ctx)
    (trueRecord : Store ctx → Store ctx × whenTrue.Path)
    (falseRecord : Store ctx → Store ctx × whenFalse.Path)
    (trueEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      whenTrue.execute Reference state = state.mapClassical (fun entry =>
        ((trueRecord entry.1).1, (entry.2, (trueRecord entry.1).2))))
    (falseEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      whenFalse.execute Reference state = state.mapClassical (fun entry =>
        ((falseRecord entry.1).1, (entry.2, (falseRecord entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (classifierBranch input whenTrue whenFalse).execute Reference state =
      state.mapClassical (fun entry =>
        ((classifierBranchRecord input whenTrue whenFalse trueRecord falseRecord entry.1).1,
          (entry.2,
            (classifierBranchRecord input whenTrue whenFalse
              trueRecord falseRecord entry.1).2))) := by
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
def dispatchRecord (classifier : Classifier ctx width) (arms : Case → Circuit ctx ctx)
    (records : ∀ selected, Store ctx → Store ctx × (arms selected).Path) :
    Store ctx → Store ctx × (dispatch classifier arms).Path :=
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
theorem dispatch_execute (classifier : Classifier ctx width) (arms : Case → Circuit ctx ctx)
    (records : ∀ selected, Store ctx → Store ctx × (arms selected).Path)
    (equations : ∀ selected (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (arms selected).execute Reference state = state.mapClassical (fun entry =>
        ((records selected entry.1).1, (entry.2, (records selected entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (dispatch classifier arms).execute Reference state = state.mapClassical (fun entry =>
      ((dispatchRecord classifier arms records entry.1).1,
        (entry.2, (dispatchRecord classifier arms records entry.1).2))) := by
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
theorem dispatchRecord_store (classifier : Classifier ctx width) (arms : Case → Circuit ctx ctx)
    (records : ∀ selected, Store ctx → Store ctx × (arms selected).Path) (store : Store ctx) :
    (dispatchRecord classifier arms records store).1 =
      (records (classifyStored classifier store) store).1 := by
  simp only [dispatchRecord, classifierBranchRecord_store]
  exact completeSelector_store (fun selected => (records selected store).1) _ _ _ _ _

/-- Actual classification supplies the original complete case without a caller branch promise. -/
theorem dispatchRecord_ready_store (classifier : Classifier ctx width)
    (arms : Case → Circuit ctx ctx)
    (records : ∀ selected, Store ctx → Store ctx × (arms selected).Path) (store : Store ctx)
    (left right : CShape.Value (PointShape width)) (ready : classifier.Ready store left right) :
    (dispatchRecord classifier arms records store).1 =
      (records (classifyValues left right) store).1 := by
  rw [dispatchRecord_store, classifyStored_eq_classifyValues classifier store left right ready]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
