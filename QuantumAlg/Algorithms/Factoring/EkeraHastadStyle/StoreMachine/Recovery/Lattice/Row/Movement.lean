/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual three-coordinate row copy

Three native word copies preserve the original ordered-copy aliasing contract.
The final target equals the initial source word for word, including width zero.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRows

open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Separation required to copy coordinates in order, including valid self-copy layouts. -/
structure PointCopySeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (source target : LatticeState.PointRefs ctx width) : Prop where
  sourceSecondAvoidsFirst :
    target.first.key ∉ (writeInput source.second).storageKeys
  sourceThirdAvoidsFirst :
    target.first.key ∉ (writeInput source.third).storageKeys
  sourceThirdAvoidsSecond :
    target.second.key ∉ (writeInput source.third).storageKeys
  targetFirstAvoidsSecond :
    target.second.key ∉ (writeInput target.first).storageKeys
  targetFirstAvoidsThird :
    target.third.key ∉ (writeInput target.first).storageKeys
  targetSecondAvoidsThird :
    target.third.key ∉ (writeInput target.second).storageKeys

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual native word copy used by each coordinate. -/
def copyOp (source target : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (writeInput source) target

/-- Copy the three actual source words into their ordered target destinations. -/
def pointCopy {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (copyOp source.first target.first))
    (.seq (BitWord.instruction (execution := model) (copyOp source.second target.second))
      (BitWord.instruction (execution := model) (copyOp source.third target.third)))

/-- The actual chronological store after the three copy instructions. -/
def pointCopyStore (source target : LatticeState.PointRefs ctx width)
    (store : Store ctx) : Store ctx :=
  ((store.applyOp (copyOp source.first target.first)).applyOp
    (copyOp source.second target.second)).applyOp (copyOp source.third target.third)

/-- Actual ordered copy stores and value-bearing selected operation paths. -/
def pointCopyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (store : Store ctx) : Store ctx × (pointCopy (model := model) source target).Path :=
  let first := BitWord.instructionStep (execution := model) (copyOp source.first target.first) store
  let second := BitWord.instructionStep (execution := model)
    (copyOp source.second target.second) first.1
  let third := BitWord.instructionStep (execution := model)
    (copyOp source.third target.third) second.1
  (third.1, (first.2, (second.2, third.2)))

theorem pointCopyStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (store : Store ctx) :
    (pointCopyStep (model := model) source target store).1 =
      pointCopyStore source target store := rfl

/-- Full actual execution preserves history and all quantum-reference correlations. -/
theorem pointCopy_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pointCopy (model := model) source target).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := pointCopyStep (model := model) source target entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [pointCopy, pointCopyStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem copy_read (source target : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (store.applyOp (copyOp source target)).read (writeInput target) =
      store.read (writeInput source) := by
  change (store.applyOp (copyOp source target)).read
    (.storage (copyOp source target).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change Resource.WordUnaryOpcode.eval .copy width (store.read (writeInput source)) = _
  rfl

/-- The final three target words are exactly the three original source words. -/
theorem pointCopy_reads (source target : LatticeState.PointRefs ctx width)
    (separation : PointCopySeparation source target) (store : Store ctx) :
    (pointCopyStore source target store).read (writeInput target.first) =
        store.read (writeInput source.first) ∧
      (pointCopyStore source target store).read (writeInput target.second) =
        store.read (writeInput source.second) ∧
      (pointCopyStore source target store).read (writeInput target.third) =
        store.read (writeInput source.third) := by
  unfold pointCopyStore
  refine ⟨?_, ?_, ?_⟩
  · rw [Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.third target.third) _
      separation.targetFirstAvoidsThird,
      Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.second target.second) _
        separation.targetFirstAvoidsSecond, copy_read]
  · rw [Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.third target.third) _
      separation.targetSecondAvoidsThird, copy_read,
      Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.first target.first) _
        separation.sourceSecondAvoidsFirst]
  · rw [copy_read,
      Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.second target.second) _
        separation.sourceThirdAvoidsSecond,
      Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.first target.first) _
        separation.sourceThirdAvoidsFirst]

/-- Exact actual word copying preserves the original integer raw point representation. -/
theorem pointCopy_correct (source target : LatticeState.PointRefs ctx width)
    (separation : PointCopySeparation source target) (store : Store ctx)
    (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store source value) :
    LatticeArithmetic.PointRawRepresents (pointCopyStore source target store) target value := by
  have reads := pointCopy_reads source target separation store
  refine ⟨?_, ?_, ?_⟩
  · rw [reads.1]; exact rep.1
  · rw [reads.2.1]; exact rep.2.1
  · rw [reads.2.2]; exact rep.2.2

/-- Every caller read outside the three actual target cells is preserved. -/
theorem pointCopy_callerFrame (source target : LatticeState.PointRefs ctx width)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (first : target.first.key ∉ other.storageKeys)
    (second : target.second.key ∉ other.storageKeys)
    (third : target.third.key ∉ other.storageKeys) :
    (pointCopyStore source target store).read other = store.read other := by
  unfold pointCopyStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.third target.third) other third,
    Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.second target.second) other second,
    Store.read_applyOp_of_not_mem_storageKeys _ (copyOp source.first target.first) other first]

/-- Independent selected instruction formula for one ordered three-word copy. -/
def pointCopyTrace {model : ExecutionModel} [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  List.replicate 3 (.classicalOperation
    (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)))

/-- Actual copy events equal the independent three-copy instruction formula. -/
theorem pointCopy_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (path : (pointCopy (model := model) source target).Path) :
    (pointCopy (model := model) source target).eventTrace path =
      pointCopyTrace (model := model) width := by
  change _ ++ (_ ++ _) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual native multiplicities are counted from the independent copy instruction formula. -/
theorem pointCopy_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (path : (pointCopy (model := model) source target).Path) :
    (pointCopy (model := model) source target).resourcePool path =
      ResourcePool.ofList (pointCopyTrace (model := model) width) := by
  change ResourcePool.ofList ((pointCopy (model := model) source target).eventTrace path) = _
  rw [pointCopy_events]

/-- The actual serial copy depth is exactly three at unit instruction duration. -/
theorem pointCopy_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (path : (pointCopy (model := model) source target).Path) :
    (pointCopy (model := model) source target).depth (fun _ => 1) path = 3 := rfl

/-- All actual row copies restore borrowed correlations jointly with external references. -/
theorem pointCopy_borrowedRestored {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pointCopy (model := model) source target).BorrowedRestored Reference state
      ((pointCopy (model := model) source target).execute Reference state) := by
  refine Circuit.borrowedRestored_seq
    (BitWord.instruction (execution := model) (copyOp source.first target.first)) _ state
    (Circuit.borrowedRestored_classical _ state) ?_
  exact Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _)
    (Circuit.borrowedRestored_classical _ _)

/-- All three actual copies visit the complete original caller context. -/
theorem pointCopy_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (path : (pointCopy (model := model) source target).Path) :
    (pointCopy (model := model) source target).visitedContexts path =
      List.replicate 3 ctx := rfl

/-- Resident space counts every supplied quantum dimension and classical cell during copying. -/
theorem pointCopy_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (path : (pointCopy (model := model) source target).Path) :
    (pointCopy (model := model) source target).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [pointCopy_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary storage retains its original roles during the entire actual copy. -/
theorem pointCopy_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (source target : LatticeState.PointRefs ctx width)
    (path : (pointCopy (model := model) source target).Path) :
    (pointCopy (model := model) source target).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [pointCopy_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRows
