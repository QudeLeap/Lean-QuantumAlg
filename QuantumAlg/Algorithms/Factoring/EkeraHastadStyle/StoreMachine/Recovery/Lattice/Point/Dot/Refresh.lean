/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot

/-!
# Actual lattice dot-product refresh

The first coordinate product overwrites the accumulator. The other two products are then
added through the same native multiply-accumulate circuit. Arbitrary initial
scratch is accepted; the five actual instructions require no extra allocation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeDotRefresh

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Caller-owned accumulator and product word for one dot-product refresh. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Writable cell for the dot value. -/
  dot : CWriteRef ctx (.unsignedWord width)
  dotRole : dot.toCStorageRef.role = .workspace
  /-- Writable cell for the product value. -/
  product : CWriteRef ctx (.unsignedWord width)
  productRole : product.toCStorageRef.role = .workspace

/-- Separation for overwriting and then accumulating one raw point dot product. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (left right : LatticeState.PointRefs ctx width) (refs : Refs ctx width) : Prop where
  dot : LatticeDot.PointDotSeparation left right refs.dot refs.product

/-- The initial product is written directly to the actual dot cell. -/
def firstProductOp (left right : LatticeState.PointRefs ctx width) (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx
    (.product (writeInput left.first) (writeInput right.first)) refs.dot

/-- Overwrite with the first product, then add the remaining two coordinate products. -/
def refreshInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (firstProductOp left right refs))
    (.seq (LatticeDot.coordinateAccumulate (model := model)
        (writeInput left.second) (writeInput right.second) refs.dot refs.product)
      (LatticeDot.coordinateAccumulate (model := model)
        (writeInput left.third) (writeInput right.third) refs.dot refs.product))

/-- The actual chronological five-write store update. -/
def refreshStore (left right : LatticeState.PointRefs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  LatticeDot.coordinateStore (writeInput left.third) (writeInput right.third)
    refs.dot refs.product
    (LatticeDot.coordinateStore (writeInput left.second) (writeInput right.second)
      refs.dot refs.product (store.applyOp (firstProductOp left right refs)))

/-- The three actual stages record one multiply followed by two multiply-add paths. -/
def refreshStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refreshInto (model := model) left right refs).Path :=
  let first := BitWord.instructionStep (execution := model) (firstProductOp left right refs) store
  let second := LatticeDot.coordinateStep (model := model)
    (writeInput left.second) (writeInput right.second) refs.dot refs.product first.1
  let third := LatticeDot.coordinateStep (model := model)
    (writeInput left.third) (writeInput right.third) refs.dot refs.product second.1
  (third.1, (first.2, (second.2, third.2)))

theorem refreshStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    (refreshStep (model := model) left right refs store).1 =
      refreshStore left right refs store := rfl

/-- The complete actual refresh execution preserves history and quantum-reference blocks. -/
theorem refreshInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) left right refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := refreshStep (model := model) left right refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [refreshInto, refreshStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, LatticeDot.coordinateAccumulate_execute,
    State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Only the caller's dot and product cells are changed by the actual refresh. -/
theorem refreshInto_callerFrame (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoidsDot : refs.dot.key ∉ other.storageKeys)
    (avoidsProduct : refs.product.key ∉ other.storageKeys) :
    (refreshStore left right refs store).read other = store.read other := by
  unfold refreshStore
  rw [LatticeDot.coordinateAccumulate_callerFrame _ _ _ _ _ other avoidsProduct avoidsDot,
    LatticeDot.coordinateAccumulate_callerFrame _ _ _ _ _ other avoidsProduct avoidsDot,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsDot]

/-- Actual dot refresh preserves both points and represents their exact integer dot product. -/
theorem refreshInto_correct (left right : LatticeState.PointRefs ctx width) (refs : Refs ctx width)
    (separation : Separation left right refs) (store : Store ctx)
    (leftValue rightValue : NumberTheory.IntegerPoint3)
    (leftRep : LatticeArithmetic.PointRawRepresents store left leftValue)
    (rightRep : LatticeArithmetic.PointRawRepresents store right rightValue) :
    RawSignedRepresents ((refreshStore left right refs store).read (writeInput refs.dot))
        (NumberTheory.integerPointDot leftValue rightValue) ∧
      LatticeArithmetic.PointRawRepresents (refreshStore left right refs store) left leftValue ∧
        LatticeArithmetic.PointRawRepresents
          (refreshStore left right refs store) right rightValue := by
  let first := store.applyOp (firstProductOp left right refs)
  let second := LatticeDot.coordinateStore (writeInput left.second) (writeInput right.second)
    refs.dot refs.product first
  have firstValue : RawSignedRepresents (first.read (writeInput refs.dot))
      (leftValue.1 * rightValue.1) := by
    change RawSignedRepresents ((store.applyOp (firstProductOp left right refs)).read
      (.storage (firstProductOp left right refs).outputRef.toCStorageRef)) _
    rw [Store.read_applyOp_output]
    exact rawSignedWordRepresents_mulLow _ _ _ _ leftRep.1 rightRep.1
  obtain ⟨leftFirst, rightFirst⟩ := LatticeDot.point_pair_preserved left right
    refs.dot refs.product
    separation.dot store first
    (fun other _ avoidsDot => Store.read_applyOp_of_not_mem_storageKeys _ _ other avoidsDot)
    leftValue rightValue leftRep rightRep
  have secondHolds := LatticeDot.coordinateAccumulate_correct
    (writeInput left.second) (writeInput right.second) refs.dot refs.product
    separation.dot.second first
  have secondValue := secondHolds.1 leftValue.2.1 rightValue.2.1 _
    leftFirst.2.1 rightFirst.2.1 firstValue
  obtain ⟨leftSecond, rightSecond⟩ := LatticeDot.point_pair_preserved left right
    refs.dot refs.product
    separation.dot first second secondHolds.2 leftValue rightValue leftFirst rightFirst
  have thirdHolds := LatticeDot.coordinateAccumulate_correct
    (writeInput left.third) (writeInput right.third) refs.dot refs.product
    separation.dot.third second
  have thirdValue := thirdHolds.1 leftValue.2.2 rightValue.2.2 _
    leftSecond.2.2 rightSecond.2.2 secondValue
  exact ⟨thirdValue, LatticeDot.point_pair_preserved left right refs.dot refs.product
    separation.dot store (refreshStore left right refs store)
    (fun other avoidsProduct avoidsDot =>
      refreshInto_callerFrame left right refs store other avoidsDot avoidsProduct)
    leftValue rightValue leftRep rightRep⟩

/-- The actual dot refresh restores all borrowed correlations without a state-output premise. -/
theorem refreshInto_borrowedRestored {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) left right refs).BorrowedRestored Reference state
      ((refreshInto (model := model) left right refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical _ state
  · exact Circuit.borrowedRestored_seq _ _ _
      (LatticeDot.coordinateAccumulate_borrowedRestored _ _ _ _ Reference _)
      (LatticeDot.coordinateAccumulate_borrowedRestored _ _ _ _ Reference _)

/-- Five actual selected instructions overwrite and accumulate the dot product. -/
theorem refreshInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width))] := by
  change _ ++ (_ ++ _) = _
  rw [BitWord.bitWord_instruction_eventTrace,
    LatticeDot.coordinateAccumulate_events, LatticeDot.coordinateAccumulate_events]
  rfl

/-- All five native operations remain sequentially dependent. -/
theorem refreshInto_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width)
    (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).depth (fun _ => 1) path = 5 := rfl

/-- The refresh visits only the complete original live context. -/
theorem refreshInto_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).visitedContexts path =
      [ctx, ctx, ctx, ctx, ctx] := rfl

/-- Resident space includes all original quantum systems and the two existing cells. -/
theorem refreshInto_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width)
    (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have same : visited = ctx := by
    simpa only [refreshInto_visited, List.mem_cons, List.not_mem_nil, or_false,
      or_self] using present
  subst visited
  exact le_rfl

/-- Auxiliary accounting uses the same supplied roles, with no temporary allocation. -/
theorem refreshInto_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width)
    (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have same : visited = ctx := by
    simpa only [refreshInto_visited, List.mem_cons, List.not_mem_nil, or_false,
      or_self] using present
  subst visited
  exact le_rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeDotRefresh
