/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot.Coordinate

/-!
# Actual three-coordinate dot accumulation

Three native multiply-add pairs reuse the same product word and accumulator.
Signed values are represented modulo their original width. Full execution,
caller reads, native operations and borrowed correlations use the same circuit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeDot

open ClassicalRoutines.NumberTheory.SignedWord
open Execution
open LatticeArithmetic (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Separation for three sequential multiply-accumulate steps sharing one
accumulator and one product scratch word. -/
structure PointDotSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) : Prop where
  first : CoordinateAccumulateSeparation
    (LatticeState.coordinateInput left.first)
    (LatticeState.coordinateInput right.first) accumulator product
  second : CoordinateAccumulateSeparation
    (LatticeState.coordinateInput left.second)
    (LatticeState.coordinateInput right.second) accumulator product
  third : CoordinateAccumulateSeparation
    (LatticeState.coordinateInput left.third)
    (LatticeState.coordinateInput right.third) accumulator product

/-- Add the three actual coordinate products to the original accumulator. -/
def pointDotAccumulate {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (coordinateAccumulate (model := model)
      (writeInput left.first) (writeInput right.first) accumulator product)
    (.seq (coordinateAccumulate (model := model)
        (writeInput left.second) (writeInput right.second)
        accumulator product)
      (coordinateAccumulate (model := model)
        (writeInput left.third) (writeInput right.third) accumulator product))

/-- The six chronological native updates on the actual store. -/
def pointStore (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  coordinateStore (writeInput left.third) (writeInput right.third) accumulator product
    (coordinateStore (writeInput left.second) (writeInput right.second) accumulator product
      (coordinateStore (writeInput left.first) (writeInput right.first) accumulator product store))

/-- The actual three coordinate updates and their recorded selected paths. -/
def pointStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (pointDotAccumulate (model := model) left right accumulator product).Path :=
  let first := coordinateStep (model := model)
    (writeInput left.first) (writeInput right.first) accumulator product store
  let second := coordinateStep (model := model)
    (writeInput left.second) (writeInput right.second) accumulator product first.1
  let third := coordinateStep (model := model)
    (writeInput left.third) (writeInput right.third) accumulator product second.1
  (third.1, (first.2, (second.2, third.2)))

lemma pointStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (pointStep (model := model) left right accumulator product store).1 =
      pointStore left right accumulator product store := rfl

/-- The complete actual interpreter retains each incoming history and quantum-reference block. -/
lemma pointDotAccumulate_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pointDotAccumulate (model := model) left right accumulator product).execute environment
      Reference state = state.mapClassical (fun entry =>
        let actual := pointStep (model := model) left right accumulator product entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [pointDotAccumulate, pointStep, Circuit.execute_seq,
    coordinateAccumulate_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every caller read outside the two reused cells is unchanged. -/
lemma pointDotAccumulate_callerFrame (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsProduct : product.key ∉ other.storageKeys)
    (avoidsAccumulator : accumulator.key ∉ other.storageKeys) :
    (pointStore left right accumulator product store).read other = store.read other := by
  unfold pointStore
  rw [coordinateAccumulate_callerFrame _ _ _ _ _ other avoidsProduct avoidsAccumulator,
    coordinateAccumulate_callerFrame _ _ _ _ _ other avoidsProduct avoidsAccumulator,
    coordinateAccumulate_callerFrame _ _ _ _ _ other avoidsProduct avoidsAccumulator]

private lemma point_pair_preserved (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (separation : PointDotSeparation left right accumulator product) (before after : Store ctx)
    (frame : ∀ {shape : CShape} (other : CInputRef ctx shape),
      product.key ∉ other.storageKeys → accumulator.key ∉ other.storageKeys →
        after.read other = before.read other)
    (leftPoint rightPoint : NumberTheory.IntegerPoint3)
    (leftRep : LatticeArithmetic.PointRawRepresents before left leftPoint)
    (rightRep : LatticeArithmetic.PointRawRepresents before right rightPoint) :
    LatticeArithmetic.PointRawRepresents after left leftPoint ∧
      LatticeArithmetic.PointRawRepresents after right rightPoint := by
  rcases leftRep with ⟨leftFirst, leftSecond, leftThird⟩
  rcases rightRep with ⟨rightFirst, rightSecond, rightThird⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [frame (writeInput left.first) separation.first.leftAvoidsProduct
      separation.first.leftAvoidsAccumulator]
    exact leftFirst
  · rw [frame (writeInput left.second) separation.second.leftAvoidsProduct
      separation.second.leftAvoidsAccumulator]
    exact leftSecond
  · rw [frame (writeInput left.third) separation.third.leftAvoidsProduct
      separation.third.leftAvoidsAccumulator]
    exact leftThird
  · rw [frame (writeInput right.first) separation.first.rightAvoidsProduct
      separation.first.rightAvoidsAccumulator]
    exact rightFirst
  · rw [frame (writeInput right.second) separation.second.rightAvoidsProduct
      separation.second.rightAvoidsAccumulator]
    exact rightSecond
  · rw [frame (writeInput right.third) separation.third.rightAvoidsProduct
      separation.third.rightAvoidsAccumulator]
    exact rightThird

/-- The actual accumulator represents its original integer plus the exact point dot product. -/
lemma pointDotAccumulate_correct (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (separation : PointDotSeparation left right accumulator product) (store : Store ctx)
    (accumulatorValue : Int) (leftPoint rightPoint : NumberTheory.IntegerPoint3)
    (accumulatorRep : RawSignedRepresents (store.read (writeInput accumulator)) accumulatorValue)
    (leftRep : LatticeArithmetic.PointRawRepresents store left leftPoint)
    (rightRep : LatticeArithmetic.PointRawRepresents store right rightPoint) :
    RawSignedRepresents ((pointStore left right accumulator product store).read
      (writeInput accumulator))
        (accumulatorValue + NumberTheory.integerPointDot leftPoint rightPoint) := by
  let first := coordinateStore (writeInput left.first) (writeInput right.first)
    accumulator product store
  let second := coordinateStore (writeInput left.second) (writeInput right.second)
    accumulator product first
  have firstHolds := coordinateAccumulate_correct (writeInput left.first) (writeInput right.first)
    accumulator product separation.first store
  have firstValue := firstHolds.1 leftPoint.1 rightPoint.1 accumulatorValue
    leftRep.1 rightRep.1 accumulatorRep
  obtain ⟨leftFirst, rightFirst⟩ := point_pair_preserved left right accumulator product separation
    store first firstHolds.2 leftPoint rightPoint leftRep rightRep
  have secondHolds := coordinateAccumulate_correct (writeInput left.second)
    (writeInput right.second) accumulator product separation.second first
  have secondValue := secondHolds.1 leftPoint.2.1 rightPoint.2.1 _
    leftFirst.2.1 rightFirst.2.1 firstValue
  obtain ⟨leftSecond, rightSecond⟩ := point_pair_preserved left right accumulator product separation
    first second secondHolds.2 leftPoint rightPoint leftFirst rightFirst
  have thirdHolds := coordinateAccumulate_correct (writeInput left.third) (writeInput right.third)
    accumulator product separation.third second
  have thirdValue := thirdHolds.1 leftPoint.2.2 rightPoint.2.2 _
    leftSecond.2.2 rightSecond.2.2 secondValue
  have sum : accumulatorValue + NumberTheory.integerPointDot leftPoint rightPoint =
      accumulatorValue + leftPoint.1 * rightPoint.1 + leftPoint.2.1 * rightPoint.2.1 +
        leftPoint.2.2 * rightPoint.2.2 := by
    simp only [NumberTheory.integerPointDot]
    ring
  rw [sum]
  exact thirdValue

/-- A zero initial accumulator yields the exact raw dot product in the final actual store. -/
lemma pointDot_value_of_zero {leftPoint rightPoint : NumberTheory.IntegerPoint3}
    (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (separation : PointDotSeparation left right accumulator product) (store : Store ctx)
    (accumulatorZero : RawSignedRepresents (store.read (writeInput accumulator)) 0)
    (leftRepresents : LatticeArithmetic.PointRawRepresents store left leftPoint)
    (rightRepresents : LatticeArithmetic.PointRawRepresents store right rightPoint) :
    RawSignedRepresents ((pointStore left right accumulator product store).read
      (writeInput accumulator)) (NumberTheory.integerPointDot leftPoint rightPoint) := by
  simpa only [Int.zero_add] using pointDotAccumulate_correct left right accumulator product
    separation store 0 leftPoint rightPoint accumulatorZero leftRepresents rightRepresents

/-- The actual zero-accumulator dot circuit also computes the point's squared norm. -/
lemma pointSquaredNorm_value_of_zero {pointValue : NumberTheory.IntegerPoint3}
    (point : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (separation : PointDotSeparation point point accumulator product) (store : Store ctx)
    (accumulatorZero : RawSignedRepresents (store.read (writeInput accumulator)) 0)
    (pointRepresents : LatticeArithmetic.PointRawRepresents store point pointValue) :
    RawSignedRepresents ((pointStore point point accumulator product store).read
      (writeInput accumulator)) (NumberTheory.integerPointSquaredNorm pointValue : Int) := by
  rw [← NumberTheory.integerPointDot_self]
  exact pointDot_value_of_zero point point accumulator product separation store
    accumulatorZero pointRepresents pointRepresents

/-- The actual dot circuit jointly restores all borrowed classical and quantum correlations. -/
lemma pointDotAccumulate_borrowedRestored
    {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pointDotAccumulate (model := model) left right accumulator product).BorrowedRestored
      Reference state
      ((pointDotAccumulate (model := model) left right accumulator product).execute environment
        Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact coordinateAccumulate_borrowedRestored _ _ _ _ Reference state
  · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
      (coordinateAccumulate_borrowedRestored _ _ _ _ Reference _)
      (coordinateAccumulate_borrowedRestored _ _ _ _ Reference _)

/-- Exact six native instructions in every actual dot-accumulation path. -/
lemma pointDotAccumulate_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (path : (pointDotAccumulate (model := model) left right accumulator product).Path) :
    (pointDotAccumulate (model := model) left right accumulator product).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .add width))] := by
  change _ ++ (_ ++ _) = _
  rw [coordinateAccumulate_events, coordinateAccumulate_events,
    coordinateAccumulate_events]
  rfl

/-- All six dependent native instructions contribute their unit duration. -/
lemma pointDotAccumulate_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (path : (pointDotAccumulate (model := model) left right accumulator product).Path) :
    (pointDotAccumulate (model := model) left right accumulator product).depth
      (fun _ => 1) path = 6 := rfl

/-- Reusing both cells leaves the complete visited context unchanged. -/
lemma pointDotAccumulate_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (path : (pointDotAccumulate (model := model) left right accumulator product).Path) :
    (pointDotAccumulate (model := model) left right accumulator product).visitedContexts path =
      [ctx, ctx, ctx, ctx, ctx, ctx] := rfl

/-- Resident space counts the two reused cells and all original quantum systems. -/
lemma pointDotAccumulate_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (path : (pointDotAccumulate (model := model) left right accumulator product).Path) :
    (pointDotAccumulate (model := model) left right accumulator product).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have same : visited = ctx := by
    simpa only [pointDotAccumulate_visited, List.mem_cons, List.not_mem_nil, or_false,
      or_self] using present
  subst visited
  exact le_rfl

/-- Auxiliary space counts the original roles without any additional workspace. -/
lemma pointDotAccumulate_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (path : (pointDotAccumulate (model := model) left right accumulator product).Path) :
    (pointDotAccumulate (model := model) left right accumulator product).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have same : visited = ctx := by
    simpa only [pointDotAccumulate_visited, List.mem_cons, List.not_mem_nil, or_false,
      or_self] using present
  subst visited
  exact le_rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeDot
