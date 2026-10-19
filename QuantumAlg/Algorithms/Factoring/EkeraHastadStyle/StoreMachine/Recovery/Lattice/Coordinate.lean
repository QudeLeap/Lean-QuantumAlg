/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.State

/-!
# Actual lattice row arithmetic

A coordinate reduction performs one low-word multiplication and one wrapping
subtraction. Three such reductions reuse one product word. The same native
circuit determines the complete execution, modular readout, caller frame,
and event trace; no extra quantum or classical storage is allocated.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeArithmetic

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Structural read of one writable coordinate. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Separation needed by one multiply-then-subtract coordinate update. -/
structure CoordinateReduceSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) : Prop where
  coefficientAvoidsProduct :
    product.toCStorageRef.key ∉ coefficient.storageKeys
  sourceAvoidsProduct : product.toCStorageRef.key ∉ source.storageKeys
  targetAvoidsProduct :
    product.toCStorageRef.key ∉ (writeInput target).storageKeys
  coefficientAvoidsTarget : target.toCStorageRef.key ∉ coefficient.storageKeys
  sourceAvoidsTarget : target.toCStorageRef.key ∉ source.storageKeys
  productAvoidsTarget :
    target.toCStorageRef.key ∉ (writeInput product).storageKeys

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual low-word multiplication writes the shared product cell. -/
def coordinateProductOp (coefficient source : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx (.product coefficient source) product

/-- The actual subtraction reads the target and the newly written product. -/
def coordinateSubtractOp (target product : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx (.product (writeInput target) (writeInput product)) target

/-- Replace the target by target minus coefficient times source modulo the raw width. -/
def coordinateReduce {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model)
    (coordinateProductOp coefficient source product))
    (BitWord.instruction (execution := model) (coordinateSubtractOp target product))

/-- The two actual instruction updates on the classical store. -/
def coordinateStore (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  (store.applyOp (coordinateProductOp coefficient source product)).applyOp
    (coordinateSubtractOp target product)

/-- The complete incoming quantum-reference blocks follow these actual store updates. -/
def coordinateStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (coordinateReduce (model := model) coefficient source target product).Path :=
  let multiplied := BitWord.instructionStep (execution := model)
    (coordinateProductOp coefficient source product) store
  let subtracted := BitWord.instructionStep (execution := model)
    (coordinateSubtractOp target product) multiplied.1
  (subtracted.1, (multiplied.2, subtracted.2))

lemma coordinateStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (coordinateStep (model := model) coefficient source target product store).1 =
      coordinateStore coefficient source target product store := rfl

lemma coordinateReduce_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : Execution.State ctx Reference (model.HiddenState × History)) :
    (coordinateReduce (model := model) coefficient source target product).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        let actual := coordinateStep (model := model) coefficient source target product entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [coordinateReduce, coordinateStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every actual coordinate path contains exactly the native multiply and subtraction. -/
lemma coordinateReduce_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width))
    (path : (coordinateReduce (model := model) coefficient source target product).Path) :
    (coordinateReduce (model := model) coefficient source target product).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .sub width))] := by
  change (BitWord.instruction (execution := model)
      (coordinateProductOp coefficient source product)).eventTrace path.1 ++
    (BitWord.instruction (execution := model)
      (coordinateSubtractOp target product)).eventTrace path.2 = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Reads outside the two actual writes are preserved, with no operand-separation premise. -/
lemma coordinateReduce_callerFrame
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsProduct : product.key ∉ other.storageKeys)
    (avoidsTarget : target.key ∉ other.storageKeys) :
    (coordinateStore coefficient source target product store).read other = store.read other := by
  unfold coordinateStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsTarget,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsProduct]

/-- Actual coordinate readout and all caller reads outside the two writes. -/
def CoordinateReduceRelation (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width))
    (before after : Store ctx) : Prop :=
  (∀ coefficientValue sourceValue targetValue : Int,
    RawSignedRepresents (before.read coefficient) coefficientValue →
      RawSignedRepresents (before.read source) sourceValue →
        RawSignedRepresents (before.read (writeInput target)) targetValue →
          RawSignedRepresents (after.read (writeInput target))
            (targetValue - coefficientValue * sourceValue)) ∧
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      product.key ∉ other.storageKeys → target.key ∉ other.storageKeys →
        after.read other = before.read other)

/-- The two real updates implement signed subtraction of the product modulo the word width. -/
lemma coordinateReduce_correct (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width))
    (separation : CoordinateReduceSeparation coefficient source target product)
    (store : Store ctx) :
    CoordinateReduceRelation coefficient source target product store
      (coordinateStore coefficient source target product store) := by
  refine ⟨?_, coordinateReduce_callerFrame coefficient source target product store⟩
  intro coefficientValue sourceValue targetValue coefficientRep sourceRep targetRep
  let multiplied := store.applyOp (coordinateProductOp coefficient source product)
  have productRep : RawSignedRepresents (multiplied.read (writeInput product))
      (coefficientValue * sourceValue) := by
    change RawSignedRepresents
      ((store.applyOp (coordinateProductOp coefficient source product)).read
        (.storage (coordinateProductOp coefficient source product).outputRef.toCStorageRef)) _
    rw [Store.read_applyOp_output]
    exact rawSignedWordRepresents_mulLow (store.read coefficient) (store.read source)
      coefficientValue sourceValue coefficientRep sourceRep
  have targetFrame : multiplied.read (writeInput target) = store.read (writeInput target) :=
    Store.read_applyOp_of_not_mem_storageKeys store
      (coordinateProductOp coefficient source product) (writeInput target)
      separation.targetAvoidsProduct
  change RawSignedRepresents
    ((multiplied.applyOp (coordinateSubtractOp target product)).read
      (.storage (coordinateSubtractOp target product).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  change RawSignedRepresents
    (Resource.WordBinaryOpcode.eval .sub width
      (.product (multiplied.read (writeInput target)) (multiplied.read (writeInput product)))) _
  apply rawSignedWordRepresents_sub _ _ targetValue (coefficientValue * sourceValue)
  · rw [targetFrame]
    exact targetRep
  · exact productRep

/-- Raw modular representation of the three independently stored coordinates. -/
def PointRawRepresents (store : Store ctx) (refs : LatticeState.PointRefs ctx width)
    (point : NumberTheory.IntegerPoint3) : Prop :=
  RawSignedRepresents (store.read (writeInput refs.first)) point.1 ∧
    RawSignedRepresents (store.read (writeInput refs.second)) point.2.1 ∧
      RawSignedRepresents (store.read (writeInput refs.third)) point.2.2

/-- Separation for the sequential reduction of three target coordinates using
one shared product scratch word. -/
structure PointReduceSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) : Prop where
  first : CoordinateReduceSeparation coefficient
    (LatticeState.coordinateInput source.first) target.first product
  second : CoordinateReduceSeparation coefficient
    (LatticeState.coordinateInput source.second) target.second product
  third : CoordinateReduceSeparation coefficient
    (LatticeState.coordinateInput source.third) target.third product
  sourceSecondAvoidsFirstTarget :
    target.first.toCStorageRef.key ∉ (LatticeState.coordinateInput source.second).storageKeys
  sourceThirdAvoidsFirstTarget :
    target.first.toCStorageRef.key ∉ (LatticeState.coordinateInput source.third).storageKeys
  sourceThirdAvoidsSecondTarget :
    target.second.toCStorageRef.key ∉ (LatticeState.coordinateInput source.third).storageKeys
  targetFirstAvoidsSecond :
    target.second.toCStorageRef.key ∉ (writeInput target.first).storageKeys
  targetFirstAvoidsThird :
    target.third.toCStorageRef.key ∉ (writeInput target.first).storageKeys
  targetSecondAvoidsFirst :
    target.first.toCStorageRef.key ∉ (writeInput target.second).storageKeys
  targetSecondAvoidsThird :
    target.third.toCStorageRef.key ∉ (writeInput target.second).storageKeys
  targetThirdAvoidsFirst :
    target.first.toCStorageRef.key ∉ (writeInput target.third).storageKeys
  targetThirdAvoidsSecond :
    target.second.toCStorageRef.key ∉ (writeInput target.third).storageKeys

/-- Three real coordinate updates reuse the same caller-owned product word. -/
def pointReduce {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (coordinateReduce (model := model) coefficient
    (writeInput source.first) target.first product)
    (.seq (coordinateReduce (model := model) coefficient
      (writeInput source.second) target.second product)
      (coordinateReduce (model := model) coefficient
        (writeInput source.third) target.third product))

/-- The three chronological native coordinate updates of the actual point circuit. -/
def pointStore (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  coordinateStore coefficient (writeInput source.third) target.third product
    (coordinateStore coefficient (writeInput source.second) target.second product
      (coordinateStore coefficient (writeInput source.first) target.first product store))

/-- Actual intermediate records follow the same three chronological store updates. -/
def pointStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (pointReduce (model := model) coefficient source target product).Path :=
  let first := coordinateStep (model := model) coefficient
    (writeInput source.first) target.first product store
  let second := coordinateStep (model := model) coefficient
    (writeInput source.second) target.second product first.1
  let third := coordinateStep (model := model) coefficient
    (writeInput source.third) target.third product second.1
  (third.1, (first.2, (second.2, third.2)))

lemma pointStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (pointStep (model := model) coefficient source target product store).1 =
      pointStore coefficient source target product store := rfl

/-- The complete point execution retains every incoming quantum-reference block and history. -/
lemma pointReduce_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : Execution.State ctx Reference (model.HiddenState × History)) :
    (pointReduce (model := model) coefficient source target product).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        let actual := pointStep (model := model) coefficient source target product entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [pointReduce, pointStep, Circuit.execute_seq, coordinateReduce_execute,
    State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The point path contains the same two actual word instructions for each of three coordinates. -/
lemma pointReduce_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width))
    (path : (pointReduce (model := model) coefficient source target product).Path) :
    (pointReduce (model := model) coefficient source target product).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .sub width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .sub width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .sub width))] := by
  change _ ++ (_ ++ _) = _
  rw [coordinateReduce_events, coordinateReduce_events, coordinateReduce_events]
  rfl

/-- Actual point arithmetic and preservation of reads outside the four writable cells. -/
def PointReduceRelation (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) (before after : Store ctx) : Prop :=
  (∀ (coefficientValue : Int) (sourcePoint targetPoint : NumberTheory.IntegerPoint3),
    RawSignedRepresents (before.read coefficient) coefficientValue →
      PointRawRepresents before source sourcePoint →
        PointRawRepresents before target targetPoint →
          PointRawRepresents after target (targetPoint.sub (sourcePoint.smul coefficientValue))) ∧
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      product.key ∉ other.storageKeys → target.first.key ∉ other.storageKeys →
        target.second.key ∉ other.storageKeys → target.third.key ∉ other.storageKeys →
          after.read other = before.read other)

/-- All three represented integer coordinates undergo the same source row subtraction. -/
lemma pointReduce_correct (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width))
    (separation : PointReduceSeparation coefficient source target product) (store : Store ctx) :
    PointReduceRelation coefficient source target product store
      (pointStore coefficient source target product store) := by
  let first := coordinateStore coefficient (writeInput source.first) target.first product
  let second := coordinateStore coefficient (writeInput source.second) target.second product
  let third := coordinateStore coefficient (writeInput source.third) target.third product
  have firstHolds := coordinateReduce_correct coefficient (writeInput source.first)
    target.first product separation.first store
  have secondHolds := coordinateReduce_correct coefficient (writeInput source.second)
    target.second product separation.second (first store)
  have thirdHolds := coordinateReduce_correct coefficient (writeInput source.third)
    target.third product separation.third (second (first store))
  refine ⟨?_, ?_⟩
  · intro coefficientValue sourcePoint targetPoint coefficientRep sourceRep targetRep
    rcases sourceRep with ⟨sourceFirstRep, sourceSecondRep, sourceThirdRep⟩
    rcases targetRep with ⟨targetFirstRep, targetSecondRep, targetThirdRep⟩
    have coefficientAfterFirst :
        RawSignedRepresents ((first store).read coefficient) coefficientValue := by
      have frame := firstHolds.2 coefficient
        separation.first.coefficientAvoidsProduct separation.first.coefficientAvoidsTarget
      change (first store).read coefficient = store.read coefficient at frame
      rw [frame]
      exact coefficientRep
    have sourceSecondAfterFirst :
        RawSignedRepresents
          ((first store).read (LatticeState.coordinateInput source.second))
          sourcePoint.2.1 := by
      have frame := firstHolds.2 (LatticeState.coordinateInput source.second)
        separation.second.sourceAvoidsProduct separation.sourceSecondAvoidsFirstTarget
      change (first store).read (LatticeState.coordinateInput source.second) =
        store.read (LatticeState.coordinateInput source.second) at frame
      rw [frame]
      exact sourceSecondRep
    have targetSecondAfterFirst :
        RawSignedRepresents ((first store).read (writeInput target.second))
          targetPoint.2.1 := by
      have frame := firstHolds.2 (writeInput target.second)
        separation.second.targetAvoidsProduct separation.targetSecondAvoidsFirst
      change (first store).read (writeInput target.second) =
        store.read (writeInput target.second) at frame
      rw [frame]
      exact targetSecondRep
    have firstAfterFirst :
        RawSignedRepresents ((first store).read (writeInput target.first))
          (targetPoint.1 - coefficientValue * sourcePoint.1) :=
      firstHolds.1 coefficientValue sourcePoint.1 targetPoint.1 coefficientRep
        sourceFirstRep targetFirstRep
    have secondAfterSecond :
        RawSignedRepresents
          ((second (first store)).read (writeInput target.second))
          (targetPoint.2.1 - coefficientValue * sourcePoint.2.1) :=
      secondHolds.1 coefficientValue sourcePoint.2.1 targetPoint.2.1
        coefficientAfterFirst sourceSecondAfterFirst targetSecondAfterFirst
    have coefficientAfterSecond :
        RawSignedRepresents
          ((second (first store)).read coefficient) coefficientValue := by
      have frame := secondHolds.2 coefficient
        separation.second.coefficientAvoidsProduct separation.second.coefficientAvoidsTarget
      change (second (first store)).read coefficient =
        (first store).read coefficient at frame
      rw [frame]
      exact coefficientAfterFirst
    have sourceThirdAfterFirst :
        RawSignedRepresents
          ((first store).read (LatticeState.coordinateInput source.third))
          sourcePoint.2.2 := by
      have frame := firstHolds.2 (LatticeState.coordinateInput source.third)
        separation.third.sourceAvoidsProduct separation.sourceThirdAvoidsFirstTarget
      change (first store).read (LatticeState.coordinateInput source.third) =
        store.read (LatticeState.coordinateInput source.third) at frame
      rw [frame]
      exact sourceThirdRep
    have sourceThirdAfterSecond :
        RawSignedRepresents
          ((second (first store)).read
            (LatticeState.coordinateInput source.third)) sourcePoint.2.2 := by
      have frame := secondHolds.2 (LatticeState.coordinateInput source.third)
        separation.third.sourceAvoidsProduct separation.sourceThirdAvoidsSecondTarget
      change (second (first store)).read
          (LatticeState.coordinateInput source.third) =
        (first store).read (LatticeState.coordinateInput source.third) at frame
      rw [frame]
      exact sourceThirdAfterFirst
    have targetThirdAfterFirst :
        RawSignedRepresents ((first store).read (writeInput target.third))
          targetPoint.2.2 := by
      have frame := firstHolds.2 (writeInput target.third)
        separation.third.targetAvoidsProduct separation.targetThirdAvoidsFirst
      change (first store).read (writeInput target.third) =
        store.read (writeInput target.third) at frame
      rw [frame]
      exact targetThirdRep
    have targetThirdAfterSecond :
        RawSignedRepresents
          ((second (first store)).read (writeInput target.third))
          targetPoint.2.2 := by
      have frame := secondHolds.2 (writeInput target.third)
        separation.third.targetAvoidsProduct separation.targetThirdAvoidsSecond
      change (second (first store)).read (writeInput target.third) =
        (first store).read (writeInput target.third) at frame
      rw [frame]
      exact targetThirdAfterFirst
    have thirdAfterThird :
        RawSignedRepresents
          ((third (second (first store))).read
            (writeInput target.third))
          (targetPoint.2.2 - coefficientValue * sourcePoint.2.2) :=
      thirdHolds.1 coefficientValue sourcePoint.2.2 targetPoint.2.2
        coefficientAfterSecond sourceThirdAfterSecond targetThirdAfterSecond
    unfold PointRawRepresents
    refine ⟨?_, ?_, thirdAfterThird⟩
    · change RawSignedRepresents
        ((third (second (first store))).read
          (writeInput target.first))
        (targetPoint.1 - coefficientValue * sourcePoint.1)
      have thirdFrame := thirdHolds.2 (writeInput target.first)
        separation.first.targetAvoidsProduct separation.targetFirstAvoidsThird
      change (third (second (first store))).read
          (writeInput target.first) =
        (second (first store)).read (writeInput target.first) at thirdFrame
      rw [thirdFrame]
      have secondFrame := secondHolds.2 (writeInput target.first)
        separation.first.targetAvoidsProduct separation.targetFirstAvoidsSecond
      change (second (first store)).read (writeInput target.first) =
        (first store).read (writeInput target.first) at secondFrame
      rw [secondFrame]
      exact firstAfterFirst
    · change RawSignedRepresents
        ((third (second (first store))).read
          (writeInput target.second))
        (targetPoint.2.1 - coefficientValue * sourcePoint.2.1)
      have thirdFrame := thirdHolds.2 (writeInput target.second)
        separation.second.targetAvoidsProduct separation.targetSecondAvoidsThird
      change (third (second (first store))).read
          (writeInput target.second) =
        (second (first store)).read (writeInput target.second) at thirdFrame
      rw [thirdFrame]
      exact secondAfterSecond
  · intro shape other avoidsProduct avoidsFirst avoidsSecond avoidsThird
    exact (thirdHolds.2 other avoidsProduct avoidsThird).trans
      ((secondHolds.2 other avoidsProduct avoidsSecond).trans
        (firstHolds.2 other avoidsProduct avoidsFirst))

/-- Every caller read outside the four actual writes survives the complete point circuit. -/
lemma pointReduce_callerFrame (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsProduct : product.key ∉ other.storageKeys)
    (avoidsFirst : target.first.key ∉ other.storageKeys)
    (avoidsSecond : target.second.key ∉ other.storageKeys)
    (avoidsThird : target.third.key ∉ other.storageKeys) :
    (pointStore coefficient source target product store).read other = store.read other := by
  unfold pointStore
  rw [coordinateReduce_callerFrame _ _ _ _ _ other avoidsProduct avoidsThird,
    coordinateReduce_callerFrame _ _ _ _ _ other avoidsProduct avoidsSecond,
    coordinateReduce_callerFrame _ _ _ _ _ other avoidsProduct avoidsFirst]

/-- The coordinate circuit restores the complete borrowed interface, including correlations. -/
lemma coordinateReduce_borrowedRestored
    {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : Execution.State ctx Reference (model.HiddenState × History)) :
    (coordinateReduce (model := model) coefficient source target product).BorrowedRestored
      Reference state
      ((coordinateReduce (model := model) coefficient source target product).execute environment
        Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (coordinateProductOp coefficient source product))
    (BitWord.instruction (execution := model) (coordinateSubtractOp target product)) state
    (Circuit.borrowedRestored_classical (environment := environment) _ state)
    (Circuit.borrowedRestored_classical (environment := environment) _ _)

/-- Reusing the product word preserves the entire borrowed interface after all three updates. -/
lemma pointReduce_borrowedRestored
    {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : Execution.State ctx Reference (model.HiddenState × History)) :
    (pointReduce (model := model) coefficient source target product).BorrowedRestored
      Reference state
      ((pointReduce (model := model) coefficient source target product).execute environment
        Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact coordinateReduce_borrowedRestored coefficient (writeInput source.first)
      target.first product Reference state
  · apply Circuit.borrowedRestored_seq (environment := environment)
    · exact coordinateReduce_borrowedRestored coefficient (writeInput source.second)
        target.second product Reference _
    · exact coordinateReduce_borrowedRestored coefficient (writeInput source.third)
        target.third product Reference _

/-- All six actual instructions visit the same existing context. -/
lemma pointReduce_visited
    {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width))
    (path : (pointReduce (model := model) coefficient source target product).Path) :
    (pointReduce (model := model) coefficient source target product).visitedContexts path =
      [ctx, ctx, ctx, ctx, ctx, ctx] := rfl

/-- The resident bound counts the entire caller context, including the shared product word. -/
lemma pointReduce_resident_le
    {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width))
    (path : (pointReduce (model := model) coefficient source target product).Path) :
    (pointReduce (model := model) coefficient source target product).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have same : visited = ctx := by
    simpa only [pointReduce_visited, List.mem_cons, List.not_mem_nil, or_false,
      or_self] using present
  subst visited
  exact le_rfl

/-- The same original auxiliary cells suffice for every actual instruction. -/
lemma pointReduce_auxiliary_le
    {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (coefficient : CInputRef ctx (.unsignedWord width))
    (source target : LatticeState.PointRefs ctx width)
    (product : CWriteRef ctx (.unsignedWord width))
    (path : (pointReduce (model := model) coefficient source target product).Path) :
    (pointReduce (model := model) coefficient source target product).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have same : visited = ctx := by
    simpa only [pointReduce_visited, List.mem_cons, List.not_mem_nil, or_false,
      or_self] using present
  subst visited
  exact le_rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeArithmetic
