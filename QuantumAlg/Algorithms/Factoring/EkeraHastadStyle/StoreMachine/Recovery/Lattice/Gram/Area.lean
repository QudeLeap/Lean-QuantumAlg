/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Norm

/-!
# Actual lattice squared-area refresh

The actual cross product feeds the actual five-instruction norm refresh.
Fourteen native operations compute the squared area with arbitrary initial
scratch, retaining the cross product for later Gram and nearest-plane phases.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeAreaRefresh

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Caller-owned outputs and scratch cells for one squared-area refresh. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the cross stage. -/
  cross : LatticeState.PointRefs ctx width
  /-- Writable cell for the product left value. -/
  productLeft : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  productLeftRole : productLeft.toCStorageRef.role = .workspace
  /-- Writable cell for the product right value. -/
  productRight : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  productRightRole : productRight.toCStorageRef.role = .workspace
  /-- Writable cell for the area value. -/
  area : CWriteRef ctx (.unsignedWord width)
  areaRole : area.toCStorageRef.role = .workspace
  /-- Writable cell for the norm product value. -/
  normProduct : CWriteRef ctx (.unsignedWord width)
  normProductRole : normProduct.toCStorageRef.role = .workspace

/-- The norm-refresh view of the area accumulator and its product scratch. -/
def normRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeNormRefresh.Refs ctx width where
  norm := refs.area
  normRole := refs.areaRole
  product := refs.normProduct
  productRole := refs.normProductRole

/-- Structural separation for the cross-product and norm-refresh phases. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (left right : LatticeState.PointRefs ctx width) (refs : Refs ctx width) : Prop where
  cross : LatticeCross.PointCrossSeparation left right refs.cross refs.productLeft
    refs.productRight
  norm : LatticeNormRefresh.Separation refs.cross (normRefs refs)

/-- The actual cross-product output is read by the actual squared-norm circuit. -/
def refreshInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeCross.pointCrossInto left right refs.cross refs.productLeft refs.productRight)
    (LatticeNormRefresh.refreshInto refs.cross (normRefs refs))

/-- Fourteen chronological native updates on the actual store. -/
def refreshStore (left right : LatticeState.PointRefs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  LatticeNormRefresh.refreshStore refs.cross (normRefs refs)
    (LatticeCross.pointStore left right refs.cross refs.productLeft refs.productRight store)

/-- Actual selected cross-product and norm paths on their chronological stores. -/
def refreshStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refreshInto (model := model) left right refs).Path :=
  let crossed := LatticeCross.pointStep (model := model)
    left right refs.cross refs.productLeft refs.productRight store
  let squared := LatticeDotRefresh.refreshStep (model := model)
    refs.cross refs.cross (LatticeNormRefresh.dotRefs (normRefs refs)) crossed.1
  (squared.1, (crossed.2, squared.2))

lemma refreshStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    (refreshStep (model := model) left right refs store).1 =
      refreshStore left right refs store := rfl

/-- Complete actual execution preserves histories and quantum-reference correlations. -/
lemma refreshInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) left right refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := refreshStep (model := model) left right refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (LatticeCross.pointCrossInto (model := model)
      left right refs.cross refs.productLeft refs.productRight)
    (LatticeNormRefresh.refreshInto (model := model) refs.cross (normRefs refs))
    (fun before =>
      let actual := LatticeCross.pointStep (model := model)
        left right refs.cross refs.productLeft refs.productRight before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeDotRefresh.refreshStep (model := model)
        refs.cross refs.cross (LatticeNormRefresh.dotRefs (normRefs refs)) before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeCross.pointCrossInto_execute _ _ _ _ _ reference current)
    (fun reference _history _ current =>
      LatticeNormRefresh.refreshInto_execute _ _ reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Reads outside all seven writable cells are preserved by the actual area refresh. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.productLeft.key ∉ other.storageKeys → refs.productRight.key ∉ other.storageKeys →
      refs.cross.first.key ∉ other.storageKeys → refs.cross.second.key ∉ other.storageKeys →
        refs.cross.third.key ∉ other.storageKeys → refs.area.key ∉ other.storageKeys →
          refs.normProduct.key ∉ other.storageKeys → after.read other = before.read other

/-- The caller frame follows only the actual written keys, without arithmetic premises. -/
lemma refreshInto_callerFrame (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (refreshStore left right refs store) := by
  intro shape other productLeft productRight first second third area normProduct
  unfold refreshStore
  rw [LatticeNormRefresh.refreshInto_callerFrame _ _ _ other area normProduct]
  apply LatticeCross.pointCrossInto_callerFrame
  intro cell
  cases cell with
  | outputFirst => exact first
  | outputSecond => exact second
  | outputThird => exact third
  | productLeft => exact productLeft
  | productRight => exact productRight

/-- The actual output is the original squared area and the computed cross product survives. -/
lemma refreshInto_correct (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (separation : Separation left right refs) (store : Store ctx)
    (leftValue rightValue : NumberTheory.IntegerPoint3)
    (leftRep : LatticeArithmetic.PointRawRepresents store left leftValue)
    (rightRep : LatticeArithmetic.PointRawRepresents store right rightValue) :
    RawSignedRepresents ((refreshStore left right refs store).read (writeInput refs.area))
        (NumberTheory.integerPointAreaSquared leftValue rightValue : Int) ∧
      LatticeArithmetic.PointRawRepresents (refreshStore left right refs store) refs.cross
        (NumberTheory.integerPointCross leftValue rightValue) := by
  have crossed := LatticeCross.pointCrossInto_correct left right refs.cross
    refs.productLeft refs.productRight separation.cross store leftValue rightValue leftRep rightRep
  exact LatticeNormRefresh.refreshInto_correct refs.cross (normRefs refs) separation.norm
    (LatticeCross.pointStore left right refs.cross refs.productLeft refs.productRight store)
    (NumberTheory.integerPointCross leftValue rightValue) crossed

/-- Both actual phases preserve the complete borrowed interface jointly with external references. -/
lemma refreshInto_borrowedRestored {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) left right refs).BorrowedRestored Reference state
      ((refreshInto (model := model) left right refs).execute environment Reference state) := by
  exact Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (LatticeCross.pointCrossInto_borrowedRestored _ _ _ _ _ Reference state)
    (LatticeNormRefresh.refreshInto_borrowedRestored _ _ Reference _)

/-- Independent native instruction formula of the nine-operation cross and five-operation norm. -/
def phaseTrace {model : ExecutionModel} [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width))]

/-- Every actual path has the independent fourteen-instruction formula. -/
lemma refreshInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).eventTrace path =
      phaseTrace (model := model) width := by
  change _ ++ _ = _
  rw [LatticeCross.pointCrossInto_events, LatticeNormRefresh.refreshInto_events]
  rfl

/-- Native multiplicities are exactly those of the independent instruction formula. -/
lemma refreshInto_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).resourcePool path =
      ResourcePool.ofList (phaseTrace (model := model) width) := by
  change ResourcePool.ofList ((refreshInto (model := model) left right refs).eventTrace
    path) = _
  rw [refreshInto_events]

/-- All fourteen instructions contribute to the actual unit-duration dependency depth. -/
lemma refreshInto_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).depth (fun _ => 1) path = 14 := rfl

/-- The two actual stages retain the complete original caller context. -/
lemma refreshInto_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (refreshInto (model := model) left right refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  rw [LatticeCross.pointCrossInto_visited, LatticeNormRefresh.refreshInto_visited] at present
  simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] using present

/-- Resident accounting includes every supplied classical cell and quantum dimension. -/
lemma refreshInto_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [refreshInto_visited left right refs path visited present]

/-- Auxiliary accounting retains the supplied roles without a temporary allocation. -/
lemma refreshInto_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) left right refs).Path) :
    (refreshInto (model := model) left right refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [refreshInto_visited left right refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeAreaRefresh
