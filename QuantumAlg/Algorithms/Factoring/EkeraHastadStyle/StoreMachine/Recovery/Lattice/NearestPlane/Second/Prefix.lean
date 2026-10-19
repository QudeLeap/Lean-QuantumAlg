/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Metric

/-!
# Actual second-phase metric prefix

The native cross product feeds five sequential dot refreshes. Each refresh
preserves all point inputs and earlier metric outputs. The prefix therefore
computes the original Gram entries and denominator from actual stored words.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- First compute the cross product, the first squared norm and the second-first Gram entry. -/
def secondMetricPrefixInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeCross.pointCrossInto refs.basis.first refs.basis.second refs.cross
      refs.crossProductLeft refs.crossProductRight)
    (.seq (metricInto refs .g11) (metricInto refs .g21))

/-- All metrics required by the actual second numerator and denominator. -/
def secondPrefixInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (secondMetricPrefixInto refs)
    (.seq (metricInto refs .targetSecond)
      (.seq (metricInto refs .targetFirst) (metricInto refs .denominator)))

/-- The chronological native writes of the cross product and first two metrics. -/
def secondMetricPrefixStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  metricStore refs .g21 (metricStore refs .g11
    (LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
      refs.crossProductLeft refs.crossProductRight store))

/-- The thirty-four actual native writes of the complete metric prefix. -/
def secondPrefixStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  metricStore refs .denominator (metricStore refs .targetFirst
    (metricStore refs .targetSecond (secondMetricPrefixStore refs store)))

/-- Each actual metric refresh returns its native output path. -/
def metricStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (metric : Metric)
    (store : Store ctx) : Store ctx × (metricInto refs metric).Path :=
  LatticeDotRefresh.refreshStep (inputPointRefs refs (metricLeft metric))
    (inputPointRefs refs (metricRight metric)) (metricRefs refs metric) store

/-- The cross product and first two actual metric paths in chronological order. -/
def secondMetricPrefixStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondMetricPrefixInto refs).Path :=
  let cross := LatticeCross.pointStep refs.basis.first refs.basis.second refs.cross
    refs.crossProductLeft refs.crossProductRight store
  let g11 := metricStep refs .g11 cross.1
  let g21 := metricStep refs .g21 g11.1
  (g21.1, (cross.2, (g11.2, g21.2)))

/-- All five actual metric paths and the cross path share one chronological store. -/
def secondPrefixStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondPrefixInto refs).Path :=
  let first := secondMetricPrefixStep refs store
  let targetSecond := metricStep refs .targetSecond first.1
  let targetFirst := metricStep refs .targetFirst targetSecond.1
  let denominator := metricStep refs .denominator targetFirst.1
  (denominator.1, (first.2, (targetSecond.2, (targetFirst.2, denominator.2))))

private def metricPairStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (left right : Metric)
    (store : Store ctx) :
    Store ctx × (Circuit.seq (metricInto refs left) (metricInto refs right)).Path :=
  let first := metricStep refs left store
  let second := metricStep refs right first.1
  (second.1, (first.2, second.2))

private def metricTripleStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (left middle right : Metric)
    (store : Store ctx) :
    Store ctx ×
      (Circuit.seq (metricInto refs left)
        (.seq (metricInto refs middle) (metricInto refs right))).Path :=
  let first := metricStep refs left store
  let rest := metricPairStep refs middle right first.1
  (rest.1, (first.2, rest.2))

private lemma metric_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (metric : Metric)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (metricInto refs metric).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := metricStep refs metric entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  LatticeDotRefresh.refreshInto_execute _ _ _ Reference state

private lemma metricPair_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (left right : Metric)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (metricInto refs left) (metricInto refs right)).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        let actual := metricPairStep refs left right entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (metricInto refs left) (metricInto refs right)
    (fun before =>
      let actual := metricStep refs left before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := metricStep refs right before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => metric_execute refs left reference current)
    (fun reference _history _ current => metric_execute refs right reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma metricTriple_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (left middle right : Metric)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (metricInto refs left)
      (.seq (metricInto refs middle) (metricInto refs right))).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := metricTripleStep refs left middle right entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) (metricInto refs left)
    (.seq (metricInto refs middle) (metricInto refs right))
    (fun before =>
      let actual := metricStep refs left before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := metricPairStep refs middle right before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => metric_execute refs left reference current)
    (fun reference _history _ current => metricPair_execute refs middle right reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma secondMetricPrefix_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondMetricPrefixInto refs).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := secondMetricPrefixStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) _ _
    (fun before =>
      let actual := LatticeCross.pointStep refs.basis.first refs.basis.second refs.cross
        refs.crossProductLeft refs.crossProductRight before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := metricPairStep refs .g11 .g21 before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeCross.pointCrossInto_execute refs.basis.first refs.basis.second refs.cross
        refs.crossProductLeft refs.crossProductRight reference current)
    (fun reference _history _ current => metricPair_execute refs .g11 .g21 reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete metric-prefix interpreter preserves the selected hidden state and history. -/
lemma secondPrefixInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondPrefixInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := secondPrefixStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) _ _
    (fun before =>
      let actual := secondMetricPrefixStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := metricTripleStep refs .targetSecond .targetFirst .denominator before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => secondMetricPrefix_execute refs reference current)
    (fun reference _history _ current =>
      metricTriple_execute refs .targetSecond .targetFirst .denominator reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private abbrev crossPhaseCell : LatticeCross.MutableCell → PhaseCell
  | .outputFirst => .crossFirst
  | .outputSecond => .crossSecond
  | .outputThird => .crossThird
  | .productLeft => .crossProductLeft
  | .productRight => .crossProductRight

private lemma cross_frame (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape) (source : PhaseCell)
    (sourceKey : other.key = phaseCellKey refs source)
    (outside : ∀ cell, crossPhaseCell cell ≠ source) :
    (LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
      refs.crossProductLeft refs.crossProductRight store).read (.storage other.toCStorageRef) =
        store.read (.storage other.toCStorageRef) := by
  apply LatticeCross.pointCrossInto_callerFrame
  intro cell
  have key : LatticeCross.mutableKey refs.cross refs.crossProductLeft refs.crossProductRight cell =
      phaseCellKey refs (crossPhaseCell cell) := by cases cell <;> rfl
  change LatticeCross.mutableKey refs.cross refs.crossProductLeft refs.crossProductRight cell ∉
    [other.key]
  simpa only [List.mem_singleton, sourceKey, key] using
    separation.phaseCellKey_ne _ _ (outside cell)

private lemma cross_preserves_point (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) (point : InputPoint) (notCross : point ≠ .cross)
    (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store (inputPointRefs refs point) value) :
    LatticeArithmetic.PointRawRepresents
      (LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
        refs.crossProductLeft refs.crossProductRight store) (inputPointRefs refs point) value := by
  cases point with
  | first =>
    refine ⟨?_, ?_, ?_⟩
    · rw [cross_frame refs separation store refs.basis.first.first .basisFirstFirst rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.1
    · rw [cross_frame refs separation store refs.basis.first.second .basisFirstSecond rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.2.1
    · rw [cross_frame refs separation store refs.basis.first.third .basisFirstThird rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.2.2
  | second =>
    refine ⟨?_, ?_, ?_⟩
    · rw [cross_frame refs separation store refs.basis.second.first .basisSecondFirst rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.1
    · rw [cross_frame refs separation store refs.basis.second.second .basisSecondSecond rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.2.1
    · rw [cross_frame refs separation store refs.basis.second.third .basisSecondThird rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.2.2
  | target =>
    refine ⟨?_, ?_, ?_⟩
    · rw [cross_frame refs separation store refs.target.first .targetFirst rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.1
    · rw [cross_frame refs separation store refs.target.second .targetSecond rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.2.1
    · rw [cross_frame refs separation store refs.target.third .targetThird rfl
        (by intro cell; cases cell <;> decide)]
      exact rep.2.2
  | cross => exact (notCross rfl).elim

/-- Original point values together with their computed cross product. -/
abbrev prefixValues (first second target : NumberTheory.IntegerPoint3) :
    InputPoint → NumberTheory.IntegerPoint3
  | .first => first
  | .second => second
  | .target => target
  | .cross => NumberTheory.integerPointCross first second

/-- The actual metric prefix preserves its four input points and computes all five original dots. -/
lemma secondPrefixInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (first second target : NumberTheory.IntegerPoint3)
    (firstRep : LatticeArithmetic.PointRawRepresents store refs.basis.first first)
    (secondRep : LatticeArithmetic.PointRawRepresents store refs.basis.second second)
    (targetRep : LatticeArithmetic.PointRawRepresents store refs.target target) :
    (∀ point, LatticeArithmetic.PointRawRepresents (secondPrefixStore refs store)
      (inputPointRefs refs point) (prefixValues first second target point)) ∧
    (∀ metric, RawSignedRepresents ((secondPrefixStore refs store).read
      (writeInput (metricRefs refs metric).dot))
      (NumberTheory.integerPointDot
        (prefixValues first second target (metricLeft metric))
        (prefixValues first second target (metricRight metric)))) := by
  let crossed := LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
    refs.crossProductLeft refs.crossProductRight store
  have crossedReps (point : InputPoint) : LatticeArithmetic.PointRawRepresents crossed
      (inputPointRefs refs point) (prefixValues first second target point) := by
    cases point with
    | first => exact cross_preserves_point refs separation.phase store .first (by decide) _ firstRep
    | second =>
      exact cross_preserves_point refs separation.phase store .second (by decide) _ secondRep
    | target =>
      exact cross_preserves_point refs separation.phase store .target (by decide) _ targetRep
    | cross =>
      exact LatticeCross.pointCrossInto_correct _ _ _ _ _ separation.cross
        store first second firstRep secondRep
  let s1 := metricStore refs .g11 crossed
  have r1 (point : InputPoint) := metricInto_preserves_point refs separation.phase .g11
    crossed point _ (crossedReps point)
  have v1 := metricInto_correct refs separation .g11 crossed _ crossedReps
  let s2 := metricStore refs .g21 s1
  have r2 (point : InputPoint) := metricInto_preserves_point refs separation.phase .g21
    s1 point _ (r1 point)
  have v2 := metricInto_correct refs separation .g21 s1 _ r1
  let s3 := metricStore refs .targetSecond s2
  have r3 (point : InputPoint) := metricInto_preserves_point refs separation.phase .targetSecond
    s2 point _ (r2 point)
  have v3 := metricInto_correct refs separation .targetSecond s2 _ r2
  let s4 := metricStore refs .targetFirst s3
  have r4 (point : InputPoint) := metricInto_preserves_point refs separation.phase .targetFirst
    s3 point _ (r3 point)
  have v4 := metricInto_correct refs separation .targetFirst s3 _ r3
  let s5 := metricStore refs .denominator s4
  have r5 (point : InputPoint) := metricInto_preserves_point refs separation.phase .denominator
    s4 point _ (r4 point)
  have v5 := metricInto_correct refs separation .denominator s4 _ r4
  refine ⟨r5, ?_⟩
  intro metric
  cases metric with
  | g11 =>
    change RawSignedRepresents (s5.read _) _
    rw [metricInto_preserves_metric refs separation.phase .denominator .g11
        (by decide) s4,
      metricInto_preserves_metric refs separation.phase .targetFirst .g11
        (by decide) s3,
      metricInto_preserves_metric refs separation.phase .targetSecond .g11
        (by decide) s2,
      metricInto_preserves_metric refs separation.phase .g21 .g11
        (by decide) s1]
    exact v1
  | g21 =>
    change RawSignedRepresents (s5.read _) _
    rw [metricInto_preserves_metric refs separation.phase .denominator .g21
        (by decide) s4,
      metricInto_preserves_metric refs separation.phase .targetFirst .g21
        (by decide) s3,
      metricInto_preserves_metric refs separation.phase .targetSecond .g21
        (by decide) s2]
    exact v2
  | targetSecond =>
    change RawSignedRepresents (s5.read _) _
    rw [metricInto_preserves_metric refs separation.phase .denominator .targetSecond
        (by decide) s4,
      metricInto_preserves_metric refs separation.phase .targetFirst .targetSecond
        (by decide) s3]
    exact v3
  | targetFirst =>
    change RawSignedRepresents (s5.read _) _
    rw [metricInto_preserves_metric refs separation.phase .denominator .targetFirst
        (by decide) s4]
    exact v4
  | denominator =>
    exact v5

/-- The prefix executes nine cross-product and twenty-five dot-refresh instructions. -/
lemma secondPrefixInto_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (secondPrefixInto refs).Path) :
    (secondPrefixInto refs).depth (fun _ => 1) path = 34 := rfl

/-- All actual native writes jointly preserve the complete borrowed interface. -/
lemma secondPrefixInto_borrowedRestored {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondPrefixInto refs).BorrowedRestored Reference state
      ((secondPrefixInto refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · apply Circuit.borrowedRestored_seq (environment := environment)
    · exact LatticeCross.pointCrossInto_borrowedRestored _ _ _ _ _ Reference state
    · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
  · apply Circuit.borrowedRestored_seq (environment := environment)
    · exact LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _
    · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
