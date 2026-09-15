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
def secondMetricPrefixInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeCross.pointCrossInto refs.basis.first refs.basis.second refs.cross
      refs.crossProductLeft refs.crossProductRight)
    (.seq (metricInto refs .g11) (metricInto refs .g21))

/-- All metrics required by the actual second numerator and denominator. -/
def secondPrefixInto (refs : Refs ctx width) : Circuit ctx ctx :=
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

/-- The unique path of each straight-line metric prefix records every actual native instruction. -/
def prefixPath (refs : Refs ctx width) : (secondPrefixInto refs).Path :=
  (((((), ((), ())), (((), ((), ())), ((), ((), ())))),
      (((), (((), ()), ((), ()))), ((), (((), ()), ((), ()))))),
    (((), (((), ()), ((), ()))),
      (((), (((), ()), ((), ()))), ((), (((), ()), ((), ()))))))

private def metricPath (refs : Refs ctx width) (metric : Metric) : (metricInto refs metric).Path :=
  ((), (((), ()), ((), ())))

private theorem metric_execute (refs : Refs ctx width) (metric : Metric) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (metricInto refs metric).execute Reference state = state.mapClassical (fun entry =>
      (metricStore refs metric entry.1, (entry.2, metricPath refs metric))) := by
  refine (LatticeDotRefresh.refreshInto_execute _ _ _ Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem metricPair_execute (refs : Refs ctx width) (left right : Metric)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (metricInto refs left) (metricInto refs right)).execute Reference state =
      state.mapClassical (fun entry =>
        (metricStore refs right (metricStore refs left entry.1),
          (entry.2, (metricPath refs left, metricPath refs right)))) := by
  refine (Circuit.execute_seq_mapClassical (metricInto refs left) (metricInto refs right)
    (fun store => (metricStore refs left store, metricPath refs left))
    (fun store => (metricStore refs right store, metricPath refs right))
    (metric_execute refs left) (metric_execute refs right) Reference state).trans ?_
  congr 1

set_option maxHeartbeats 800000 in
-- Composing three opaque dependent metric paths requires additional normalization.
private theorem metricTriple_execute (refs : Refs ctx width) (left middle right : Metric)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (metricInto refs left)
      (.seq (metricInto refs middle) (metricInto refs right))).execute Reference state =
      state.mapClassical (fun entry =>
        (metricStore refs right (metricStore refs middle (metricStore refs left entry.1)),
          (entry.2, (metricPath refs left, (metricPath refs middle, metricPath refs right))))) := by
  refine (Circuit.execute_seq_mapClassical (metricInto refs left)
    (.seq (metricInto refs middle) (metricInto refs right))
    (fun store => (metricStore refs left store, metricPath refs left))
    (fun store => (metricStore refs right (metricStore refs middle store),
      (metricPath refs middle, metricPath refs right)))
    (metric_execute refs left)
    (by
      intro Reference History _ state
      refine (metricPair_execute refs middle right Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem secondMetricPrefix_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondMetricPrefixInto refs).execute Reference state = state.mapClassical (fun entry =>
      (secondMetricPrefixStore refs entry.1, (entry.2, (prefixPath refs).1))) := by
  refine (Circuit.execute_seq_mapClassical _ _
    (fun store => (LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
      refs.crossProductLeft refs.crossProductRight store, (prefixPath refs).1.1))
    (fun store => (metricStore refs .g21 (metricStore refs .g11 store), (prefixPath refs).1.2))
    (by
      intro Reference History _ state
      refine (LatticeCross.pointCrossInto_execute refs.basis.first refs.basis.second refs.cross
      refs.crossProductLeft refs.crossProductRight Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (by
      intro Reference History _ state
      refine (metricPair_execute refs .g11 .g21 Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The complete actual metric-prefix interpreter preserves history and quantum-reference blocks. -/
theorem secondPrefixInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondPrefixInto refs).execute Reference state = state.mapClassical (fun entry =>
      (secondPrefixStore refs entry.1, (entry.2, prefixPath refs))) := by
  refine (Circuit.execute_seq_mapClassical _ _
    (fun store => (secondMetricPrefixStore refs store, (prefixPath refs).1))
    (fun store => (metricStore refs .denominator
      (metricStore refs .targetFirst (metricStore refs .targetSecond store)), (prefixPath refs).2))
    (secondMetricPrefix_execute refs)
    (by
      intro Reference History _ state
      refine (metricTriple_execute refs .targetSecond .targetFirst .denominator
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private abbrev crossPhaseCell : LatticeCross.MutableCell → PhaseCell
  | .outputFirst => .crossFirst
  | .outputSecond => .crossSecond
  | .outputThird => .crossThird
  | .productLeft => .crossProductLeft
  | .productRight => .crossProductRight

private theorem cross_frame (refs : Refs ctx width) (separation : PhaseSeparation refs)
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

private theorem cross_preserves_point (refs : Refs ctx width) (separation : PhaseSeparation refs)
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
theorem secondPrefixInto_correct (refs : Refs ctx width) (separation : Separation refs)
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
theorem secondPrefixInto_depth (refs : Refs ctx width) (path : (secondPrefixInto refs).Path) :
    (secondPrefixInto refs).depth (fun _ => 1) path = 34 := rfl

/-- All actual native writes jointly preserve the complete borrowed interface. -/
theorem secondPrefixInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondPrefixInto refs).BorrowedRestored Reference state
      ((secondPrefixInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · apply Circuit.borrowedRestored_seq
    · exact LatticeCross.pointCrossInto_borrowedRestored _ _ _ _ _ Reference state
    · exact Circuit.borrowedRestored_seq _ _ _
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
  · apply Circuit.borrowedRestored_seq
    · exact LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _
    · exact Circuit.borrowedRestored_seq _ _ _
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
