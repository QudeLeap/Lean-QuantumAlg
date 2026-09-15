/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Layout

/-!
# Actual third-coordinate metric prefix

The actual cross product feeds the target and third-row dot products. The
complete nineteen-instruction prefix preserves all four original point inputs.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual cross product followed by the numerator and signed-denominator dot refreshes. -/
def thirdMetricPrefixInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeCross.pointCrossInto refs.basis.first refs.basis.second refs.cross
      refs.productLeft refs.productRight)
    (.seq (LatticeDotRefresh.refreshInto refs.target refs.cross (numeratorDotRefs refs))
      (LatticeDotRefresh.refreshInto refs.basis.third refs.cross (denominatorDotRefs refs)))

/-- The nineteen actual chronological native updates of the metric prefix. -/
def metricPrefixStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  LatticeDotRefresh.refreshStore refs.basis.third refs.cross (denominatorDotRefs refs)
    (LatticeDotRefresh.refreshStore refs.target refs.cross (numeratorDotRefs refs)
      (LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
        refs.productLeft refs.productRight store))

/-- The unique actual path records all nineteen straight-line instructions. -/
def metricPrefixPath (refs : Refs ctx width) : (thirdMetricPrefixInto refs).Path :=
  ((((), ((), ())), (((), ((), ())), ((), ((), ())))),
    (((), (((), ()), ((), ()))), ((), (((), ()), ((), ())))))

private theorem metricTail_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (LatticeDotRefresh.refreshInto refs.target refs.cross (numeratorDotRefs refs))
      (LatticeDotRefresh.refreshInto refs.basis.third refs.cross (denominatorDotRefs refs))).execute
        Reference state = state.mapClassical (fun entry =>
          (LatticeDotRefresh.refreshStore refs.basis.third refs.cross (denominatorDotRefs refs)
            (LatticeDotRefresh.refreshStore refs.target refs.cross (numeratorDotRefs refs) entry.1),
              (entry.2, (metricPrefixPath refs).2))) := by
  refine (Circuit.execute_seq_mapClassical _ _
    (fun store => (LatticeDotRefresh.refreshStore refs.target refs.cross (numeratorDotRefs refs)
      store, (metricPrefixPath refs).2.1))
    (fun store => (LatticeDotRefresh.refreshStore refs.basis.third refs.cross
      (denominatorDotRefs refs) store, (metricPrefixPath refs).2.2))
    (by
      intro Reference History _ state
      refine (LatticeDotRefresh.refreshInto_execute refs.target refs.cross (numeratorDotRefs refs)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (by
      intro Reference History _ state
      refine (LatticeDotRefresh.refreshInto_execute refs.basis.third refs.cross
        (denominatorDotRefs refs) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual execution preserves history and quantum-reference blocks. -/
theorem thirdMetricPrefixInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (thirdMetricPrefixInto refs).execute Reference state = state.mapClassical (fun entry =>
      (metricPrefixStore refs entry.1, (entry.2, metricPrefixPath refs))) := by
  refine (Circuit.execute_seq_mapClassical _ _
    (fun store => (LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
      refs.productLeft refs.productRight store, (metricPrefixPath refs).1))
    (fun store => (LatticeDotRefresh.refreshStore refs.basis.third refs.cross
      (denominatorDotRefs refs)
        (LatticeDotRefresh.refreshStore refs.target refs.cross (numeratorDotRefs refs) store),
          (metricPrefixPath refs).2))
    (by
      intro Reference History _ state
      refine (LatticeCross.pointCrossInto_execute refs.basis.first refs.basis.second refs.cross
      refs.productLeft refs.productRight Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (metricTail_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private abbrev crossPhaseCell : LatticeCross.MutableCell → PhaseCell
  | .outputFirst => .crossFirst
  | .outputSecond => .crossSecond
  | .outputThird => .crossThird
  | .productLeft => .productLeft
  | .productRight => .productRight

/-- Named cells actually written by the nineteen native prefix instructions. -/
def prefixCells : List PhaseCell :=
  [.crossFirst, .crossSecond, .crossThird, .productLeft, .productRight,
    .dotProduct, .numerator, .denominator]

/-- Every caller read outside the actual prefix footprint is unchanged. -/
theorem thirdMetricPrefixInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell ∈ prefixCells, phaseCellKey refs cell ∉ other.storageKeys) :
    (metricPrefixStore refs store).read other = store.read other := by
  unfold metricPrefixStore
  rw [LatticeDotRefresh.refreshInto_callerFrame _ _ (denominatorDotRefs refs) _ other
      (avoids .denominator (by simp [prefixCells])) (avoids .dotProduct (by simp [prefixCells])),
    LatticeDotRefresh.refreshInto_callerFrame _ _ (numeratorDotRefs refs) _ other
      (avoids .numerator (by simp [prefixCells])) (avoids .dotProduct (by simp [prefixCells]))]
  apply LatticeCross.pointCrossInto_callerFrame
  intro cell
  have key : LatticeCross.mutableKey refs.cross refs.productLeft refs.productRight cell =
      phaseCellKey refs (crossPhaseCell cell) := by cases cell <;> rfl
  rw [key]
  exact avoids _ (by cases cell <;> simp [prefixCells])

private theorem named_avoids (refs : Refs ctx width) (separation : PhaseSeparation refs)
    {shape : CShape} (other : CWriteRef ctx shape) (source target : PhaseCell)
    (sourceKey : other.key = phaseCellKey refs source) (different : target ≠ source) :
    phaseCellKey refs target ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  change phaseCellKey refs target ∉ [other.key]
  simpa only [List.mem_singleton, sourceKey] using
    separation.phaseCellKey_ne target source different

private theorem cross_frame (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape) (source : PhaseCell)
    (sourceKey : other.key = phaseCellKey refs source)
    (outside : ∀ cell, crossPhaseCell cell ≠ source) :
    (LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
      refs.productLeft refs.productRight store).read (.storage other.toCStorageRef) =
        store.read (.storage other.toCStorageRef) := by
  apply LatticeCross.pointCrossInto_callerFrame
  intro cell
  have key : LatticeCross.mutableKey refs.cross refs.productLeft refs.productRight cell =
      phaseCellKey refs (crossPhaseCell cell) := by cases cell <;> rfl
  rw [key]
  exact named_avoids refs separation other source _ sourceKey (outside cell)

private theorem point_of_frames {before after : Store ctx}
    (refs : LatticeState.PointRefs ctx width) (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents before refs value)
    (first : after.read (writeInput refs.first) = before.read (writeInput refs.first))
    (second : after.read (writeInput refs.second) = before.read (writeInput refs.second))
    (third : after.read (writeInput refs.third) = before.read (writeInput refs.third)) :
    LatticeArithmetic.PointRawRepresents after refs value := by
  refine ⟨?_, ?_, ?_⟩
  · rw [first]; exact rep.1
  · rw [second]; exact rep.2.1
  · rw [third]; exact rep.2.2

/-- Actual prefix words represent the original signed dots, retaining all four original points. -/
theorem thirdMetricPrefixInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (first second third target : NumberTheory.IntegerPoint3)
    (firstRep : LatticeArithmetic.PointRawRepresents store refs.basis.first first)
    (secondRep : LatticeArithmetic.PointRawRepresents store refs.basis.second second)
    (thirdRep : LatticeArithmetic.PointRawRepresents store refs.basis.third third)
    (targetRep : LatticeArithmetic.PointRawRepresents store refs.target target) :
    RawSignedRepresents ((metricPrefixStore refs store).read (writeInput refs.numerator))
        (numeratorValue first second target) ∧
      RawSignedRepresents ((metricPrefixStore refs store).read (writeInput refs.denominator))
        (denominatorValue first second third) ∧
      LatticeArithmetic.PointRawRepresents (metricPrefixStore refs store) refs.basis.first first ∧
      LatticeArithmetic.PointRawRepresents (metricPrefixStore refs store) refs.basis.second second ∧
      LatticeArithmetic.PointRawRepresents (metricPrefixStore refs store) refs.basis.third third ∧
      LatticeArithmetic.PointRawRepresents (metricPrefixStore refs store) refs.target target ∧
      LatticeArithmetic.PointRawRepresents (metricPrefixStore refs store) refs.cross
        (crossValue first second) := by
  let crossed := LatticeCross.pointStore refs.basis.first refs.basis.second refs.cross
    refs.productLeft refs.productRight store
  let dotted := LatticeDotRefresh.refreshStore refs.target refs.cross
    (numeratorDotRefs refs) crossed
  have crossRep := LatticeCross.pointCrossInto_correct _ _ _ _ _ separation.cross
    store first second firstRep secondRep
  have thirdCross : LatticeArithmetic.PointRawRepresents crossed refs.basis.third third := by
    apply point_of_frames refs.basis.third third thirdRep
    · exact cross_frame refs separation.phase store refs.basis.third.first .basisThirdFirst rfl
        (by intro cell; cases cell <;> decide)
    · exact cross_frame refs separation.phase store refs.basis.third.second .basisThirdSecond rfl
        (by intro cell; cases cell <;> decide)
    · exact cross_frame refs separation.phase store refs.basis.third.third .basisThirdThird rfl
        (by intro cell; cases cell <;> decide)
  have targetCross : LatticeArithmetic.PointRawRepresents crossed refs.target target := by
    apply point_of_frames refs.target target targetRep
    · exact cross_frame refs separation.phase store refs.target.first .targetFirst rfl
        (by intro cell; cases cell <;> decide)
    · exact cross_frame refs separation.phase store refs.target.second .targetSecond rfl
        (by intro cell; cases cell <;> decide)
    · exact cross_frame refs separation.phase store refs.target.third .targetThird rfl
        (by intro cell; cases cell <;> decide)
  have numerator := LatticeDotRefresh.refreshInto_correct _ _ (numeratorDotRefs refs)
    separation.numeratorDot crossed target (crossValue first second) targetCross crossRep
  have thirdDotted : LatticeArithmetic.PointRawRepresents dotted refs.basis.third third := by
    apply point_of_frames refs.basis.third third thirdCross
    · exact LatticeDotRefresh.refreshInto_callerFrame _ _ (numeratorDotRefs refs)
        crossed (writeInput refs.basis.third.first)
        (named_avoids refs separation.phase refs.basis.third.first .basisThirdFirst
          .numerator rfl (by decide))
        (named_avoids refs separation.phase refs.basis.third.first .basisThirdFirst
          .dotProduct rfl (by decide))
    · exact LatticeDotRefresh.refreshInto_callerFrame _ _ (numeratorDotRefs refs)
        crossed (writeInput refs.basis.third.second)
        (named_avoids refs separation.phase refs.basis.third.second .basisThirdSecond
          .numerator rfl (by decide))
        (named_avoids refs separation.phase refs.basis.third.second .basisThirdSecond
          .dotProduct rfl (by decide))
    · exact LatticeDotRefresh.refreshInto_callerFrame _ _ (numeratorDotRefs refs)
        crossed (writeInput refs.basis.third.third)
        (named_avoids refs separation.phase refs.basis.third.third .basisThirdThird
          .numerator rfl (by decide))
        (named_avoids refs separation.phase refs.basis.third.third .basisThirdThird
          .dotProduct rfl (by decide))
  have denominator := LatticeDotRefresh.refreshInto_correct _ _ (denominatorDotRefs refs)
    separation.denominatorDot dotted third (crossValue first second) thirdDotted numerator.2.2
  have originalFrame {shape : CShape} (other : CWriteRef ctx shape) (source : PhaseCell)
      (sourceKey : other.key = phaseCellKey refs source) (outside : source ∉ prefixCells) :
      (metricPrefixStore refs store).read (.storage other.toCStorageRef) =
        store.read (.storage other.toCStorageRef) := by
    apply thirdMetricPrefixInto_callerFrame
    intro cell present
    exact named_avoids refs separation.phase other source cell sourceKey
      (fun equal => outside (equal ▸ present))
  refine ⟨?_, denominator.1, ?_, ?_, denominator.2.1, ?_, denominator.2.2⟩
  · change RawSignedRepresents
      ((LatticeDotRefresh.refreshStore refs.basis.third refs.cross (denominatorDotRefs refs)
        dotted).read (writeInput refs.numerator)) _
    rw [LatticeDotRefresh.refreshInto_callerFrame _ _ (denominatorDotRefs refs) dotted
      (writeInput refs.numerator)
      (named_avoids refs separation.phase refs.numerator .numerator .denominator rfl (by decide))
      (named_avoids refs separation.phase refs.numerator .numerator .dotProduct rfl (by decide))]
    exact numerator.1
  · apply point_of_frames refs.basis.first first firstRep
    · exact originalFrame refs.basis.first.first .basisFirstFirst rfl (by decide)
    · exact originalFrame refs.basis.first.second .basisFirstSecond rfl (by decide)
    · exact originalFrame refs.basis.first.third .basisFirstThird rfl (by decide)
  · apply point_of_frames refs.basis.second second secondRep
    · exact originalFrame refs.basis.second.first .basisSecondFirst rfl (by decide)
    · exact originalFrame refs.basis.second.second .basisSecondSecond rfl (by decide)
    · exact originalFrame refs.basis.second.third .basisSecondThird rfl (by decide)
  · apply point_of_frames refs.target target targetRep
    · exact originalFrame refs.target.first .targetFirst rfl (by decide)
    · exact originalFrame refs.target.second .targetSecond rfl (by decide)
    · exact originalFrame refs.target.third .targetThird rfl (by decide)

/-- The actual prefix contains nineteen native instruction dependencies. -/
theorem thirdMetricPrefixInto_depth (refs : Refs ctx width)
    (path : (thirdMetricPrefixInto refs).Path) :
    (thirdMetricPrefixInto refs).depth (fun _ => 1) path = 19 := rfl

/-- All actual metric-prefix instructions restore borrowed correlations jointly. -/
theorem thirdMetricPrefixInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (thirdMetricPrefixInto refs).BorrowedRestored Reference state
      ((thirdMetricPrefixInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact LatticeCross.pointCrossInto_borrowedRestored _ _ _ _ _ Reference state
  · exact Circuit.borrowedRestored_seq _ _ _
      (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
      (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
