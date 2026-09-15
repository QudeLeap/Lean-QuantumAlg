/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Layout

/-!
# Actual second-phase metric refreshes

Five views select the existing caller cells and the shared native dot circuit.
All four input points survive each refresh, so later metrics read the original
coordinates even when the same product scratch is reused.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The five stored dot products needed by the second-coordinate numerator and denominator. -/
inductive Metric where
  | g11 | g21 | targetSecond | targetFirst | denominator
deriving DecidableEq

/-- The four points read while forming the second-phase metrics. -/
inductive InputPoint where
  | first | second | target | cross
deriving DecidableEq

/-- Resolve a point view to its three existing caller coordinates. -/
abbrev inputPointRefs (refs : Refs ctx width) : InputPoint → LatticeState.PointRefs ctx width
  | .first => refs.basis.first
  | .second => refs.basis.second
  | .target => refs.target
  | .cross => refs.cross

/-- Resolve a metric view to the existing accumulator and shared product word. -/
abbrev metricRefs (refs : Refs ctx width) : Metric → LatticeDotRefresh.Refs ctx width
  | .g11 => g11DotRefs refs
  | .g21 => g21DotRefs refs
  | .targetSecond => targetSecondDotRefs refs
  | .targetFirst => targetFirstDotRefs refs
  | .denominator => denominatorDotRefs refs

/-- Named accumulator identity of a selected metric. -/
abbrev metricCell : Metric → PhaseCell
  | .g11 => .g11
  | .g21 => .g21
  | .targetSecond => .targetDotSecond
  | .targetFirst => .targetDotFirst
  | .denominator => .denominator

/-- Left point input of the selected dot refresh. -/
abbrev metricLeft : Metric → InputPoint
  | .g11 => .first
  | .g21 => .second
  | .targetSecond => .target
  | .targetFirst => .target
  | .denominator => .cross

/-- Right point input of the selected dot refresh. -/
abbrev metricRight : Metric → InputPoint
  | .g11 => .first
  | .g21 => .first
  | .targetSecond => .second
  | .targetFirst => .first
  | .denominator => .cross

/-- One actual native five-instruction dot refresh. -/
def metricInto (refs : Refs ctx width) (metric : Metric) : Circuit ctx ctx :=
  LatticeDotRefresh.refreshInto (inputPointRefs refs (metricLeft metric))
    (inputPointRefs refs (metricRight metric)) (metricRefs refs metric)

/-- The corresponding five chronological writes on the actual store. -/
def metricStore (refs : Refs ctx width) (metric : Metric) (store : Store ctx) : Store ctx :=
  LatticeDotRefresh.refreshStore (inputPointRefs refs (metricLeft metric))
    (inputPointRefs refs (metricRight metric)) (metricRefs refs metric) store

private theorem metric_output_key (refs : Refs ctx width) (metric : Metric) :
    (metricRefs refs metric).dot.key = phaseCellKey refs (metricCell metric) := by
  cases metric <;> rfl

private theorem metric_product_key (refs : Refs ctx width) (metric : Metric) :
    (metricRefs refs metric).product.key = phaseCellKey refs .dotProduct := by
  cases metric <;> rfl

/-- Any named caller cell distinct from the two actual outputs is unchanged. -/
theorem metricInto_frame (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (metric : Metric) (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape)
    (source : PhaseCell) (sourceKey : other.key = phaseCellKey refs source)
    (notMetric : metricCell metric ≠ source) (notProduct : .dotProduct ≠ source) :
    (metricStore refs metric store).read (.storage other.toCStorageRef) =
      store.read (.storage other.toCStorageRef) := by
  apply LatticeDotRefresh.refreshInto_callerFrame
  · change (metricRefs refs metric).dot.key ∉ [other.key]
    simpa only [List.mem_singleton, sourceKey, metric_output_key] using
      separation.phaseCellKey_ne _ _ notMetric
  · change (metricRefs refs metric).product.key ∉ [other.key]
    simpa only [List.mem_singleton, sourceKey, metric_product_key] using
      separation.phaseCellKey_ne _ _ notProduct

/-- All input points survive every actual metric refresh. -/
theorem metricInto_preserves_point (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (metric : Metric) (store : Store ctx) (point : InputPoint)
    (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store (inputPointRefs refs point) value) :
    LatticeArithmetic.PointRawRepresents (metricStore refs metric store)
      (inputPointRefs refs point) value := by
  cases point with
  | first =>
    refine ⟨?_, ?_, ?_⟩
    · rw [metricInto_frame refs separation metric store
        refs.basis.first.first .basisFirstFirst rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.1
    · rw [metricInto_frame refs separation metric store
        refs.basis.first.second .basisFirstSecond rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.1
    · rw [metricInto_frame refs separation metric store
        refs.basis.first.third .basisFirstThird rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.2
  | second =>
    refine ⟨?_, ?_, ?_⟩
    · rw [metricInto_frame refs separation metric store
        refs.basis.second.first .basisSecondFirst rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.1
    · rw [metricInto_frame refs separation metric store
        refs.basis.second.second .basisSecondSecond rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.1
    · rw [metricInto_frame refs separation metric store
        refs.basis.second.third .basisSecondThird rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.2
  | target =>
    refine ⟨?_, ?_, ?_⟩
    · rw [metricInto_frame refs separation metric store
        refs.target.first .targetFirst rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.1
    · rw [metricInto_frame refs separation metric store
        refs.target.second .targetSecond rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.1
    · rw [metricInto_frame refs separation metric store
        refs.target.third .targetThird rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.2
  | cross =>
    refine ⟨?_, ?_, ?_⟩
    · rw [metricInto_frame refs separation metric store
        refs.cross.first .crossFirst rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.1
    · rw [metricInto_frame refs separation metric store
        refs.cross.second .crossSecond rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.1
    · rw [metricInto_frame refs separation metric store
        refs.cross.third .crossThird rfl
        (by cases metric <;> decide) (by decide)]
      exact rep.2.2

/-- The selected actual output is the integer dot product of its two original input points. -/
theorem metricInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (metric : Metric) (store : Store ctx) (values : InputPoint → NumberTheory.IntegerPoint3)
    (reps : ∀ point, LatticeArithmetic.PointRawRepresents store
      (inputPointRefs refs point) (values point)) :
    RawSignedRepresents ((metricStore refs metric store).read
      (writeInput (metricRefs refs metric).dot))
      (NumberTheory.integerPointDot (values (metricLeft metric))
        (values (metricRight metric))) := by
  have separated : LatticeDotRefresh.Separation (inputPointRefs refs (metricLeft metric))
      (inputPointRefs refs (metricRight metric)) (metricRefs refs metric) := by
    cases metric with
    | g11 => exact separation.g11Dot
    | g21 => exact separation.g21Dot
    | targetSecond => exact separation.targetSecondDot
    | targetFirst => exact separation.targetFirstDot
    | denominator => exact separation.denominatorDot
  exact (LatticeDotRefresh.refreshInto_correct _ _ _ separated store _ _
    (reps (metricLeft metric)) (reps (metricRight metric))).1

/-- A later different metric preserves the earlier actual accumulator. -/
theorem metricInto_preserves_metric (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (written retained : Metric) (different : written ≠ retained) (store : Store ctx) :
    (metricStore refs written store).read (writeInput (metricRefs refs retained).dot) =
      store.read (writeInput (metricRefs refs retained).dot) := by
  apply metricInto_frame refs separation written store _ (metricCell retained)
    (metric_output_key refs retained)
  · cases written <;> cases retained <;> simp_all only [ne_eq, not_true_eq_false] <;> decide
  · cases retained <;> decide

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
