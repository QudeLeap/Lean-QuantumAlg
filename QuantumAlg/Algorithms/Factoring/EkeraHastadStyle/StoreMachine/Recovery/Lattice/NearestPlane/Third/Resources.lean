/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Resources
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Restoration

/-!
# Actual third-coordinate nearest-plane resources

Nineteen metric instructions, at most three denominator-normalization and two
numerator-correction instructions, thirteen division instructions and six
reductions give the independent bound forty-three. Every live cell is counted
in the supplied context, and borrowed restoration includes external references.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent nineteen-native-instruction formula for cross product and two dots. -/
def prefixTrace (width : Nat) : List (Resource.Event model) :=
  ([.wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .sub width,
    .wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .sub width,
    .wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .sub width,
    .wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .add width,
    .wordBinary .mulLow width, .wordBinary .add width,
    .wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .add width,
    .wordBinary .mulLow width, .wordBinary .add width] :
    List Resource.ClassicalOpLabel).map
      (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label))

/-- Independent actual normalization/division/reduction formula with recorded branch flags. -/
def normalizationTrace (width : Nat) (magnitudeNegative numeratorNegative
    divisionMagnitude divisionCorrection divisionRestore : Bool) : List (Resource.Event model) :=
  (signTrace width ++ magnitudeTrace width magnitudeNegative) ++
    ((if numeratorNegative then
      ([.wordUnary .complement width, .wordUnary .increment width] :
        List Resource.ClassicalOpLabel).map
        (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label))
      else []) ++
      (RoundedDiv.bodyTrace width divisionMagnitude divisionCorrection divisionRestore ++
        ([.wordBinary .mulLow width, .wordBinary .sub width,
          .wordBinary .mulLow width, .wordBinary .sub width,
          .wordBinary .mulLow width, .wordBinary .sub width] :
          List Resource.ClassicalOpLabel).map
          (fun label => .classicalOperation
            (BitWord.selectedCoordinate (execution := model) label))))

/-- Independent full-phase native formula for the real recorded flags. -/
def phaseTrace (width : Nat) (magnitudeNegative numeratorNegative
    divisionMagnitude divisionCorrection divisionRestore : Bool) : List (Resource.Event model) :=
  prefixTrace width ++ normalizationTrace width magnitudeNegative numeratorNegative
    divisionMagnitude divisionCorrection divisionRestore

/-- Every actual metric-prefix path has the independent nineteen-instruction trace. -/
theorem thirdMetricPrefixInto_events (refs : Refs ctx width)
    (path : (thirdMetricPrefixInto refs).Path) :
    (thirdMetricPrefixInto refs).eventTrace path = prefixTrace width := by
  unfold thirdMetricPrefixInto at path ⊢
  change _ ++ (_ ++ _) = _
  rw [LatticeCross.pointCrossInto_events, LatticeDotRefresh.refreshInto_events,
    LatticeDotRefresh.refreshInto_events]
  rfl

/-- The actual suffix events match the independent formula and recorded branch flags. -/
theorem thirdNormalizeInto_events (refs : Refs ctx width)
    (path : (thirdNormalizeInto refs).Path) :
    (thirdNormalizeInto refs).eventTrace path =
      let divided := path.2.2.1
      normalizationTrace width path.1.2.1.toBool path.2.1.1.toBool
        divided.1.1.2.1.toBool divided.2.1.2.1.1.toBool divided.2.2.2.2.1.toBool := by
  rcases path with ⟨normalizationPath, signPath, divisionPath, reductionPath⟩
  change _ ++ (_ ++ (_ ++ _)) = _
  rw [normalizeMagnitude_events, numeratorSignInto_events, RoundedDiv.body_events,
    LatticeArithmetic.pointReduce_events]
  rfl

/-- Full actual native events follow the independent formula with actual recorded flags. -/
theorem thirdInto_events (refs : Refs ctx width) (path : (thirdInto refs).Path) :
    (thirdInto refs).eventTrace path =
      let suffix := path.2
      let divided := suffix.2.2.1
      phaseTrace width suffix.1.2.1.toBool suffix.2.1.1.toBool
        divided.1.1.2.1.toBool divided.2.1.2.1.1.toBool divided.2.2.2.2.1.toBool := by
  change _ ++ _ = _
  rw [thirdMetricPrefixInto_events, thirdNormalizeInto_events]
  rfl

/-- Full actual native multiplicities are the pool of the independent instruction formula. -/
theorem thirdInto_resourcePool (refs : Refs ctx width) (path : (thirdInto refs).Path) :
    (thirdInto refs).resourcePool path =
      let suffix := path.2
      let divided := suffix.2.2.1
      ResourcePool.ofList (phaseTrace width suffix.1.2.1.toBool suffix.2.1.1.toBool
        divided.1.1.2.1.toBool divided.2.1.2.1.1.toBool divided.2.2.2.2.1.toBool) := by
  change ResourcePool.ofList ((thirdInto refs).eventTrace path) = _
  rw [thirdInto_events]

/-- The actual sign-normalizing suffix uses at most twenty-four native instructions. -/
theorem thirdNormalizeInto_eventCount_le (refs : Refs ctx width)
    (path : (thirdNormalizeInto refs).Path) :
    ((thirdNormalizeInto refs).eventTrace path).length ≤ 24 := by
  rcases path with ⟨normalizationPath, signPath, divisionPath, reductionPath⟩
  have normalized := normalizeMagnitude_eventCount_le (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude normalizationPath
  have corrected := numeratorSignInto_eventCount_le refs signPath
  have divided := RoundedDiv.body_eventCount_le refs.division divisionPath
  change List.length (_ ++ (_ ++ (_ ++ _))) ≤ 24
  rw [LatticeArithmetic.pointReduce_events]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- At most forty-three native instructions execute in the full third phase. -/
theorem thirdInto_eventCount_le (refs : Refs ctx width) (path : (thirdInto refs).Path) :
    ((thirdInto refs).eventTrace path).length ≤ 43 := by
  have suffix := thirdNormalizeInto_eventCount_le refs path.2
  have prefixLength : (prefixTrace (model := model) width).length = 19 := rfl
  change List.length (_ ++ _) ≤ 43
  rw [List.length_append, thirdMetricPrefixInto_events, prefixLength]
  omega

/-- The actual suffix retains all sign, division and reduction dependencies. -/
theorem thirdNormalizeInto_depth_le (refs : Refs ctx width)
    (path : (thirdNormalizeInto refs).Path) :
    (thirdNormalizeInto refs).depth (fun _ => 1) path ≤ 24 := by
  rcases path with ⟨normalizationPath, signPath, divisionPath, reductionPath⟩
  have normalized := normalizeMagnitude_depth_le (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude normalizationPath
  have corrected := numeratorSignInto_depth_le refs signPath
  have divided := RoundedDiv.body_depth_le refs.division divisionPath
  have reduction : (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.third refs.target refs.reduceProduct).depth (fun _ => 1) reductionPath = 6 := rfl
  change (normalizeMagnitude (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude).depth (fun _ => 1) normalizationPath +
    ((numeratorSignInto refs).depth (fun _ => 1) signPath +
      ((RoundedDiv.body refs.division).depth (fun _ => 1) divisionPath +
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct).depth (fun _ => 1) reductionPath)) ≤ 24
  rw [reduction]
  omega

/-- The full actual unit-duration dependency depth is at most forty-three. -/
theorem thirdInto_depth_le (refs : Refs ctx width) (path : (thirdInto refs).Path) :
    (thirdInto refs).depth (fun _ => 1) path ≤ 43 := by
  have suffix := thirdNormalizeInto_depth_le refs path.2
  change (thirdMetricPrefixInto refs).depth (fun _ => 1) path.1 +
    (thirdNormalizeInto refs).depth (fun _ => 1) path.2 ≤ 43
  rw [thirdMetricPrefixInto_depth]
  omega

/-- Every actual suffix stage restores the complete borrowed interface on its incoming state. -/
theorem thirdNormalizeInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (thirdNormalizeInto refs).BorrowedRestored Reference state
      ((thirdNormalizeInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact normalizeMagnitude_borrowedRestored _ _ _ Reference state
  · apply Circuit.borrowedRestored_seq
    · exact numeratorSignInto_borrowedRestored refs Reference _
    · exact Circuit.borrowedRestored_seq _ _ _
        (RoundedDiv.body_borrowedRestored _ Reference _)
        (LatticeArithmetic.pointReduce_borrowedRestored _ _ _ _ Reference _)

/-- The full actual third phase restores borrowed correlations jointly with external references. -/
theorem thirdInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (thirdInto refs).BorrowedRestored Reference state
      ((thirdInto refs).execute Reference state) := by
  exact Circuit.borrowedRestored_seq _ _ state
    (thirdMetricPrefixInto_borrowedRestored refs Reference state)
    (thirdNormalizeInto_borrowedRestored refs Reference _)

/-- The nineteen actual prefix instructions use the caller's original complete context. -/
theorem thirdMetricPrefixInto_visited (refs : Refs ctx width)
    (path : (thirdMetricPrefixInto refs).Path) :
    (thirdMetricPrefixInto refs).visitedContexts path = List.replicate 19 ctx := rfl

/-- The actual sign-normalizing suffix visits only the original supplied context. -/
theorem thirdNormalizeInto_visited (refs : Refs ctx width)
    (path : (thirdNormalizeInto refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (thirdNormalizeInto refs).visitedContexts path) : visited = ctx := by
  rcases path with ⟨normalizationPath, signPath, divisionPath, reductionPath⟩
  change visited ∈ (_ ++ (_ ++ (_ ++ _))) at present
  simp only [List.mem_append] at present
  rcases present with normalized | corrected | divided | reduced
  · rw [normalizeMagnitude_visited] at normalized
    split at normalized <;>
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using normalized
  · rw [numeratorSignInto_visited] at corrected
    split at corrected <;>
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using corrected
  · exact RoundedDiv.body_visited refs.division divisionPath visited divided
  · simpa only [LatticeArithmetic.pointReduce_visited, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using reduced

/-- The complete actual third phase visits only the original caller context. -/
theorem thirdInto_visited (refs : Refs ctx width) (path : (thirdInto refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (thirdInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  rcases List.mem_append.mp present with metric | suffix
  · rw [thirdMetricPrefixInto_visited] at metric
    exact (List.mem_replicate.mp metric).2
  · exact thirdNormalizeInto_visited refs path.2 visited suffix

/-- Resident accounting counts all original quantum dimensions and classical cells. -/
theorem thirdInto_resident_le (refs : Refs ctx width) (path : (thirdInto refs).Path) :
    (thirdInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [thirdInto_visited refs path visited present]

/-- Auxiliary accounting retains the supplied roles throughout the complete actual phase. -/
theorem thirdInto_auxiliary_le (refs : Refs ctx width) (path : (thirdInto refs).Path) :
    (thirdInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [thirdInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
