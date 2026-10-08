/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Resources
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Restoration

/-!
# Actual second-coordinate nearest-plane resources

The thirty-four-instruction metric prefix, three numerator instructions,
at most thirteen division instructions and six reductions give a bound of
fifty-six. Space and borrowed restoration use the same complete actual circuit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent formula for the cross product and five dot refreshes. -/
def prefixTrace (width : Nat) : List (Resource.Event model) :=
  ([.wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .sub width,
    .wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .sub width,
    .wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .sub width] ++
    (List.replicate 5 [.wordBinary .mulLow width, .wordBinary .mulLow width,
      .wordBinary .add width, .wordBinary .mulLow width, .wordBinary .add width]).flatten :
      List Resource.ClassicalOpLabel).map
    (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label))

/-- Independent two-product difference instruction formula. -/
def numeratorTrace (width : Nat) : List (Resource.Event model) :=
  ([.wordBinary .mulLow width, .wordBinary .mulLow width,
    .wordBinary .sub width] : List Resource.ClassicalOpLabel).map
    (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label))

/-- Independent full-phase formula parameterized by the recorded division flags. -/
def phaseTrace (width : Nat) (magnitudeNegative correctionNegative restoreNegative : Bool) :
    List (Resource.Event model) :=
  prefixTrace width ++ (numeratorTrace width ++
    (RoundedDiv.bodyTrace width magnitudeNegative correctionNegative restoreNegative ++
      ([.wordBinary .mulLow width, .wordBinary .sub width,
        .wordBinary .mulLow width, .wordBinary .sub width,
        .wordBinary .mulLow width, .wordBinary .sub width] :
        List Resource.ClassicalOpLabel).map
        (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label))))

/-- Every real metric-prefix path follows the independent thirty-four-instruction formula. -/
theorem secondPrefixInto_events (refs : Refs ctx width) (path : (secondPrefixInto refs).Path) :
    (secondPrefixInto refs).eventTrace path = prefixTrace width := by
  unfold secondPrefixInto secondMetricPrefixInto metricInto at path ⊢
  change (_ ++ (_ ++ _)) ++ (_ ++ (_ ++ _)) = _
  rw [LatticeCross.pointCrossInto_events, LatticeDotRefresh.refreshInto_events,
    LatticeDotRefresh.refreshInto_events, LatticeDotRefresh.refreshInto_events,
    LatticeDotRefresh.refreshInto_events, LatticeDotRefresh.refreshInto_events]
  rfl

/-- Every real numerator path follows the independent three-instruction formula. -/
theorem numeratorInto_events (refs : Refs ctx width) (path : (numeratorInto refs).Path) :
    (numeratorInto refs).eventTrace path = numeratorTrace width := by
  unfold numeratorInto LatticeCross.coordinateCross at path ⊢
  rw [ProductDifference.computeInto_events]
  rfl

/-- Actual native events follow the independent formula and the actual recorded division flags. -/
theorem secondInto_events (refs : Refs ctx width) (path : (secondInto refs).Path) :
    (secondInto refs).eventTrace path =
      let divided := path.2.2.1
      phaseTrace width divided.1.1.2.1.toBool divided.2.1.2.1.1.toBool
        divided.2.2.2.2.1.toBool := by
  rcases path with ⟨metricPath, numeratorPath, divisionPath, reductionPath⟩
  change _ ++ (_ ++ (_ ++ _)) = _
  rw [secondPrefixInto_events, numeratorInto_events, RoundedDiv.body_events,
    LatticeArithmetic.pointReduce_events]
  rfl

/-- Actual native multiplicities are the pool of the same independent instruction formula. -/
theorem secondInto_resourcePool (refs : Refs ctx width) (path : (secondInto refs).Path) :
    (secondInto refs).resourcePool path =
      let divided := path.2.2.1
      ResourcePool.ofList (phaseTrace width divided.1.1.2.1.toBool
        divided.2.1.2.1.1.toBool divided.2.2.2.2.1.toBool) := by
  change ResourcePool.ofList ((secondInto refs).eventTrace path) = _
  rw [secondInto_events]

/-- Every actual second-coordinate path executes at most fifty-six native instructions. -/
theorem secondInto_eventCount_le (refs : Refs ctx width) (path : (secondInto refs).Path) :
    ((secondInto refs).eventTrace path).length ≤ 56 := by
  rcases path with ⟨metricPath, numeratorPath, divisionPath, reductionPath⟩
  have divisionBound := RoundedDiv.body_eventCount_le refs.division divisionPath
  have prefixLength : (prefixTrace (model := model) width).length = 34 := rfl
  have numeratorLength : (numeratorTrace (model := model) width).length = 3 := rfl
  change List.length (_ ++ (_ ++ (_ ++ _))) ≤ 56
  rw [secondPrefixInto_events, numeratorInto_events, LatticeArithmetic.pointReduce_events]
  simp only [List.length_append, prefixLength, numeratorLength, List.length_cons, List.length_nil]
  omega

/-- Unit-duration depth includes every native metric, numerator, division and reduction step. -/
theorem secondInto_depth_le (refs : Refs ctx width) (path : (secondInto refs).Path) :
    (secondInto refs).depth (fun _ => 1) path ≤ 56 := by
  rcases path with ⟨metricPath, numeratorPath, divisionPath, reductionPath⟩
  have divisionBound := RoundedDiv.body_depth_le refs.division divisionPath
  have reductionDepth : (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.second refs.target refs.reduceProduct).depth (fun _ => 1) reductionPath = 6 := rfl
  change (secondPrefixInto refs).depth (fun _ => 1) metricPath +
    ((numeratorInto refs).depth (fun _ => 1) numeratorPath +
      ((RoundedDiv.body refs.division).depth (fun _ => 1) divisionPath +
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct).depth (fun _ => 1) reductionPath)) ≤ 56
  rw [secondPrefixInto_depth, numeratorInto_depth, reductionDepth]
  omega

/-- All four actual stages jointly preserve the complete borrowed interface. -/
theorem secondInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (secondInto refs).BorrowedRestored Reference state
      ((secondInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact secondPrefixInto_borrowedRestored refs Reference state
  · apply Circuit.borrowedRestored_seq
    · exact numeratorInto_borrowedRestored refs Reference _
    · exact Circuit.borrowedRestored_seq _ _ _
        (RoundedDiv.body_borrowedRestored _ Reference _)
        (LatticeArithmetic.pointReduce_borrowedRestored _ _ _ _ Reference _)

/-- Every actual metric instruction uses the original complete caller context. -/
theorem secondPrefixInto_visited (refs : Refs ctx width) (path : (secondPrefixInto refs).Path) :
    (secondPrefixInto refs).visitedContexts path = List.replicate 34 ctx := rfl

/-- Every actual numerator instruction uses the original complete caller context. -/
theorem numeratorInto_visited (refs : Refs ctx width) (path : (numeratorInto refs).Path) :
    (numeratorInto refs).visitedContexts path = List.replicate 3 ctx := rfl

/-- The complete actual second phase visits only the original supplied context. -/
theorem secondInto_visited (refs : Refs ctx width) (path : (secondInto refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (secondInto refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨metricPath, numeratorPath, divisionPath, reductionPath⟩
  change visited ∈ (_ ++ (_ ++ (_ ++ _))) at present
  simp only [List.mem_append] at present
  rcases present with metric | numerator | division | reduction
  · rw [secondPrefixInto_visited] at metric
    exact (List.mem_replicate.mp metric).2
  · rw [numeratorInto_visited] at numerator
    exact (List.mem_replicate.mp numerator).2
  · exact RoundedDiv.body_visited refs.division divisionPath visited division
  · simpa only [LatticeArithmetic.pointReduce_visited, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using reduction

/-- Resident accounting retains every original classical cell and quantum dimension. -/
theorem secondInto_resident_le (refs : Refs ctx width) (path : (secondInto refs).Path) :
    (secondInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [secondInto_visited refs path visited present]

/-- Auxiliary accounting uses the original supplied roles throughout the complete phase. -/
theorem secondInto_auxiliary_le (refs : Refs ctx width) (path : (secondInto refs).Path) :
    (secondInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [secondInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
