/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.First.Correctness
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Resources
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Restoration

/-!
# Actual first-coordinate nearest-plane resources

The two five-instruction refreshes, at most thirteen division instructions and
six coordinate-update instructions give the independent bound twenty-nine.
All live storage is already supplied by the caller; borrowed restoration holds
jointly with arbitrary external references, without arithmetic preconditions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent native event formula for two refreshes, signed division and three reductions. -/
def phaseTrace (width : Nat) (magnitudeNegative correctionNegative restoreNegative : Bool) :
    List (Resource.Event model) :=
  ([.wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .add width,
    .wordBinary .mulLow width, .wordBinary .add width,
    .wordBinary .mulLow width, .wordBinary .mulLow width, .wordBinary .add width,
    .wordBinary .mulLow width, .wordBinary .add width] :
    List Resource.ClassicalOpLabel).map
      (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label)) ++
    SignedWord.RoundedDiv.bodyTrace width magnitudeNegative correctionNegative restoreNegative ++
    ([.wordBinary .mulLow width, .wordBinary .sub width,
      .wordBinary .mulLow width, .wordBinary .sub width,
      .wordBinary .mulLow width, .wordBinary .sub width] :
      List Resource.ClassicalOpLabel).map
      (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label))

/-- Every real path matches the independent event formula with its recorded division flags. -/
lemma firstInto_events (refs : Refs ctx width) (path : (firstInto refs).Path) :
    (firstInto refs).eventTrace path =
      let divided := path.2.2.1
      phaseTrace width divided.1.1.2.1.toBool divided.2.1.2.1.1.toBool
        divided.2.2.2.2.1.toBool := by
  rcases path with ⟨dotPath, normPath, divisionPath, reductionPath⟩
  change _ ++ (_ ++ (_ ++ _)) = _
  rw [LatticeDotRefresh.refreshInto_events, LatticeNormRefresh.refreshInto_events,
    SignedWord.RoundedDiv.body_events, LatticeArithmetic.pointReduce_events]
  simp only [phaseTrace, List.cons_append, List.nil_append]
  rfl

/-- Actual native multiplicities are the pool of that same independent instruction formula. -/
lemma firstInto_resourcePool (refs : Refs ctx width) (path : (firstInto refs).Path) :
    (firstInto refs).resourcePool path =
      let divided := path.2.2.1
      ResourcePool.ofList (phaseTrace width divided.1.1.2.1.toBool
        divided.2.1.2.1.1.toBool divided.2.2.2.2.1.toBool) := by
  change ResourcePool.ofList ((firstInto refs).eventTrace path) = _
  rw [firstInto_events]

/-- Every actual first-coordinate path executes at most twenty-nine native instructions. -/
lemma firstInto_eventCount_le (refs : Refs ctx width) (path : (firstInto refs).Path) :
    ((firstInto refs).eventTrace path).length ≤ 29 := by
  rcases path with ⟨dotPath, normPath, divisionPath, reductionPath⟩
  have divisionBound := SignedWord.RoundedDiv.body_eventCount_le refs.division divisionPath
  change List.length (_ ++ (_ ++ (_ ++ _))) ≤ 29
  rw [LatticeDotRefresh.refreshInto_events, LatticeNormRefresh.refreshInto_events,
    LatticeArithmetic.pointReduce_events]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The actual unit-duration dependency depth includes both refreshes, division and reduction. -/
lemma firstInto_depth_le (refs : Refs ctx width) (path : (firstInto refs).Path) :
    (firstInto refs).depth (fun _ => 1) path ≤ 29 := by
  rcases path with ⟨dotPath, normPath, divisionPath, reductionPath⟩
  have divisionBound := SignedWord.RoundedDiv.body_depth_le refs.division divisionPath
  have reductionDepth : (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.first refs.target refs.reduceProduct).depth (fun _ => 1) reductionPath = 6 := rfl
  change (LatticeDotRefresh.refreshInto refs.target refs.basis.first (numeratorDotRefs refs)).depth
    (fun _ => 1) dotPath +
    ((LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs)).depth
      (fun _ => 1) normPath +
      ((SignedWord.RoundedDiv.body refs.division).depth (fun _ => 1) divisionPath +
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct).depth (fun _ => 1) reductionPath)) ≤ 29
  rw [LatticeDotRefresh.refreshInto_depth, LatticeNormRefresh.refreshInto_depth, reductionDepth]
  omega

/-- Every stage preserves the complete borrowed interface on its actual incoming state. -/
lemma firstInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (firstInto refs).BorrowedRestored Reference state
      ((firstInto refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference state
  · apply Circuit.borrowedRestored_seq (environment := environment)
    · exact LatticeNormRefresh.refreshInto_borrowedRestored _ _ Reference _
    · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
        (SignedWord.RoundedDiv.body_borrowedRestored _ Reference _)
        (LatticeArithmetic.pointReduce_borrowedRestored _ _ _ _ Reference _)

/-- Every visited context of the complete first phase is the original caller context. -/
lemma firstInto_visited (refs : Refs ctx width) (path : (firstInto refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (firstInto refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨dotPath, normPath, divisionPath, reductionPath⟩
  change visited ∈ (_ ++ (_ ++ (_ ++ _))) at present
  simp only [List.mem_append] at present
  rcases present with dot | norm | division | reduction
  · simpa only [LatticeDotRefresh.refreshInto_visited, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using dot
  · simpa only [LatticeNormRefresh.refreshInto_visited, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using norm
  · exact SignedWord.RoundedDiv.body_visited refs.division divisionPath visited division
  · simpa only [LatticeArithmetic.pointReduce_visited, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using reduction

/-- Resident space includes all original classical cells and every quantum dimension. -/
lemma firstInto_resident_le (refs : Refs ctx width) (path : (firstInto refs).Path) :
    (firstInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [firstInto_visited refs path visited present]

/-- Auxiliary roles are unchanged across the complete actual first phase. -/
lemma firstInto_auxiliary_le (refs : Refs ctx width) (path : (firstInto refs).Path) :
    (firstInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [firstInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst
