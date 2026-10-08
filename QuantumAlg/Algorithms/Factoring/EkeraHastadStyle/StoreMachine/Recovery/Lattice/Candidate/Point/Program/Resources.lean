/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Point.Program.Correctness

/-!
# Actual candidate-point native resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent five-instruction multiply-add formula for each original basis column. -/
def coordinateTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width))]

/-- Independent three-addition coefficient prefix and three original column dot products. -/
def candidateTrace (width : Nat) : List (Resource.Event model) :=
  List.replicate 3 (.classicalOperation
    (BitWord.selectedCoordinate (execution := model) (.wordBinary .add width))) ++
    (coordinateTrace width ++ (coordinateTrace width ++ coordinateTrace width))

/-- Every actual candidate path emits exactly the independently specified native instructions. -/
theorem candidatePointInto_events (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).eventTrace path = candidateTrace width := by
  simp only [candidatePointInto, coefficientInto, pointInto, coordinateCombination,
    Circuit.eventTrace, BitWord.bitWord_instruction_eventTrace,
    LatticeDotRefresh.refreshInto_events]
  rfl

/-- The original candidate formula accounts for every actual native operation multiplicity. -/
theorem candidatePointInto_resourcePool (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).resourcePool path = ResourcePool.ofList (candidateTrace width) :=
  congrArg ResourcePool.ofList (candidatePointInto_events refs path)

/-- The actual path uses exactly eighteen original native arithmetic instructions. -/
theorem candidatePointInto_eventCount (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    ((candidatePointInto refs).eventTrace path).length = 18 := by
  rw [candidatePointInto_events]
  rfl

/-- Unit-duration dependency depth charges all eighteen sequential instructions. -/
theorem candidatePointInto_depth (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).depth (fun _ => 1) path = 18 := rfl

/-- Actual coefficient addition restores the complete borrowed-reference joint state. -/
theorem coefficientInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (coefficientInto refs).BorrowedRestored Reference state
      ((coefficientInto refs).execute Reference state) := by
  refine Circuit.borrowedRestored_seq
    (BitWord.instruction (execution := model) (coefficientOp refs .first)) _ state
    (Circuit.borrowedRestored_classical (model := model) _ state) ?_
  exact Circuit.borrowedRestored_seq _ _ _
    (Circuit.borrowedRestored_classical (model := model) _ _)
    (Circuit.borrowedRestored_classical (model := model) _ _)

/-- All three actual column dot products preserve every borrowed-reference correlation. -/
theorem pointInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pointInto refs).BorrowedRestored Reference state
      ((pointInto refs).execute Reference state) := by
  refine Circuit.borrowedRestored_seq (coordinateCombination refs .first) _ state
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference state) ?_
  exact Circuit.borrowedRestored_seq _ _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)

/-- The complete actual candidate restores the joint borrowed state with arbitrary references. -/
theorem candidatePointInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePointInto refs).BorrowedRestored Reference state
      ((candidatePointInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (coefficientInto_borrowedRestored refs Reference state)
    (pointInto_borrowedRestored refs Reference _)

/-- Every actual instruction retains the original supplied quantum and classical context. -/
theorem candidatePointInto_visited (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).visitedContexts path = List.replicate 18 ctx := rfl

/-- The full supplied resident storage remains counted throughout the actual candidate. -/
theorem candidatePointInto_resident_le (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [candidatePointInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary accounting retains all original roles and requires no additional storage. -/
theorem candidatePointInto_auxiliary_le (refs : Refs ctx width)
    (path : (candidatePointInto refs).Path) :
    (candidatePointInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [candidatePointInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine
