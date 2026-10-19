/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.RowLoading.Correctness

/-!
# Actual original first-row loading resources

Both native resizes precede self-XOR and increment of the original third
coordinate. The exact four-instruction formula also gives unit-duration depth,
with the original complete live context and joint borrowed restoration.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N width : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent native formula for both original source resizes and third-coordinate loading. -/
def firstRowTrace (N width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (BatchMachine.JWidth N) width))] ++
    ([.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize (BatchMachine.JWidth N) width))] ++
      Word.PowerOfTwo.powerTrace (model := model) width 0)

/-- Every actual first-row path emits exactly the independent four-instruction formula. -/
lemma loadFirstBasisRowInto_events (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).eventTrace path = firstRowTrace N width := by
  change _ ++ (_ ++ _) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    Word.PowerOfTwo.into_events]
  rfl

/-- Actual original row-loading multiplicities equal the full independent native formula. -/
lemma loadFirstBasisRowInto_resourcePool (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).resourcePool path =
      ResourcePool.ofList (firstRowTrace N width) :=
  congrArg ResourcePool.ofList (loadFirstBasisRowInto_events pair output path)

/-- Both actual source reads and initialized third-coordinate loading cost four instructions. -/
lemma loadFirstBasisRowInto_eventCount (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    ((loadFirstBasisRowInto pair output).eventTrace path).length = 4 := by
  rw [loadFirstBasisRowInto_events]
  rfl

/-- The complete actual first-row loader has four sequential native unit-duration dependencies. -/
lemma loadFirstBasisRowInto_depth (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).depth (fun _ => 1) path = 4 := by
  change 1 + (1 + (Word.PowerOfTwo.into 0 output.b13).depth (fun _ => 1) path.2.2) = 4
  have loaded := Word.PowerOfTwo.into_depth 0 output.b13 path.2.2
  omega

/-- Actual first-row loading jointly restores every borrowed entry and external correlation. -/
lemma loadFirstBasisRowInto_borrowedRestored (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadFirstBasisRowInto pair output).BorrowedRestored Reference state
      ((loadFirstBasisRowInto pair output).execute environment Reference state) := by
  exact Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (Circuit.borrowedRestored_classical (environment := environment) _ state)
    (Circuit.borrowedRestored_seq
      (environment := environment) _ _ _ (Circuit.borrowedRestored_classical (environment :=
      environment) _ _)
      (Word.PowerOfTwo.into_borrowedRestored 0 output.b13 Reference _))

/-- Every actual native row-loading instruction keeps the complete original context live. -/
lemma loadFirstBasisRowInto_visited (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (loadFirstBasisRowInto pair output).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++ ([ctx] ++
    (Word.PowerOfTwo.into 0 output.b13).visitedContexts path.2.2) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with first | second | third
  · exact first
  · exact second
  · exact Word.PowerOfTwo.into_visited 0 output.b13 path.2.2 visited third

/-- The actual original first-row loader requires no additional resident entry. -/
lemma loadFirstBasisRowInto_resident_le (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [loadFirstBasisRowInto_visited pair output path visited present]

/-- Every original auxiliary entry remains counted during actual first-row loading. -/
lemma loadFirstBasisRowInto_auxiliary_le (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [loadFirstBasisRowInto_visited pair output path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading
