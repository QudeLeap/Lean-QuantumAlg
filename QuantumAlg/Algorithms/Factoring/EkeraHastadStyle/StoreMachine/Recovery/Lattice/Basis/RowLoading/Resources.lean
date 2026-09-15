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

/-- Independent native formula for both original source resizes and third-coordinate loading. -/
def firstRowTrace (N width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize (BatchMachine.JWidth N) width)] ++
    ([.classicalOperation (.wordResize (BatchMachine.JWidth N) width)] ++
      Word.PowerOfTwo.powerTrace width 0)

/-- Every actual first-row path emits exactly the independent four-instruction formula. -/
theorem loadFirstBasisRowInto_events (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).eventTrace path = firstRowTrace N width :=
  congrArg₂ List.append rfl (congrArg₂ List.append rfl
    (Word.PowerOfTwo.into_events 0 output.b13 path.2.2))

/-- Actual original row-loading multiplicities equal the full independent native formula. -/
theorem loadFirstBasisRowInto_resourcePool (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).resourcePool path =
      ResourcePool.ofList (firstRowTrace N width) :=
  congrArg ResourcePool.ofList (loadFirstBasisRowInto_events pair output path)

/-- Both actual source reads and initialized third-coordinate loading cost four instructions. -/
theorem loadFirstBasisRowInto_eventCount (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    ((loadFirstBasisRowInto pair output).eventTrace path).length = 4 := by
  rw [loadFirstBasisRowInto_events]
  rfl

/-- The complete actual first-row loader has four sequential native unit-duration dependencies. -/
theorem loadFirstBasisRowInto_depth (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).depth (fun _ => 1) path = 4 := by
  change 1 + (1 + (Word.PowerOfTwo.into 0 output.b13).depth (fun _ => 1) path.2.2) = 4
  have loaded := Word.PowerOfTwo.into_depth 0 output.b13 path.2.2
  omega

/-- Actual first-row loading jointly restores every borrowed entry and external correlation. -/
theorem loadFirstBasisRowInto_borrowedRestored (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (loadFirstBasisRowInto pair output).BorrowedRestored Reference state
      ((loadFirstBasisRowInto pair output).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (.classical (firstOp pair output))
    (firstRowTailInto pair output)
  · exact Circuit.borrowedRestored_classical _ state
  · exact Circuit.borrowedRestored_seq (.classical (secondOp pair output))
      (Word.PowerOfTwo.into 0 output.b13) _ (Circuit.borrowedRestored_classical _ _)
      (Word.PowerOfTwo.into_borrowedRestored 0 output.b13 Reference _)

/-- Every actual native row-loading instruction keeps the complete original context live. -/
theorem loadFirstBasisRowInto_visited (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path)
    (visited : RuntimeCtx kind)
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
theorem loadFirstBasisRowInto_resident_le (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [loadFirstBasisRowInto_visited pair output path visited present]

/-- Every original auxiliary entry remains counted during actual first-row loading. -/
theorem loadFirstBasisRowInto_auxiliary_le (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (path : (loadFirstBasisRowInto pair output).Path) :
    (loadFirstBasisRowInto pair output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [loadFirstBasisRowInto_visited pair output path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading
