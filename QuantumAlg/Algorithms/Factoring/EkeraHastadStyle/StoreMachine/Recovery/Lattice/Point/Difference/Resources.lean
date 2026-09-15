/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Difference

/-!
# Actual point-difference resources

The complete native trace is three subtractions. Every supplied resource stays
live, and borrowed correlations are restored jointly with external references.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent instruction formula of the original coordinatewise subtraction. -/
def differenceTrace (width : Nat) : List (Resource.Event kind) :=
  List.replicate 3 (.classicalOperation (.wordBinary .sub width))

/-- Every actual path emits exactly the three independently specified subtraction events. -/
theorem pointDifferenceInto_events (refs : Refs ctx width)
    (path : (pointDifferenceInto refs).Path) :
    (pointDifferenceInto refs).eventTrace path = differenceTrace width := rfl

/-- Native multiplicity comes from the same independent three-subtraction formula. -/
theorem pointDifferenceInto_resourcePool (refs : Refs ctx width)
    (path : (pointDifferenceInto refs).Path) :
    (pointDifferenceInto refs).resourcePool path =
      ResourcePool.ofList (differenceTrace width) := rfl

/-- Actual serial dependency depth is exactly three at unit native instruction duration. -/
theorem pointDifferenceInto_depth (refs : Refs ctx width)
    (path : (pointDifferenceInto refs).Path) :
    (pointDifferenceInto refs).depth (fun _ => 1) path = 3 := rfl

/-- All three real writes preserve the full borrowed-reference joint state. -/
theorem pointDifferenceInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pointDifferenceInto refs).BorrowedRestored Reference state
      ((pointDifferenceInto refs).execute Reference state) := by
  refine Circuit.borrowedRestored_seq (.classical (differenceOp refs .first)) _ state
    (Circuit.borrowedRestored_classical _ state) ?_
  exact Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _)
    (Circuit.borrowedRestored_classical _ _)

/-- Each of the three actual instructions visits the original caller context. -/
theorem pointDifferenceInto_visited (refs : Refs ctx width)
    (path : (pointDifferenceInto refs).Path) :
    (pointDifferenceInto refs).visitedContexts path = List.replicate 3 ctx := rfl

/-- The complete supplied resident quantum and classical storage remains counted. -/
theorem pointDifferenceInto_resident_le (refs : Refs ctx width)
    (path : (pointDifferenceInto refs).Path) :
    (pointDifferenceInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [pointDifferenceInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary accounting retains the original roles through the entire actual subtraction. -/
theorem pointDifferenceInto_auxiliary_le (refs : Refs ctx width)
    (path : (pointDifferenceInto refs).Path) :
    (pointDifferenceInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [pointDifferenceInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine
