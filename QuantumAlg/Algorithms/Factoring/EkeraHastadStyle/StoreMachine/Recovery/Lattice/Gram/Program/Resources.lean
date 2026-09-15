/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program

/-!
# Actual Gram refresh resources

Six native dot refreshes cost exactly thirty operations and unit-duration
serial depth thirty. All original classical and quantum resources remain live.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent thirty-instruction formula for the six overwritten Gram outputs. -/
def gramTrace (width : Nat) : List (Resource.Event kind) :=
  (List.replicate 6 [.classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .add width),
    .classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .add width)]).flatten

/-- Every actual Gram path has exactly the independent thirty-instruction trace. -/
theorem refreshInto_events (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (path : (refreshInto basis refs).Path) :
    (refreshInto basis refs).eventTrace path = gramTrace width := rfl

/-- Actual native multiplicities are those of the independent Gram instruction formula. -/
theorem refreshInto_resourcePool (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (path : (refreshInto basis refs).Path) :
    (refreshInto basis refs).resourcePool path = ResourcePool.ofList (gramTrace width) := rfl

/-- Exactly thirty native operations execute in the complete actual Gram refresh. -/
theorem refreshInto_eventCount (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (path : (refreshInto basis refs).Path) :
    ((refreshInto basis refs).eventTrace path).length = 30 := rfl

/-- The actual serial dependency depth is thirty at unit instruction duration. -/
theorem refreshInto_depth (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (path : (refreshInto basis refs).Path) :
    (refreshInto basis refs).depth (fun _ => 1) path = 30 := rfl

/-- All six actual refreshes restore borrowed correlations jointly with external references. -/
theorem refreshInto_borrowedRestored (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (refreshInto basis refs).BorrowedRestored Reference state
      ((refreshInto basis refs).execute Reference state) := by
  refine Circuit.borrowedRestored_seq (entryInto basis refs .g11) _ state
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (entryInto basis refs .g21) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (entryInto basis refs .g31) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (entryInto basis refs .g22) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (entryInto basis refs .g32) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  exact LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _

/-- All thirty actual instructions use the original complete context. -/
theorem refreshInto_visited (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (path : (refreshInto basis refs).Path) :
    (refreshInto basis refs).visitedContexts path = List.replicate 30 ctx := rfl

/-- Resident accounting includes the complete supplied quantum and classical storage. -/
theorem refreshInto_resident_le (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto basis refs).Path) :
    (refreshInto basis refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [refreshInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary accounting retains all original cell roles throughout the actual computation. -/
theorem refreshInto_auxiliary_le (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto basis refs).Path) :
    (refreshInto basis refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [refreshInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine
