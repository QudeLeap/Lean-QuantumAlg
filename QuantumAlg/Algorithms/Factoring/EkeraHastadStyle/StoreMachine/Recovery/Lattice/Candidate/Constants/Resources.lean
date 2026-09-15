/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Constants

/-!
# Actual shared candidate constant resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateConstants

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native zero initialization and original initialized upper-bound formula. -/
def loadTrace (m width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .bitXor width)] ++
    ClassicalRoutines.Word.PowerOfTwo.powerTrace width m

/-- Every actual shared-constant path emits the complete independent native formula. -/
theorem loadInto_events (m : Nat) (refs : Refs ctx width) (path : (loadInto m refs).Path) :
    (loadInto m refs).eventTrace path = loadTrace m width :=
  congrArg₂ List.append rfl
    (ClassicalRoutines.Word.PowerOfTwo.into_events m refs.upperBound path.2)

/-- Actual native multiplicities count zeroing, upper-bound initialization and every shift. -/
theorem loadInto_resourcePool (m : Nat) (refs : Refs ctx width) (path : (loadInto m refs).Path) :
    (loadInto m refs).resourcePool path = ResourcePool.ofList (loadTrace m width) :=
  congrArg ResourcePool.ofList (loadInto_events m refs path)

/-- Actual operation count includes both explicit initializations and the original power loading. -/
theorem loadInto_eventCount (m : Nat) (refs : Refs ctx width) (path : (loadInto m refs).Path) :
    ((loadInto m refs).eventTrace path).length = m + 3 := by
  change List.length ([_] ++ _) = _
  rw [List.length_append, ClassicalRoutines.Word.PowerOfTwo.into_eventCount]
  simp only [List.length_cons, List.length_nil]
  omega

/-- Unit-duration dependency depth charges the full original initialization sequence. -/
theorem loadInto_depth (m : Nat) (refs : Refs ctx width) (path : (loadInto m refs).Path) :
    (loadInto m refs).depth (fun _ => 1) path = m + 3 := by
  change 1 + (ClassicalRoutines.Word.PowerOfTwo.into m refs.upperBound).depth
    (fun _ => 1) path.2 = _
  rw [ClassicalRoutines.Word.PowerOfTwo.into_depth]
  omega

/-- Actual constant initialization restores the complete original borrowed-reference joint state. -/
theorem loadInto_borrowedRestored (m : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (loadInto m refs).BorrowedRestored Reference state
      ((loadInto m refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical _ state)
    (ClassicalRoutines.Word.PowerOfTwo.into_borrowedRestored m refs.upperBound Reference _)

/-- Every actual initialization instruction and shift retains the original supplied context. -/
theorem loadInto_visited (m : Nat) (refs : Refs ctx width) (path : (loadInto m refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (loadInto m refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++
    (ClassicalRoutines.Word.PowerOfTwo.into m refs.upperBound).visitedContexts path.2 at present
  simp only [List.mem_append, List.mem_singleton] at present
  exact present.elim id
    (ClassicalRoutines.Word.PowerOfTwo.into_visited m refs.upperBound path.2 visited)

/-- Resident accounting includes both constants and every other live caller resource. -/
theorem loadInto_resident_le (m : Nat) (refs : Refs ctx width) (path : (loadInto m refs).Path) :
    (loadInto m refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [loadInto_visited m refs path visited present]

/-- Auxiliary accounting retains original roles and allocates no additional cells. -/
theorem loadInto_auxiliary_le (m : Nat) (refs : Refs ctx width) (path : (loadInto m refs).Path) :
    (loadInto m refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [loadInto_visited m refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateConstants
