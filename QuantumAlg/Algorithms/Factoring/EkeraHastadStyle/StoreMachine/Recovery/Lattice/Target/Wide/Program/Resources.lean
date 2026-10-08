/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Program.Correctness

/-!
# Actual native wide-target resources

The independent formula includes two resize-and-shift preimages and both
selected centered coordinates. Its actual paths use at most `2*m + 16` native
operations while retaining every original context entry and borrowed system.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent native formula of both original common-width scaled preimages. -/
def preimagesTrace (m ell width : Nat) : List (Resource.Event model) :=
  Word.PowerOfTwo.Scale.scaleTrace ell width m ++ Word.PowerOfTwo.Scale.scaleTrace ell width m

/-- Independent native formula of both preimages followed by both selected centered coordinates. -/
def targetTrace (m ell width : Nat) (firstNegates secondNegates : Bool) :
    List (Resource.Event model) :=
  preimagesTrace m ell width ++ LatticeTargetPoint.pointTrace width firstNegates secondNegates

/-- Both actual preimage paths emit precisely the independent resize-and-shift formula. -/
theorem preimagesInto_events (refs : Refs ctx m ell width) (path : (preimagesInto refs).Path) :
    (preimagesInto refs).eventTrace path = preimagesTrace m ell width :=
  congrArg₂ List.append (Word.PowerOfTwo.Scale.into_events m refs.first.k refs.first.scaled path.1)
    (Word.PowerOfTwo.Scale.into_events m refs.second.k refs.second.scaled path.2)

/-- The complete actual wide-target path emits the independently selected native formula. -/
theorem loadTargetInto_events (refs : Refs ctx m ell width) (path : (loadTargetInto refs).Path) :
    (loadTargetInto refs).eventTrace path = targetTrace m ell width
      (LatticeTarget.selectedNegation refs.target.first path.2.1.2)
      (LatticeTarget.selectedNegation refs.target.second path.2.2.2) :=
  congrArg₂ List.append (preimagesInto_events refs path.1)
    (LatticeTargetPoint.loadTargetPointInto_events refs.target path.2)

/-- Actual wide-target native multiplicities equal the independent selected instruction formula. -/
theorem loadTargetInto_resourcePool (refs : Refs ctx m ell width)
    (path : (loadTargetInto refs).Path) :
    (loadTargetInto refs).resourcePool path = ResourcePool.ofList (targetTrace m ell width
      (LatticeTarget.selectedNegation refs.target.first path.2.1.2)
      (LatticeTarget.selectedNegation refs.target.second path.2.2.2)) :=
  congrArg ResourcePool.ofList (loadTargetInto_events refs path)

/-- Placement-independent coordinate envelope of both preimages and centered target calls. -/
def eventEnvelope (m ell width : Nat) : ResourcePool model :=
  ResourcePool.ofList (preimagesTrace m ell width) + LatticeTargetPoint.eventEnvelope width

/-- Every actual wide-target pool lies in the independently specified native coordinate envelope. -/
theorem loadTargetInto_resourcePool_le (refs : Refs ctx m ell width)
    (path : (loadTargetInto refs).Path) :
    (loadTargetInto refs).resourcePool path ≤ eventEnvelope m ell width := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append, preimagesInto_events]
  exact add_le_add le_rfl
    (LatticeTargetPoint.loadTargetPointInto_resourcePool_le refs.target path.2)

/-- Actual preimage construction performs exactly two resizes and twice the prescribed shifts. -/
theorem preimagesInto_eventCount (refs : Refs ctx m ell width)
    (path : (preimagesInto refs).Path) :
    ((preimagesInto refs).eventTrace path).length = 2 * (m + 1) := by
  have first := Word.PowerOfTwo.Scale.into_eventCount m refs.first.k refs.first.scaled path.1
  have second := Word.PowerOfTwo.Scale.into_eventCount m refs.second.k refs.second.scaled path.2
  change List.length (_ ++ _) = _
  rw [List.length_append]
  change ((Word.PowerOfTwo.Scale.into m refs.first.k refs.first.scaled).eventTrace path.1).length +
    ((Word.PowerOfTwo.Scale.into m refs.second.k refs.second.scaled).eventTrace path.2).length = _
  omega

/-- The complete actual wide target uses at most two shifts per bit and sixteen other operations. -/
theorem loadTargetInto_eventCount_le (refs : Refs ctx m ell width)
    (path : (loadTargetInto refs).Path) :
    ((loadTargetInto refs).eventTrace path).length ≤ 2 * m + 16 := by
  have preimages := preimagesInto_eventCount refs path.1
  have target := LatticeTargetPoint.loadTargetPointInto_eventCount_le refs.target path.2
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  omega

/-- Unit-duration depth includes both original native preimage sequences. -/
theorem preimagesInto_depth (refs : Refs ctx m ell width) (path : (preimagesInto refs).Path) :
    (preimagesInto refs).depth (fun _ => 1) path = 2 * (m + 1) := by
  have first := Word.PowerOfTwo.Scale.into_depth m refs.first.k refs.first.scaled path.1
  have second := Word.PowerOfTwo.Scale.into_depth m refs.second.k refs.second.scaled path.2
  change (Word.PowerOfTwo.Scale.into m refs.first.k refs.first.scaled).depth (fun _ => 1) path.1 +
    (Word.PowerOfTwo.Scale.into m refs.second.k refs.second.scaled).depth (fun _ => 1) path.2 = _
  omega

/-- Unit-duration depth includes actual preimages, comparisons and selected arithmetic. -/
theorem loadTargetInto_depth_le (refs : Refs ctx m ell width) (path : (loadTargetInto refs).Path) :
    (loadTargetInto refs).depth (fun _ => 1) path ≤ 2 * m + 16 := by
  have preimages := preimagesInto_depth refs path.1
  have target := LatticeTargetPoint.loadTargetPointInto_depth_le refs.target path.2
  change (preimagesInto refs).depth (fun _ => 1) path.1 +
    (LatticeTargetPoint.loadTargetPointInto refs.target).depth (fun _ => 1) path.2 ≤ _
  omega

/-- Both actual preimages restore every borrowed system jointly with the external reference. -/
theorem preimagesInto_borrowedRestored (refs : Refs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preimagesInto refs).BorrowedRestored Reference state
      ((preimagesInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Word.PowerOfTwo.Scale.into_borrowedRestored m refs.first.k refs.first.scaled Reference state)
    (Word.PowerOfTwo.Scale.into_borrowedRestored m refs.second.k refs.second.scaled Reference _)

/-- The complete actual wide-target call restores all borrowed-reference correlations. -/
theorem loadTargetInto_borrowedRestored (refs : Refs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadTargetInto refs).BorrowedRestored Reference state
      ((loadTargetInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (preimagesInto_borrowedRestored refs Reference state)
    (LatticeTargetPoint.loadTargetPointInto_borrowedRestored refs.target Reference _)

/-- Every original context entry remains live throughout both actual preimages. -/
theorem preimagesInto_visited (refs : Refs ctx m ell width) (path : (preimagesInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (preimagesInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim
    (Word.PowerOfTwo.Scale.into_visited m refs.first.k refs.first.scaled path.1 visited)
    (Word.PowerOfTwo.Scale.into_visited m refs.second.k refs.second.scaled path.2 visited)

/-- The actual preimage and centering calls retain the entire original supplied context. -/
theorem loadTargetInto_visited (refs : Refs ctx m ell width) (path : (loadTargetInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (loadTargetInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim (preimagesInto_visited refs path.1 visited)
    (LatticeTargetPoint.loadTargetPointInto_visited refs.target path.2 visited)

/-- Every original resident entry remains counted throughout actual wide-target loading. -/
theorem loadTargetInto_resident_le (refs : Refs ctx m ell width)
    (path : (loadTargetInto refs).Path) :
    (loadTargetInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [loadTargetInto_visited refs path visited present]

/-- Every original auxiliary role remains counted throughout actual wide-target loading. -/
theorem loadTargetInto_auxiliary_le (refs : Refs ctx m ell width)
    (path : (loadTargetInto refs).Path) :
    (loadTargetInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [loadTargetInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine
