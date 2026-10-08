/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Resources

/-!
# Native quadratic-prefix resources and joint borrowed restoration
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Independent chronological native instructions preparing the original center and square. -/
def prepareTrace (shortWidth : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize shortWidth (centerWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (centerWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.mulFull (centerWidth shortWidth) (centerWidth shortWidth)))]

/-- The original five-operation prefix records the actual truncated-subtraction branch. -/
def discriminantTrace (shortWidth : Nat) (underflow : Bool) : List (Resource.Event model) :=
  prepareTrace shortWidth ++ NatSub.nativeTrace (discriminantWidth shortWidth) underflow

/-- Placement-independent coordinates include the original underflow branch maximum. -/
def discriminantEnvelope (shortWidth : Nat) : ResourcePool model :=
  ResourcePool.ofList (prepareTrace shortWidth) +
    NatSub.eventEnvelope (discriminantWidth shortWidth)

/-- The three selected preparation instructions have their original chronological trace. -/
theorem prepareInto_events (refs : Refs ctx shortWidth) (path : (prepareInto refs).Path) :
    (prepareInto refs).eventTrace path = prepareTrace shortWidth := by
  change (BitWord.instruction (execution := model) (resizeOp refs)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (incrementOp refs)).eventTrace path.2.1 ++
      (BitWord.instruction (execution := model) (squareOp refs)).eventTrace path.2.2) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Every actual prefix path emits exactly its five independently specified native events. -/
theorem discriminantInto_events (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    (discriminantInto refs).eventTrace path =
      discriminantTrace shortWidth path.2.2.1.toBool := by
  change (prepareInto refs).eventTrace path.1 ++
    (NatSub.into refs.subtract).eventTrace path.2 = _
  rw [prepareInto_events, NatSub.into_events]
  rfl

/-- Native multiplicities are extracted from the same five-operation execution path. -/
theorem discriminantInto_resourcePool (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    (discriminantInto refs).resourcePool path =
      ResourcePool.ofList (discriminantTrace shortWidth path.2.2.1.toBool) :=
  congrArg ResourcePool.ofList (discriminantInto_events refs path)

/-- The actual native coordinates meet the original independent comparison-branch envelope. -/
theorem discriminantInto_pool_le (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    (discriminantInto refs).resourcePool path ≤ discriminantEnvelope shortWidth := by
  change ResourcePool.ofList ((prepareInto refs).eventTrace path.1 ++
    (NatSub.into refs.subtract).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, prepareInto_events]
  exact add_le_add le_rfl (NatSub.into_pool_le refs.subtract path.2)

/-- Widening, increment, full square, comparison and the selected subtraction write all execute. -/
theorem discriminantInto_eventCount (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    ((discriminantInto refs).eventTrace path).length = 5 := by
  rw [discriminantInto_events]
  simp only [discriminantTrace, List.length_append]
  rfl

/-- The five original native instructions retain their sequential dependency depth. -/
theorem discriminantInto_depth (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    (discriminantInto refs).depth (fun _ => 1) path = 5 := by
  change 3 + (NatSub.into refs.subtract).depth (fun _ => 1) path.2 = _
  rw [NatSub.into_depth]

/-- Each native prefix operation keeps the complete original runtime context live. -/
theorem discriminantInto_visited (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    (discriminantInto refs).visitedContexts path = List.replicate 5 ctx := by
  change [ctx, ctx, ctx] ++ (NatSub.into refs.subtract).visitedContexts path.2 = _
  rw [NatSub.into_visited]
  rfl

/-- All supplied classical and quantum storage remains included in resident accounting. -/
theorem discriminantInto_resident_le (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    (discriminantInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [discriminantInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Every original auxiliary role remains live through the discriminant computation. -/
theorem discriminantInto_auxiliary_le (refs : Refs ctx shortWidth)
    (path : (discriminantInto refs).Path) :
    (discriminantInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [discriminantInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- All five actual native operations restore borrowed systems jointly with external references. -/
theorem discriminantInto_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (discriminantInto refs).BorrowedRestored Reference state
      ((discriminantInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_classical
        (BitWord.selectedApplication (execution := model) (resizeOp refs)) _
    · exact Circuit.borrowedRestored_seq _ _ _
        (Circuit.borrowedRestored_classical
          (BitWord.selectedApplication (execution := model) (incrementOp refs)) _)
        (Circuit.borrowedRestored_classical
          (BitWord.selectedApplication (execution := model) (squareOp refs)) _)
  · exact NatSub.into_borrowedRestored refs.subtract Reference _

/-- Independent original prefix and finite-square-root native coordinate allowance. -/
def eventEnvelope (shortWidth : Nat) : ResourcePool model :=
  discriminantEnvelope shortWidth + NatSqrt.eventEnvelope (discriminantWidth shortWidth)

/-- Chronological original prefix and square-root formula with the actual underflow decision. -/
def nativeTrace (shortWidth : Nat) (underflow : Bool) : List (Resource.Event model) :=
  discriminantTrace shortWidth underflow ++ NatSqrt.driverTrace (discriminantWidth shortWidth)

/-- The actual complete path emits the specified prefix and finite-square-root instructions. -/
theorem into_events (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path = nativeTrace shortWidth path.1.2.2.1.toBool := by
  change (discriminantInto refs).eventTrace path.1 ++
    (NatSqrt.into refs.sqrt).eventTrace path.2 = _
  rw [discriminantInto_events, NatSqrt.into_events]
  rfl

/-- Complete native multiplicities are counted from the same actual execution path. -/
theorem into_resourcePool (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path =
      ResourcePool.ofList (nativeTrace shortWidth path.1.2.2.1.toBool) :=
  congrArg ResourcePool.ofList (into_events refs path)

/-- Actual native coordinates meet the independent original prefix and square-root allowance. -/
theorem into_pool_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope shortWidth := by
  change ResourcePool.ofList ((discriminantInto refs).eventTrace path.1 ++
    (NatSqrt.into refs.sqrt).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (discriminantInto_pool_le refs path.1)
    (NatSqrt.into_pool_le refs.sqrt path.2)

/-- The actual count charges all prefix, initialization, refinement and caller-output writes. -/
theorem into_eventCount (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    ((into refs).eventTrace path).length = 7 * discriminantWidth shortWidth + 9 := by
  change ((discriminantInto refs).eventTrace path.1 ++
    (NatSqrt.into refs.sqrt).eventTrace path.2).length = _
  rw [List.length_append, discriminantInto_eventCount, NatSqrt.into_eventCount]
  have atLeastTwo := discriminantWidth_two_le shortWidth
  omega

/-- All original prefix and square-root operations retain their sequential dependency depth. -/
theorem into_depth (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path = 7 * discriminantWidth shortWidth + 9 := by
  change (discriminantInto refs).depth (fun _ => 1) path.1 +
    (NatSqrt.into refs.sqrt).depth (fun _ => 1) path.2 = _
  rw [discriminantInto_depth, NatSqrt.into_depth]
  have atLeastTwo := discriminantWidth_two_le shortWidth
  omega

/-- The complete circuit keeps every original caller cell and quantum system live. -/
theorem into_visited (refs : Refs ctx shortWidth) (path : (into refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (discriminantInto refs).visitedContexts path.1 ++
    (NatSqrt.into refs.sqrt).visitedContexts path.2 at present
  rcases List.mem_append.mp present with prefixPresent | sqrtPresent
  · rw [discriminantInto_visited] at prefixPresent
    exact (List.mem_replicate.mp prefixPresent).2
  · exact NatSqrt.into_visited refs.sqrt path.2 visited sqrtPresent

/-- Resident peak includes all supplied classical cells and quantum dimensions throughout. -/
theorem into_resident_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Auxiliary peak retains the original workspace roles during the complete computation. -/
theorem into_auxiliary_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Complete prefix execution restores borrowed storage jointly with every external reference. -/
theorem into_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact discriminantInto_borrowedRestored refs Reference state
  · exact NatSqrt.into_borrowedRestored refs.sqrt Reference _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix
