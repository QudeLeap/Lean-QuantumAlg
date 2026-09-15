/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Initialize.Program
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Independent native resources of the actual square-root initialization
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- Original independent resize, two clears, increment and fixed-shift coordinate budget. -/
def initializationEventEnvelope (inputWidth : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation
      (.wordResize inputWidth (workWidth inputWidth + workWidth inputWidth))) +
    (ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor (workWidth inputWidth))) +
      (ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor (workWidth inputWidth))) +
        (ResourcePool.singleton
            (.classicalOperation (.wordUnary .increment (workWidth inputWidth))) +
          ResourcePool.scale (inputWidth - 1) (ResourcePool.singleton
            (.classicalOperation (.wordUnary .shiftLeft (workWidth inputWidth)))))))

/-- Chronological original native instruction formula, independent of placement and store. -/
def initializationTrace (inputWidth : Nat) : List (Resource.Event kind) :=
  .classicalOperation (.wordResize inputWidth (workWidth inputWidth + workWidth inputWidth)) ::
    .classicalOperation (.wordBinary .bitXor (workWidth inputWidth)) ::
      .classicalOperation (.wordBinary .bitXor (workWidth inputWidth)) ::
        .classicalOperation (.wordUnary .increment (workWidth inputWidth)) ::
          List.replicate (inputWidth - 1)
            (.classicalOperation (.wordUnary .shiftLeft (workWidth inputWidth)))

/-- The actual initializer emits exactly the original independent instruction sequence. -/
theorem initializeInto_events (refs : Refs ctx inputWidth) (path : (initializeInto refs).Path) :
    (initializeInto refs).eventTrace path = initializationTrace inputWidth := by
  simp [initializeInto, shiftHalfLoopInto, shiftHalfInto, Circuit.eventTrace,
    initializeResizeOp, initializeClearOp, initializeIncrementOp, shiftHalfOp,
    ClassicalOp.eventTrace, ClassicalOp.event, ClassicalOp.label, initializationTrace,
    List.ofFn_const]

/-- Native multiplicities equal the independent original initialization formula. -/
theorem initializeInto_resourcePool (refs : Refs ctx inputWidth)
    (path : (initializeInto refs).Path) :
    (initializeInto refs).resourcePool path = initializationEventEnvelope inputWidth := by
  change ResourcePool.ofList ((initializeInto refs).eventTrace path) = _
  rw [initializeInto_events]
  simp only [initializationTrace, ResourcePool.ofList_cons, ResourcePool.ofList_replicate,
    initializationEventEnvelope]

/-- Every actual initializer path satisfies its independent native coordinate bound. -/
theorem initializeInto_pool_le (refs : Refs ctx inputWidth) (path : (initializeInto refs).Path) :
    (initializeInto refs).resourcePool path ≤ initializationEventEnvelope inputWidth :=
  le_of_eq (initializeInto_resourcePool refs path)

/-- Four native setup instructions precede the exact fixed number of native shifts. -/
theorem initializeInto_eventCount (refs : Refs ctx inputWidth)
    (path : (initializeInto refs).Path) :
    ((initializeInto refs).eventTrace path).length = 4 + (inputWidth - 1) := by
  rw [initializeInto_events]
  simp only [initializationTrace, List.length_cons, List.length_replicate]
  omega

/-- Actual unit-duration depth includes all four setup writes and every dependent shift. -/
theorem initializeInto_depth (refs : Refs ctx inputWidth) (path : (initializeInto refs).Path) :
    (initializeInto refs).depth (fun _ => 1) path = 4 + (inputWidth - 1) := by
  have shifts : (∑ _ : Fin (inputWidth - 1), (1 : Nat)) = inputWidth - 1 := by simp
  change 1 + (1 + (1 + (1 + (0 + ∑ _ : Fin (inputWidth - 1), (1 : Nat))))) = _
  rw [shifts]
  omega

/-- All visited contexts are the complete original context throughout setup and iteration. -/
theorem initializeInto_visited (refs : Refs ctx inputWidth) (path : (initializeInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (initializeInto refs).visitedContexts path) :
    visited = ctx := by
  have member : visited = ctx ∨ inputWidth - 1 ≠ 0 ∧ visited = ctx := by
    simpa [initializeInto, shiftHalfLoopInto, shiftHalfInto, Circuit.visitedContexts,
      List.ofFn_const] using present
  exact member.elim id And.right

/-- Resident space retains every caller-supplied cell and quantum system. -/
theorem initializeInto_resident_le (refs : Refs ctx inputWidth)
    (path : (initializeInto refs).Path) :
    (initializeInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [initializeInto_visited refs path visited present]

/-- Auxiliary space follows the original workspace roles without hidden fresh cells. -/
theorem initializeInto_auxiliary_le (refs : Refs ctx inputWidth)
    (path : (initializeInto refs).Path) :
    (initializeInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [initializeInto_visited refs path visited present]

/-- Every charged initialization write restores the complete borrowed-reference joint state. -/
theorem initializeInto_borrowedRestored (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (initializeInto refs).BorrowedRestored Reference state
      ((initializeInto refs).execute Reference state) := by
  unfold initializeInto
  refine Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical _ _) ?_
  refine Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _) ?_
  refine Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _) ?_
  refine Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _) ?_
  exact Circuit.borrowedRestored_iterate (shiftHalfInto refs) Reference
    (by intro history _ current; exact Circuit.borrowedRestored_classical _ current)
    (inputWidth - 1) _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
