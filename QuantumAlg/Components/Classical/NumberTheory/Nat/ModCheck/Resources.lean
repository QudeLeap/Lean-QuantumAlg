/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Program
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Original native resources and full borrowed restoration of the actual remainder check
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {numeratorWidth divisorWidth : Nat}

/-- Independent original native division and remainder-equality coordinate budget. -/
def eventEnvelope (numeratorWidth divisorWidth : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.divRem numeratorWidth divisorWidth)) +
    ResourcePool.singleton (.classicalOperation (.wordBinary .equal divisorWidth))

/-- Chronological two-instruction formula, independent of values, placement and actual paths. -/
def nativeTrace (numeratorWidth divisorWidth : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.divRem numeratorWidth divisorWidth),
    .classicalOperation (.wordBinary .equal divisorWidth)]

/-- Every actual path emits precisely the original two native instructions. -/
theorem into_events (refs : Refs ctx numeratorWidth divisorWidth) (path : (into refs).Path) :
    (into refs).eventTrace path = nativeTrace numeratorWidth divisorWidth := rfl

/-- Actual native multiplicities equal the independent original envelope. -/
theorem into_resourcePool (refs : Refs ctx numeratorWidth divisorWidth)
    (path : (into refs).Path) :
    (into refs).resourcePool path = eventEnvelope numeratorWidth divisorWidth := by
  change ResourcePool.ofList ((into refs).eventTrace path) = _
  rw [into_events]
  simp only [nativeTrace, ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero,
    eventEnvelope]

/-- Every actual path satisfies its original independent native coordinate budget. -/
theorem into_pool_le (refs : Refs ctx numeratorWidth divisorWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope numeratorWidth divisorWidth :=
  le_of_eq (into_resourcePool refs path)

/-- Division and comparison each contribute one actual native event. -/
theorem into_eventCount (refs : Refs ctx numeratorWidth divisorWidth) (path : (into refs).Path) :
    ((into refs).eventTrace path).length = 2 := rfl

/-- The actual comparison depends on the preceding division, giving unit-duration depth two. -/
theorem into_depth (refs : Refs ctx numeratorWidth divisorWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path = 2 := rfl

/-- Both actual instructions retain the complete original runtime context. -/
theorem into_visited (refs : Refs ctx numeratorWidth divisorWidth) (path : (into refs).Path) :
    (into refs).visitedContexts path = [ctx, ctx] := rfl

/-- Every caller-supplied classical cell and quantum dimension remains resident. -/
theorem into_resident_le (refs : Refs ctx numeratorWidth divisorWidth)
    (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  simp only [into_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- The actual instructions preserve the auxiliary accounting of the caller's existing roles. -/
theorem into_auxiliary_le (refs : Refs ctx numeratorWidth divisorWidth)
    (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  simp only [into_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- Both actual native writes restore the full borrowed-reference joint state. -/
theorem into_borrowedRestored (refs : Refs ctx numeratorWidth divisorWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical (divideOp refs) state)
    (Circuit.borrowedRestored_classical (checkOp refs) _)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck
