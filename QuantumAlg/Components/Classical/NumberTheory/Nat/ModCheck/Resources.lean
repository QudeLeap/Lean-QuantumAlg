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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {numeratorWidth divisorWidth : Nat}

/-- Independent original native division and remainder-equality coordinate budget. -/
def eventEnvelope (numeratorWidth divisorWidth : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.divRem numeratorWidth divisorWidth))) +
    ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal divisorWidth)))

/-- Chronological two-instruction formula, independent of values, placement and actual paths. -/
def nativeTrace (numeratorWidth divisorWidth : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.divRem numeratorWidth divisorWidth)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal divisorWidth))]

/-- Every actual path emits precisely the original two native instructions. -/
theorem into_events (refs : Refs ctx numeratorWidth divisorWidth) (path : (into (model := model)
  refs).Path) :
    (into (model := model) refs).eventTrace path = nativeTrace (model := model) numeratorWidth
      divisorWidth := by
  change (BitWord.instruction (execution := model) (divideOp refs)).eventTrace path.1 ++
    (BitWord.instruction (execution := model) (checkOp refs)).eventTrace path.2 = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual native multiplicities equal the independent original envelope. -/
theorem into_resourcePool (refs : Refs ctx numeratorWidth divisorWidth)
    (path : (into (model := model) refs).Path) :
    (into (model := model) refs).resourcePool path = eventEnvelope (model := model) numeratorWidth
      divisorWidth := by
  change ResourcePool.ofList ((into (model := model) refs).eventTrace path) = _
  rw [into_events]
  simp only [nativeTrace, ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero,
    eventEnvelope]

/-- Every actual path satisfies its original independent native coordinate budget. -/
theorem into_pool_le (refs : Refs ctx numeratorWidth divisorWidth) (path : (into (model := model)
  refs).Path) :
    (into (model := model) refs).resourcePool path ≤ eventEnvelope (model := model) numeratorWidth
      divisorWidth :=
  le_of_eq (into_resourcePool refs path)

/-- Division and comparison each contribute one actual native event. -/
theorem into_eventCount (refs : Refs ctx numeratorWidth divisorWidth) (path : (into (model :=
  model) refs).Path) :
    ((into (model := model) refs).eventTrace path).length = 2 := by
  rw [into_events]
  rfl

/-- The actual comparison depends on the preceding division, giving unit-duration depth two. -/
theorem into_depth (refs : Refs ctx numeratorWidth divisorWidth) (path : (into (model := model)
  refs).Path) :
    (into (model := model) refs).depth (fun _ => 1) path = 2 := rfl

/-- Both actual instructions retain the complete original runtime context. -/
theorem into_visited (refs : Refs ctx numeratorWidth divisorWidth) (path : (into (model := model)
  refs).Path) :
    (into (model := model) refs).visitedContexts path = [ctx, ctx] := rfl

/-- Every caller-supplied classical cell and quantum dimension remains resident. -/
theorem into_resident_le (refs : Refs ctx numeratorWidth divisorWidth)
    (path : (into (model := model) refs).Path) :
    (into (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  simp only [into_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- The actual instructions preserve the auxiliary accounting of the caller's existing roles. -/
theorem into_auxiliary_le (refs : Refs ctx numeratorWidth divisorWidth)
    (path : (into (model := model) refs).Path) :
    (into (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  simp only [into_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- Both actual native writes restore the full borrowed-reference joint state. -/
theorem into_borrowedRestored (refs : Refs ctx numeratorWidth divisorWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) refs).BorrowedRestored Reference state ((into (model := model)
      refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical
    (BitWord.selectedApplication (execution := model) (divideOp refs)) state)
    (Circuit.borrowedRestored_classical
      (BitWord.selectedApplication (execution := model) (checkOp refs)) _)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck
