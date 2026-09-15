/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Correctness
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual integer-square-root round resources and joint borrowed restoration

The independent six-operation formula includes the copy selected by the actual
stored flag. Both possible copies have the same native opcode. All original
resident and auxiliary storage stays live, and the complete borrowed state is
preserved jointly with arbitrary external references.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native operation formula for the original binary-refinement round. -/
def roundTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.addCarry width),
    .classicalOperation (.mulFull width width),
    .classicalOperation (.wordBinary .lessThan (width + width)),
    .classicalOperation (.bit .not),
    .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .shiftRight width)]

/-- Every actual branch path emits exactly the original six native operations. -/
theorem roundInto_events (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto input refs).Path) :
    (roundInto input refs).eventTrace path = roundTrace width := rfl

/-- Native multiplicities come from that same actual path and independent operation formula. -/
theorem roundInto_resourcePool (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto input refs).Path) :
    (roundInto input refs).resourcePool path = ResourcePool.ofList (roundTrace width) :=
  congrArg ResourcePool.ofList (roundInto_events input refs path)

/-- Each actual binary-refinement round performs exactly six native instructions. -/
theorem roundInto_eventCount (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto input refs).Path) :
    ((roundInto input refs).eventTrace path).length = 6 := rfl

/-- The exact native unit-duration depth includes all six original dependent operations. -/
theorem roundInto_depth (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto input refs).Path) :
    (roundInto input refs).depth (fun _ => 1) path = 6 := rfl

/-- The original context stays live through every actual operation, including the selected copy. -/
theorem roundInto_visited (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto input refs).Path) :
    (roundInto input refs).visitedContexts path = [ctx, ctx, ctx, ctx, ctx, ctx] := rfl

/-- All original classical entries and quantum dimensions remain counted throughout the round. -/
theorem roundInto_resident_le (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto input refs).Path) :
    (roundInto input refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  simp only [roundInto_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- All original auxiliary roles remain counted through the complete actual round. -/
theorem roundInto_auxiliary_le (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto input refs).Path) :
    (roundInto input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  simp only [roundInto_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- Every actual prefix, selected copy and shift restores borrowed correlations jointly. -/
theorem roundInto_borrowedRestored (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (roundInto input refs).BorrowedRestored Reference state
      ((roundInto input refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_classical (addOp refs) _
    · apply Circuit.borrowedRestored_seq
      · exact Circuit.borrowedRestored_classical (squareOp refs) _
      · exact Circuit.borrowedRestored_seq _ _ _
          (Circuit.borrowedRestored_classical (compareOp input refs) _)
          (Circuit.borrowedRestored_classical (takeOp refs) _)
  · apply Circuit.borrowedRestored_seq
    · apply Circuit.borrowedRestored_branch
      intro value history _ current
      exact Circuit.borrowedRestored_classical (rootOp refs value.toBool) current
    · exact Circuit.borrowedRestored_classical (halfOp refs) _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt
