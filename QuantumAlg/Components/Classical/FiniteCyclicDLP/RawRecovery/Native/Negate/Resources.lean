/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Negate.Semantics
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual modular-negation branch resources

Each actual path emits the equality test and exactly its selected native
copy or subtraction. The exact peak is attained while the original context,
one zero word and one flag are all live. Both scratch cells are absent after
the actual matching releases.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual zero-test and selected branch instruction coordinates. -/
def negateEvents (kind : ProblemKind) (width : Nat) (zero : Bool) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .equal width),
    if zero then .classicalOperation (.wordUnary .copy width)
      else .classicalOperation (.wordBinary .sub width)]

/-- The complete actual path emits precisely its two selected native instructions. -/
theorem withNegate_eventTrace (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    (withNegate modulus right output).eventTrace path =
      negateEvents kind width path.2.1.toBool := by
  rcases path with ⟨testPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- Actual native multiplicities retain the selected copy-versus-subtraction distinction. -/
theorem withNegate_resourcePool (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    (withNegate modulus right output).resourcePool path =
      ResourcePool.ofList (negateEvents kind width path.2.1.toBool) :=
  congrArg ResourcePool.ofList (withNegate_eventTrace modulus right output path)

/-- Every actual path contains one test and exactly one selected arithmetic instruction. -/
theorem withNegate_eventCount (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    ((withNegate modulus right output).eventTrace path).length = 2 := by
  rw [withNegate_eventTrace]
  rfl

/-- Arbitrary event durations retain the actual dependency from test to selected arithmetic. -/
theorem withNegate_durationDepth (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (withNegate modulus right output).Path) :
    (withNegate modulus right output).depth duration path =
      duration (.classicalOperation (.wordBinary .equal width)) +
        if path.2.1.toBool then duration (.classicalOperation (.wordUnary .copy width))
          else duration (.classicalOperation (.wordBinary .sub width)) := by
  rcases path with ⟨testPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- Unit-duration serial depth is exactly two on either actual branch. -/
theorem withNegate_depth (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    (withNegate modulus right output).depth (fun _ => 1) path = 2 := by
  rw [withNegate_durationDepth]
  simp only [ite_self]

/-- The exact chronological contexts include both live scratch cells before their releases. -/
theorem withNegate_visitedContexts (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    (withNegate modulus right output).visitedContexts path =
      [ctx, negateZeroCtx ctx width, negateCtx ctx width, negateCtx ctx width,
        negateZeroCtx ctx width, ctx] := by
  rcases path with ⟨testPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- Actual zero-word and equality-flag scratch storage. -/
def negateScratchSpace {kind : ProblemKind} (width : Nat) : SpacePool kind :=
  SpacePool.ofShape .bit + SpacePool.ofShape (.unsignedWord width)

private theorem withNegate_visited (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈ (withNegate modulus right output).visitedContexts path) :
    visited = ctx ∨ visited = negateZeroCtx ctx width ∨ visited = negateCtx ctx width := by
  rw [withNegate_visitedContexts] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  tauto

private theorem withNegate_scoped_mem (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    negateCtx ctx width ∈ (withNegate modulus right output).visitedContexts path := by
  rw [withNegate_visitedContexts]
  simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

/-- The exact resident peak counts every original live entry and both actual scratch cells. -/
theorem withNegate_resident (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    (withNegate modulus right output).peakResidentSpace path =
      negateScratchSpace width + ctx.residentSpace := by
  have upper : (withNegate modulus right output).peakResidentSpace path ≤
      (negateCtx ctx width).residentSpace := by
    apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rcases withNegate_visited modulus right output path visited present with same | same | same
    · subst visited
      intro axis
      change ctx.residentSpace axis ≤ SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis)
      omega
    · subst visited
      intro axis
      change _ ≤ SpacePool.ofShape .bit axis + (negateZeroCtx ctx width).residentSpace axis
      omega
    · exact same ▸ le_rfl
  have lower := (withNegate modulus right output).residentSpace_le_peak_of_visited path
    (negateCtx ctx width) (withNegate_scoped_mem modulus right output path)
  exact (le_antisymm upper lower).trans (by
    simp only [negateCtx, negateZeroCtx, RuntimeCtx.residentSpace_addWorkspace,
      negateScratchSpace, add_assoc])

/-- The exact auxiliary peak counts the same scratch cells beside all original auxiliary roles. -/
theorem withNegate_auxiliary (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (withNegate modulus right output).Path) :
    (withNegate modulus right output).peakAuxiliarySpace path =
      negateScratchSpace width + ctx.auxiliarySpace := by
  have upper : (withNegate modulus right output).peakAuxiliarySpace path ≤
      (negateCtx ctx width).auxiliarySpace := by
    apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rcases withNegate_visited modulus right output path visited present with same | same | same
    · subst visited
      intro axis
      change ctx.auxiliarySpace axis ≤ SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis)
      omega
    · subst visited
      intro axis
      change _ ≤ SpacePool.ofShape .bit axis + (negateZeroCtx ctx width).auxiliarySpace axis
      omega
    · exact same ▸ le_rfl
  have lower := (withNegate modulus right output).auxiliarySpace_le_peak_of_visited path
    (negateCtx ctx width) (withNegate_scoped_mem modulus right output path)
  exact (le_antisymm upper lower).trans (by
    simp only [negateCtx, negateZeroCtx, RuntimeCtx.auxiliarySpace_addWorkspace,
      negateScratchSpace, add_assoc])

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
