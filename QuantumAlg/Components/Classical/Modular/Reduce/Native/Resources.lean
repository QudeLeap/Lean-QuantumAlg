/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.Reduce.Native
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Exact native remainder-reduction resources

The original division and remainder resize are both charged. The single
actual quotient/remainder pair contributes its full shape beside every
original context entry and is released before returning to the caller.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.Reduce.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- Original two native events with their actual operand widths. -/
def reductionEvents (kind : ProblemKind) (sourceWidth width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.divRem sourceWidth (width + 1)),
    .classicalOperation (.wordResize (width + 1) width)]

/-- Every actual path emits exactly the original division and remainder resize. -/
theorem reduceWord_eventTrace (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord numerator modulus output).Path) :
    (reduceWord numerator modulus output).eventTrace path =
      reductionEvents kind sourceWidth width :=
  rfl

/-- The native pool is obtained from the actual two-operation path. -/
theorem reduceWord_resourcePool (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord numerator modulus output).Path) :
    (reduceWord numerator modulus output).resourcePool path =
      ResourcePool.ofList (reductionEvents kind sourceWidth width) := rfl

/-- Exactly two native operations are charged, with no hidden modulus loading. -/
theorem reduceWord_eventCount (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord numerator modulus output).Path) :
    ((reduceWord numerator modulus output).eventTrace path).length = 2 := rfl

/-- Arbitrary native durations retain the original division-to-remainder dependency. -/
theorem reduceWord_durationDepth (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (reduceWord numerator modulus output).Path) :
    (reduceWord numerator modulus output).depth duration path =
      duration (.classicalOperation (.divRem sourceWidth (width + 1))) +
        duration (.classicalOperation (.wordResize (width + 1) width)) := rfl

/-- Unit-duration depth equals the two original serial instructions. -/
theorem reduceWord_depth (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord numerator modulus output).Path) :
    (reduceWord numerator modulus output).depth (fun _ => 1) path = 2 := rfl

/-- Exact resident peak counts the real full division pair and every original context entry. -/
theorem reduceWord_resident (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord numerator modulus output).Path) :
    (reduceWord numerator modulus output).peakResidentSpace path =
      SpacePool.ofShape (divisionShape sourceWidth width) + ctx.residentSpace := by
  have bodyPeak : (reductionPlaced numerator modulus output).peakResidentSpace path =
      (reductionCtx ctx sourceWidth width).residentSpace := by
    change SpacePool.max (reductionCtx ctx sourceWidth width).residentSpace
      (SpacePool.max (reductionCtx ctx sourceWidth width).residentSpace 0) = _
    simp only [SpacePool.max_zero, SpacePool.max_self]
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (divisionShape sourceWidth width) ctx.canonicalFreshKey_fresh
    (reductionPlaced numerator modulus output) path).trans
      ((congrArg (SpacePool.max ctx.residentSpace) bodyPeak).trans ?_)
  exact SpacePool.max_eq_right le_add_self

/-- Exact auxiliary peak counts the real full division pair and every original context entry. -/
theorem reduceWord_auxiliary (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (reduceWord numerator modulus output).Path) :
    (reduceWord numerator modulus output).peakAuxiliarySpace path =
      SpacePool.ofShape (divisionShape sourceWidth width) + ctx.auxiliarySpace := by
  have bodyPeak : (reductionPlaced numerator modulus output).peakAuxiliarySpace path =
      (reductionCtx ctx sourceWidth width).auxiliarySpace := by
    change SpacePool.max (reductionCtx ctx sourceWidth width).auxiliarySpace
      (SpacePool.max (reductionCtx ctx sourceWidth width).auxiliarySpace 0) = _
    simp only [SpacePool.max_zero, SpacePool.max_self]
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (divisionShape sourceWidth width) ctx.canonicalFreshKey_fresh
    (reductionPlaced numerator modulus output) path).trans
      ((congrArg (SpacePool.max ctx.auxiliarySpace) bodyPeak).trans ?_)
  exact SpacePool.max_eq_right le_add_self

end QuantumAlg.ClassicalRoutines.Modular.Reduce.Native
