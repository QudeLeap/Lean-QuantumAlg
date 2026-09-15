/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Native
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Depth
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual resources of normalized recovery

Both three-instruction reductions execute, followed by equality and nominal
product materialization. The two arithmetic scopes reuse their scratch
storage. Peaks count the three persistent temporaries, one active product
and quotient/remainder pair, and every original context entry.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native

open Execution Modular.NativePower

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Eight chronological native operations of the original recovery/check sequence. -/
def recoveryEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.mulFull width width),
    .classicalOperation (.divRem (width + width) (width + 1)),
    .classicalOperation (.wordResize (width + 1) width),
    .classicalOperation (.mulFull width width),
    .classicalOperation (.divRem (width + width) (width + 1)),
    .classicalOperation (.wordResize (width + 1) width),
    .classicalOperation (.wordBinary .equal width),
    .classicalOperation (.nominalEncoding (.packProduct width 1))]

/-- The actual circuit emits exactly both reductions, equality and product materialization. -/
theorem withRecovery_eventTrace (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).eventTrace path = recoveryEvents kind width := rfl

/-- The complete exact native pool is read from the actual chronological event list. -/
theorem withRecovery_resourcePool (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).resourcePool path =
      ResourcePool.ofList (recoveryEvents kind width) := rfl

/-- Both full native multiplications are charged together with the final comparison and pack. -/
theorem withRecovery_pool (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).resourcePool path =
      multiplyEnvelope kind width + multiplyEnvelope kind width +
        ResourcePool.singleton (.classicalOperation (.wordBinary .equal width)) +
          ResourcePool.singleton
            (.classicalOperation (.nominalEncoding (.packProduct width 1))) := by
  rw [withRecovery_resourcePool]
  simp only [recoveryEvents, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
    multiplyEnvelope, add_zero, add_assoc]

/-- Every actual path performs eight charged native operations. -/
theorem withRecovery_eventCount (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    ((withRecovery input modulus output).eventTrace path).length = 8 := rfl

/-- Arbitrary durations retain both modular-product dependencies and the final check and pack. -/
theorem withRecovery_durationDepth (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (duration : Resource.Event kind → Nat)
    (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).depth duration path =
      2 * multiplyDepth width duration +
        duration (.classicalOperation (.wordBinary .equal width)) +
          duration (.classicalOperation (.nominalEncoding (.packProduct width 1))) := by
  change (duration (.classicalOperation (.mulFull width width)) +
    (duration (.classicalOperation (.divRem (width + width) (width + 1))) +
      duration (.classicalOperation (.wordResize (width + 1) width)))) +
    ((duration (.classicalOperation (.mulFull width width)) +
      (duration (.classicalOperation (.divRem (width + width) (width + 1))) +
        duration (.classicalOperation (.wordResize (width + 1) width)))) +
      (duration (.classicalOperation (.wordBinary .equal width)) +
        duration (.classicalOperation (.nominalEncoding (.packProduct width 1))))) = _
  simp only [multiplyDepth]
  omega

/-- Unit-duration dependency depth is exactly eight. -/
theorem withRecovery_depth (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).depth (fun _ => 1) path = 8 := rfl

/-- Complete chronological context visits include both releases of the reused arithmetic scope. -/
theorem withRecovery_visitedContexts (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).visitedContexts path =
      [ctx, candidateCtx ctx width, reconstructionCtx ctx width,
        recoveryCtx ctx width, productCtx (recoveryCtx ctx width) width,
        divisionCtx (recoveryCtx ctx width) width, divisionCtx (recoveryCtx ctx width) width,
        divisionCtx (recoveryCtx ctx width) width, productCtx (recoveryCtx ctx width) width,
        recoveryCtx ctx width, recoveryCtx ctx width, productCtx (recoveryCtx ctx width) width,
        divisionCtx (recoveryCtx ctx width) width, divisionCtx (recoveryCtx ctx width) width,
        divisionCtx (recoveryCtx ctx width) width, productCtx (recoveryCtx ctx width) width,
        recoveryCtx ctx width, recoveryCtx ctx width, recoveryCtx ctx width,
        reconstructionCtx ctx width, candidateCtx ctx width, ctx] := rfl

/-- Actual maximum scratch shapes: three persistent heads plus one active arithmetic scope. -/
def recoveryScratchSpace {kind : ProblemKind} (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (divisionShape width) + SpacePool.ofShape (.unsignedWord (width + width)) +
    SpacePool.ofShape .bit + SpacePool.ofShape (.unsignedWord width) +
      SpacePool.ofShape (.unsignedWord width)

/-- The real scratch shapes total precisely seven word widths and two classical bits. -/
theorem recoveryScratchSpace_eq_bits (kind : ProblemKind) (width : Nat) :
    recoveryScratchSpace (kind := kind) width = SpacePool.ofShape (.bits (7 * width + 2)) := by
  funext axis
  cases axis <;> simp [recoveryScratchSpace, divisionShape, SpacePool.ofShape]
  omega

private theorem recoveryVisits_member {α : Type} (a b c d e f x : α)
    (present : x ∈ [a, b, c, d, e, f, f, f, e, d, d, e, f, f, f, e, d, d, d, c, b, a]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  tauto

private theorem withRecovery_visited (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈ (withRecovery input modulus output).visitedContexts path) :
    visited = ctx ∨ visited = candidateCtx ctx width ∨ visited = reconstructionCtx ctx width ∨
      visited = recoveryCtx ctx width ∨ visited = productCtx (recoveryCtx ctx width) width ∨
        visited = divisionCtx (recoveryCtx ctx width) width := by
  rw [withRecovery_visitedContexts] at present
  exact recoveryVisits_member _ _ _ _ _ _ visited present

private theorem withRecovery_scoped_mem (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    divisionCtx (recoveryCtx ctx width) width ∈
      (withRecovery input modulus output).visitedContexts path := by
  rw [withRecovery_visitedContexts]
  simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

/-- Exact resident peak includes every original entry and all simultaneously live scratch. -/
theorem withRecovery_resident (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).peakResidentSpace path =
      recoveryScratchSpace width + ctx.residentSpace := by
  have upper : (withRecovery input modulus output).peakResidentSpace path ≤
      (divisionCtx (recoveryCtx ctx width) width).residentSpace := by
    apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rcases withRecovery_visited input modulus output path visited present with
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro axis
      cases axis <;> simp [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
        divisionShape, SpacePool.ofShape]
      all_goals omega
  have lower := (withRecovery input modulus output).residentSpace_le_peak_of_visited path
    (divisionCtx (recoveryCtx ctx width) width) (withRecovery_scoped_mem input modulus output path)
  exact (le_antisymm upper lower).trans (by
    simp only [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
      RuntimeCtx.residentSpace_addWorkspace, recoveryScratchSpace, add_assoc])

/-- Exact auxiliary peak includes every original entry and all simultaneously live scratch. -/
theorem withRecovery_auxiliary (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery input modulus output).Path) :
    (withRecovery input modulus output).peakAuxiliarySpace path =
      recoveryScratchSpace width + ctx.auxiliarySpace := by
  have upper : (withRecovery input modulus output).peakAuxiliarySpace path ≤
      (divisionCtx (recoveryCtx ctx width) width).auxiliarySpace := by
    apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rcases withRecovery_visited input modulus output path visited present with
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro axis
      cases axis <;> simp [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
        divisionShape, SpacePool.ofShape]
      all_goals omega
  have lower := (withRecovery input modulus output).auxiliarySpace_le_peak_of_visited path
    (divisionCtx (recoveryCtx ctx width) width) (withRecovery_scoped_mem input modulus output path)
  exact (le_antisymm upper lower).trans (by
    simp only [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
      RuntimeCtx.auxiliarySpace_addWorkspace, recoveryScratchSpace, add_assoc])

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native
