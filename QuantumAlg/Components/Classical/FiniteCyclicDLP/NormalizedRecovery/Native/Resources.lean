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

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Eight chronological native operations of the original recovery/check sequence. -/
def recoveryEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.mulFull width width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.divRem (width +
      width) (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize (width +
      1) width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.mulFull width width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.divRem (width +
      width) (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize (width +
      1) width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal
      width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.nominalEncoding
      (.packProduct width 1)))]

private lemma scopedMultiply_events
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scopedMultiply (model := model) left right modulus output).Path) :
    (scopedMultiply (model := model) left right modulus output).eventTrace path =
      multiplyEvents model width :=
  nativePowerMultiply_eventTrace (underMultiply left width) (underMultiply right width)
    (underMultiply modulus width) (productCell ctx width) (divisionCell ctx width)
    (writeUnderMultiply output width) path

private lemma recoveryBody_events (left right inverse : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (candidate reconstruction : CWriteRef ctx (.unsignedWord width))
    (verified : CWriteRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (path : (recoveryBody (model := model) left right inverse modulus candidate reconstruction
      verified output).Path) :
    (recoveryBody (model := model) left right inverse modulus candidate reconstruction
      verified output).eventTrace path = recoveryEvents model width := by
  rcases path with ⟨first, second, third, fourth⟩
  change (scopedMultiply (model := model) right inverse modulus candidate).eventTrace first ++
    ((scopedMultiply (model := model) (wordRead candidate) left modulus reconstruction).eventTrace
      second ++
      ((BitWord.instruction (execution := model)
        (recoveryEqualOp right reconstruction verified)).eventTrace third ++
        (BitWord.instruction (execution := model)
          (recoveryPackOp candidate verified output)).eventTrace fourth)) = _
  rw [scopedMultiply_events, scopedMultiply_events, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The actual circuit emits exactly both reductions, equality and product materialization. -/
lemma withRecovery_eventTrace (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    (withRecovery (model := model) input modulus output).eventTrace path = recoveryEvents model
      width := by
  exact recoveryBody_events (underRecovery (.first input) width)
    (underRecovery (.first (.second input)) width)
    (underRecovery (.second (.second input)) width) (underRecovery modulus width)
    (candidateCell ctx width) (reconstructionCell ctx width) (verifiedCell ctx width)
    (writeUnderRecovery output width) path

/-- The complete exact native pool is read from the actual chronological event list. -/
lemma withRecovery_resourcePool (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    (withRecovery (model := model) input modulus output).resourcePool path =
      ResourcePool.ofList (recoveryEvents model width) :=
  congrArg ResourcePool.ofList (withRecovery_eventTrace input modulus output path)

/-- Both full native multiplications are charged together with the final comparison and pack. -/
lemma withRecovery_pool (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    (withRecovery (model := model) input modulus output).resourcePool path =
      multiplyEnvelope model width + multiplyEnvelope model width +
        ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution :=
          model) (.wordBinary .equal width))) +
          ResourcePool.singleton
            (.classicalOperation (BitWord.selectedCoordinate (execution := model)
              (.nominalEncoding (.packProduct width 1)))) := by
  rw [withRecovery_resourcePool]
  simp only [recoveryEvents, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
    multiplyEnvelope, add_zero, add_assoc]

/-- Every actual path performs eight charged native operations. -/
lemma withRecovery_eventCount (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    ((withRecovery (model := model) input modulus output).eventTrace path).length = 8 := by
  rw [withRecovery_eventTrace]
  rfl

/-- Arbitrary durations retain both modular-product dependencies and the final check and pack. -/
lemma withRecovery_durationDepth (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (duration : Resource.Event model → Nat)
    (path : (withRecovery (model := model) input modulus output).Path) :
    (withRecovery (model := model) input modulus output).depth duration path =
      2 * multiplyDepth width duration +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .equal width))) +
          duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.nominalEncoding (.packProduct width 1)))) := by
  rcases path with ⟨first, second, third, fourth⟩
  change (recoveryBody (model := model) (underRecovery (.first input) width)
    (underRecovery (.first (.second input)) width)
    (underRecovery (.second (.second input)) width) (underRecovery modulus width)
    (candidateCell ctx width) (reconstructionCell ctx width) (verifiedCell ctx width)
    (writeUnderRecovery output width)).depth duration (first, second, third, fourth) = _
  simp only [recoveryBody, Circuit.depth_seq, nativePower_scopedMultiply_depth,
    BitWord.bitWord_instruction_depth]
  change multiplyDepth width duration + (multiplyDepth width duration +
    (duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width))) +
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.nominalEncoding (.packProduct width 1)))))) = _
  omega

/-- Unit-duration dependency depth is exactly eight. -/
lemma withRecovery_depth (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    (withRecovery (model := model) input modulus output).depth (fun _ => 1) path = 8 := rfl

/-- Complete chronological context visits include both releases of the reused arithmetic scope. -/
lemma withRecovery_visitedContexts (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    (withRecovery (model := model) input modulus output).visitedContexts path =
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
lemma recoveryScratchSpace_eq_bits (kind : ProblemKind) (width : Nat) :
    recoveryScratchSpace (kind := kind) width = SpacePool.ofShape (.bits (7 * width + 2)) := by
  funext axis
  cases axis <;> simp [recoveryScratchSpace, divisionShape, SpacePool.ofShape]
  omega

private lemma recoveryVisits_member {α : Type} (a b c d e f x : α)
    (present : x ∈ [a, b, c, d, e, f, f, f, e, d, d, e, f, f, f, e, d, d, d, c, b, a]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  tauto

private lemma withRecovery_visited (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (withRecovery (model := model) input modulus output).visitedContexts
      path) :
    visited = ctx ∨ visited = candidateCtx ctx width ∨ visited = reconstructionCtx ctx width ∨
      visited = recoveryCtx ctx width ∨ visited = productCtx (recoveryCtx ctx width) width ∨
        visited = divisionCtx (recoveryCtx ctx width) width := by
  rw [withRecovery_visitedContexts] at present
  exact recoveryVisits_member _ _ _ _ _ _ visited present

private lemma withRecovery_scoped_mem (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    divisionCtx (recoveryCtx ctx width) width ∈
      (withRecovery (model := model) input modulus output).visitedContexts path := by
  rw [withRecovery_visitedContexts]
  simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

/-- Exact resident peak includes every original entry and all simultaneously live scratch. -/
lemma withRecovery_resident (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    (withRecovery (model := model) input modulus output).peakResidentSpace path =
      recoveryScratchSpace width + ctx.residentSpace := by
  have upper : (withRecovery (model := model) input modulus output).peakResidentSpace path ≤
      (divisionCtx (recoveryCtx ctx width) width).residentSpace := by
    apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rcases withRecovery_visited input modulus output path visited present with
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro axis
      simp only [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
        RuntimeCtx.residentSpace_addWorkspace,
        Pi.add_apply]
      omega
  have lower := (withRecovery (model := model) input modulus
    output).residentSpace_le_peak_of_visited path
    (divisionCtx (recoveryCtx ctx width) width) (withRecovery_scoped_mem input modulus output path)
  exact (le_antisymm upper lower).trans (by
    simp only [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
      RuntimeCtx.residentSpace_addWorkspace, recoveryScratchSpace, add_assoc])

/-- Exact auxiliary peak includes every original entry and all simultaneously live scratch. -/
lemma withRecovery_auxiliary (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (path : (withRecovery (model := model) input
      modulus output).Path) :
    (withRecovery (model := model) input modulus output).peakAuxiliarySpace path =
      recoveryScratchSpace width + ctx.auxiliarySpace := by
  have upper : (withRecovery (model := model) input modulus output).peakAuxiliarySpace path ≤
      (divisionCtx (recoveryCtx ctx width) width).auxiliarySpace := by
    apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rcases withRecovery_visited input modulus output path visited present with
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro axis
      simp only [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
        RuntimeCtx.auxiliarySpace_addWorkspace,
        Pi.add_apply]
      omega
  have lower := (withRecovery (model := model) input modulus
    output).auxiliarySpace_le_peak_of_visited path
    (divisionCtx (recoveryCtx ctx width) width) (withRecovery_scoped_mem input modulus output path)
  exact (le_antisymm upper lower).trans (by
    simp only [candidateCtx, reconstructionCtx, recoveryCtx, productCtx, divisionCtx,
      RuntimeCtx.auxiliarySpace_addWorkspace, recoveryScratchSpace, add_assoc])

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native
