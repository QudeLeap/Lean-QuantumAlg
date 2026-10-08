/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Placement
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Exact resources of original first-accepted scratch placement

Both lexical bits are live while the original selector executes. Allocation
adds no native event: every path has the original negation and conjunction,
and exactly its selected paths add the word and latch copies. The complete
caller context remains resident beside two actual auxiliary bits.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Allocation retains the original two decision events and the actual selected two-copy arm. -/
theorem withSelection_eventTrace (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).eventTrace path =
      decisionEvents model ++ (if path.2.1.toBool then copyEvents model width else []) := by
  cases model with
  | classical operations services =>
      have same := BitWord.Selected.operations_eq (execution := .classical operations services)
      change operations = BitWord.model at same
      cases same
      rcases path with ⟨decision, ⟨value, selectedPath⟩⟩
      cases value with
      | bit taken => cases taken <;> rfl
  | quantum gates oracles operations services =>
      have same := BitWord.Selected.operations_eq
        (execution := .quantum gates oracles operations services)
      change operations = BitWord.model at same
      cases same
      rcases path with ⟨decision, ⟨value, selectedPath⟩⟩
      cases value with
      | bit taken => cases taken <;> rfl

/-- The actual path's exact native pool comes from its own selected trace. -/
theorem withSelection_resourcePool (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).resourcePool path =
      ResourcePool.ofList (decisionEvents model ++
        (if path.2.1.toBool then copyEvents model width else [])) := by
  rw [Circuit.resourcePool, withSelection_eventTrace]

/-- The independent original four-operation allowance bounds every actual selected path. -/
theorem withSelection_pool_le (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).resourcePool path ≤ nativeEnvelope
      model width := by
  rw [withSelection_resourcePool, ResourcePool.ofList_append]
  unfold nativeEnvelope
  apply add_le_add le_rfl
  split
  · exact le_rfl
  · exact zero_le

/-- Exactly two or four native instructions execute according to the actual stored branch. -/
theorem withSelection_eventCount (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    ((withSelection (model := model) inputs accepted selected).eventTrace path).length =
      if path.2.1.toBool then 4 else 2 := by
  rw [withSelection_eventTrace]
  cases path.2.1.toBool <;> rfl

/-- Serial duration retains the original decision and selected copy instructions. -/
theorem withSelection_depth (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit
          .and))) +
          (if path.2.1.toBool then
            duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
              (.wordUnary .copy width))) +
              duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit
                .copy))) else 0) := by
  cases model with
  | classical operations services =>
      have same := BitWord.Selected.operations_eq (execution := .classical operations services)
      change operations = BitWord.model at same
      cases same
      rcases path with ⟨decision, ⟨value, selectedPath⟩⟩
      cases value with
      | bit taken => cases taken <;> rfl
  | quantum gates oracles operations services =>
      have same := BitWord.Selected.operations_eq
        (execution := .quantum gates oracles operations services)
      change operations = BitWord.model at same
      cases same
      rcases path with ⟨decision, ⟨value, selectedPath⟩⟩
      cases value with
      | bit taken => cases taken <;> rfl

/-- Every actual dependency duration is the sum over the same executed native trace. -/
theorem withSelection_duration_eventTrace (inputs : Inputs ctx width)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).depth duration path =
      (((withSelection (model := model) inputs accepted selected).eventTrace path).map
        duration).sum := by
  rw [withSelection_depth, withSelection_eventTrace]
  cases path.2.1.toBool <;> simp [decisionEvents, copyEvents, Nat.add_assoc]

/-- The original four native durations bound every actual selected path. -/
theorem withSelection_depth_le (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).depth duration path ≤
      ((decisionEvents model ++ copyEvents model width).map duration).sum := by
  rw [withSelection_depth]
  cases path.2.1.toBool <;> simp [decisionEvents, copyEvents, Nat.add_assoc]

/-- Both real lexical bits remain live through the original selector. -/
def selectionScratchSpace (kind : ProblemKind) : SpacePool kind :=
  SpacePool.ofShape .bit + SpacePool.ofShape .bit

private def availableCtx {kind : ProblemKind} (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

private def takeCtx {kind : ProblemKind} (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  (availableCtx ctx).addWorkspace (availableCtx ctx).canonicalFreshKey .bit
    (availableCtx ctx).canonicalFreshKey_fresh

private theorem withSelection_visitedContexts (inputs : Inputs ctx width)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).visitedContexts path =
      [ctx, availableCtx ctx] ++
        (if path.2.1.toBool then [takeCtx ctx, takeCtx ctx, takeCtx ctx, takeCtx ctx]
          else [takeCtx ctx, takeCtx ctx, takeCtx ctx]) ++ [availableCtx ctx, ctx] := by
  rcases path with ⟨decision, ⟨value, selectedPath⟩⟩
  cases value with
  | bit taken => cases taken <;> rfl

/-- Resident peak includes exactly the original caller context and two lexical bits. -/
theorem withSelection_resident (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).peakResidentSpace path =
      selectionScratchSpace model.kind + ctx.residentSpace := by
  rw [Circuit.peakResidentSpace, withSelection_visitedContexts]
  cases path.2.1.toBool <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals
    apply SpacePool.ext
    intro axis
    cases model <;> cases axis <;> simp (disch := omega) [Circuit.peak, availableCtx, takeCtx,
      selectionScratchSpace, SpacePool.ofShape, SpacePool.max] <;> omega

/-- Auxiliary peak charges those same two bits throughout their actual simultaneous lifetime. -/
theorem withSelection_auxiliary (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (path : (withSelection (model := model) inputs accepted selected).Path) :
    (withSelection (model := model) inputs accepted selected).peakAuxiliarySpace path =
      selectionScratchSpace model.kind + ctx.auxiliarySpace := by
  rw [Circuit.peakAuxiliarySpace, withSelection_visitedContexts]
  cases path.2.1.toBool <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals
    apply SpacePool.ext
    intro axis
    cases model <;> cases axis <;> simp (disch := omega) [Circuit.peak, availableCtx, takeCtx,
      selectionScratchSpace, SpacePool.ofShape, SpacePool.max] <;> omega

/-- Scratch costs exactly two classical bits even for a zero-width candidate word. -/
theorem selectionScratchSpace_classicalBits (kind : ProblemKind) :
    selectionScratchSpace kind .classicalBits = 2 := rfl

end

end QuantumAlg.ClassicalRoutines.FirstAccepted
