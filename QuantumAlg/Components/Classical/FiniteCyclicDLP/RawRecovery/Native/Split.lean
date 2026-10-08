/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
import all QuantumAlg.Components.Classical.Word.Split.Correctness
import all QuantumAlg.Components.Classical.Word.Split.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Lexical placement of the original raw Fourier word split

The existing combined-width decoded word is split by the canonical actual
low resize, exactly the low width's right shifts, and high resize. Both result
words are fresh lexical cells. Their real consumer executes before either
cell is released, and no reference to a released result escapes its context.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

section Placement

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- First actual lexical output contains the most significant raw register. -/
@[reducible] def splitLeftCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Second actual lexical output contains the least significant raw register. -/
@[reducible] def splitCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (splitLeftCtx ctx width).addWorkspace (splitLeftCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (splitLeftCtx ctx width).canonicalFreshKey_fresh

/-- Existing structural reads keep their exact identities under both result scopes. -/
def underSplit {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (splitCtx ctx width) shape :=
  (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (splitLeftCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (splitLeftCtx ctx width).canonicalFreshKey_fresh

/-- The destructive working word remains the actual original decoded cell. -/
def writeUnderSplit {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (splitCtx ctx width) shape :=
  (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (splitLeftCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (splitLeftCtx ctx width).canonicalFreshKey_fresh

/-- Real first result head, lifted past the subsequent low-result allocation. -/
def splitLeftCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (splitCtx ctx width) (.unsignedWord width) :=
  (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (splitLeftCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (splitLeftCtx ctx width).canonicalFreshKey_fresh

/-- Real final result head for the low raw register. -/
def splitRightCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (splitCtx ctx width) (.unsignedWord width) :=
  CWriteRef.workspaceHead (splitLeftCtx ctx width) (splitLeftCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (splitLeftCtx ctx width).canonicalFreshKey_fresh

/-- The canonical word splitter uses these exact three physical storage identities. -/
def splitRefs (decoded : CWriteRef ctx (.unsignedWord (width + width))) :
    Word.Split.Refs (splitCtx ctx width) width width :=
  ⟨writeUnderSplit decoded width, splitLeftCell ctx width, splitRightCell ctx width⟩

private theorem existing_write_ne_fresh {shape : CShape} (output : CWriteRef ctx shape) :
    output.key ≠ ctx.canonicalFreshKey := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  rw [← same]
  exact List.mem_map_of_mem output.toCStorageRef.present

/-- Actual lexical allocation proves every separation condition internally. -/
theorem splitRefs_separation (decoded : CWriteRef ctx (.unsignedWord (width + width))) :
    Word.Split.Separation (splitRefs decoded) := by
  constructor
  · exact existing_write_ne_fresh (decoded.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  · exact existing_write_ne_fresh decoded
  · exact existing_write_ne_fresh (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh)

/-- Enter precisely the two scopes used by the actual enclosing circuit. -/
def enterSplit (store : Store ctx) (width : Nat) : Store (splitCtx ctx width) :=
  (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace (splitLeftCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (splitLeftCtx ctx width).canonicalFreshKey_fresh

/-- Both scope entries preserve the actual original combined-width decoded value. -/
theorem enterSplit_read (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (enterSplit store width).read (underSplit input width) = store.read input :=
  (Store.read_pushWorkspace_underWorkspace
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
    (splitLeftCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (splitLeftCtx ctx width).canonicalFreshKey_fresh
    (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh)).trans
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh input)

end Placement

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original native split is placed on the original word and both fresh results. -/
def splitPlaced (decoded : CWriteRef ctx (.unsignedWord (width + width))) :
    Circuit model (splitCtx ctx width) (splitCtx ctx width) :=
  Word.Split.splitInto (model := model) (splitRefs decoded)

/-- Actual store and finite instruction path of that same placed split. -/
def splitPlacedStep (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (store : Store (splitCtx ctx width)) :
    Store (splitCtx ctx width) × (splitPlaced (model := model) decoded).Path :=
  Word.Split.splitStep (model := model) (splitRefs decoded) store

/-- Results stay live throughout their real consumer and are then released in reverse order. -/
def withSplit (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (consumer : Circuit model (splitCtx ctx width) (splitCtx ctx width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (.workspace (splitLeftCtx ctx width) (splitLeftCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (splitLeftCtx ctx width).canonicalFreshKey_fresh
      (.seq (splitPlaced (model := model) decoded) consumer))

/-- Exact execution retains the shared service, complete reference blocks and actual path. -/
theorem splitPlaced_execute (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (splitCtx ctx width) Reference (model.HiddenState × History)) :
    (splitPlaced (model := model) decoded).execute Reference state =
      state.mapClassical (fun entry =>
        let result := splitPlacedStep (model := model) decoded entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  (Word.Split.splitInto_execute (model := model) (splitRefs decoded) Reference state).trans
    (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The actual two result words are the original quotient and remainder for any inner store. -/
theorem splitPlaced_values (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (store : Store (splitCtx ctx width)) :
    ((splitPlacedStep (model := model) decoded store).1.read
      (.storage (splitLeftCell ctx width).toCStorageRef)).toNat =
        (store.read (underSplit (.storage decoded.toCStorageRef) width)).toNat / 2 ^ width ∧
      ((splitPlacedStep (model := model) decoded store).1.read
        (.storage (splitRightCell ctx width).toCStorageRef)).toNat =
        (store.read (underSplit (.storage decoded.toCStorageRef) width)).toNat % 2 ^ width :=
  ⟨Word.Split.splitInto_high (model := model) (splitRefs decoded)
      (splitRefs_separation decoded) store,
    Word.Split.splitInto_low (model := model) (splitRefs decoded)
      (splitRefs_separation decoded) store⟩

/-- The original decoded-terminal representation gives exactly the original two raw frequencies. -/
theorem splitPlaced_original_values (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (store : Store ctx) (input : CShape.Value (RawRecovery.InputShape width))
    (represents : (store.read (.storage decoded.toCStorageRef)).toNat = decodedTerminal input) :
    ((splitPlacedStep (model := model) decoded (enterSplit store width)).1.read
      (.storage (splitLeftCell ctx width).toCStorageRef)).toNat = leftRaw input ∧
      ((splitPlacedStep (model := model) decoded (enterSplit store width)).1.read
        (.storage (splitRightCell ctx width).toCStorageRef)).toNat = rightRaw input := by
  have values := splitPlaced_values (model := model) decoded (enterSplit store width)
  have original := (congrArg CShape.Value.toNat
    (enterSplit_read store (.storage decoded.toCStorageRef) width)).trans represents
  exact ⟨values.1.trans (congrArg (fun value => value / 2 ^ width) original),
    values.2.trans (congrArg (fun value => value % 2 ^ width) original)⟩

/-- The enclosing lexical split emits exactly the original split operations before its consumer. -/
theorem withSplit_eventTrace (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (consumer : Circuit model (splitCtx ctx width) (splitCtx ctx width))
    (path : (withSplit (model := model) decoded consumer).Path) :
    (withSplit (model := model) decoded consumer).eventTrace path =
      Word.Split.splitTrace (model := model) width width ++ consumer.eventTrace path.2 :=
  congrArg (fun trace => trace ++ consumer.eventTrace path.2)
    (Word.Split.splitInto_events (model := model) (splitRefs decoded) path.1)

/-- Native multiplicities come from the original split instructions and the real consumer. -/
theorem withSplit_resourcePool (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (consumer : Circuit model (splitCtx ctx width) (splitCtx ctx width))
    (path : (withSplit (model := model) decoded consumer).Path) :
    (withSplit (model := model) decoded consumer).resourcePool path =
      ResourcePool.ofList (Word.Split.splitTrace (model := model) width width) +
        consumer.resourcePool path.2 :=
  (congrArg ResourcePool.ofList (withSplit_eventTrace decoded consumer path)).trans
    (ResourcePool.ofList_append _ _)

/-- The original two resizes and right shifts precede every dependent consumer instruction. -/
theorem withSplit_depth (decoded : CWriteRef ctx (.unsignedWord (width + width)))
    (consumer : Circuit model (splitCtx ctx width) (splitCtx ctx width))
    (path : (withSplit (model := model) decoded consumer).Path) :
    (withSplit (model := model) decoded consumer).depth (fun _ => 1) path =
      width + 2 + consumer.depth (fun _ => 1) path.2 :=
  congrArg (fun depth => depth + consumer.depth (fun _ => 1) path.2)
    (Word.Split.splitInto_depth (model := model) (splitRefs decoded) path.1)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
