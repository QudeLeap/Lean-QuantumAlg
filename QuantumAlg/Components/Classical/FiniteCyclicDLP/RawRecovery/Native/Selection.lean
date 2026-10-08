/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Native
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model

/-!
# Actual inverse-status selection and optional recovery result

The original stored success bit selects normalized recovery or identity.
Both paths then execute the same nominal optional-result pack. Its payload
is an actual fresh lexical cell and is released after packing. This suffix
consumes the upstream inverse/status cells; it does not compute their values.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution Modular.NativePower

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The optional-result payload is one genuine fresh lexical cell. -/
@[reducible] def selectionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh

/-- Existing reads keep their exact stored identities below the payload scope. -/
def underSelection {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (selectionCtx ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh

/-- The original optional-result destination remains the same caller cell. -/
def writeUnderSelection {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (selectionCtx ctx width) shape :=
  output.underWorkspace ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh

/-- Actual lexical payload destination. -/
def selectionPayloadCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (selectionCtx ctx width) (FiniteCyclicDLP.OutputShape width) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh

/-- The actual stored status selects the original recovery component or identity. -/
def selectedRecoveryChoice {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (value : CShape.Value .bit) : Circuit model ctx ctx :=
  if value.toBool then NormalizedRecovery.Native.withRecovery (model := model) input modulus
      payload else .id ctx

/-- Actual selected store and path, including the unchanged store on failure. -/
def selectedRecoveryChoiceStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (selectedRecoveryChoice (model := model) input modulus payload value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => NormalizedRecovery.Native.withRecoveryStep (model := model) input modulus
      payload store

/-- One actual optional-result pack reads the stored status and computed payload. -/
def selectedRecoveryPackOp (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) :
    ClassicalOp (.product .bit (FiniteCyclicDLP.OutputShape width)) (OutputShape width) ctx ctx :=
  .packOption ctx (.product success (wordRead payload)) output

/-- Original selected suffix: status-controlled recovery, then common optional packing. -/
def selectedRecoveryBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) : Circuit model ctx ctx :=
  .seq (.branch success (selectedRecoveryChoice (model := model) input modulus payload))
    (BitWord.instruction (execution := model) (selectedRecoveryPackOp success payload output))

/-- Actual selection followed by the actual common output write. -/
def selectedRecoveryBodyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx) :
    Store ctx × (selectedRecoveryBody (model := model) input modulus success payload output).Path :=
  let value := store.read success
  let chosen := selectedRecoveryChoiceStep (model := model) input modulus payload value store
  let packed := BitWord.instructionStep (execution := model)
    (selectedRecoveryPackOp success payload output) chosen.1
  (packed.1, (⟨value, chosen.2⟩, packed.2))

/-- The real suffix is placed below its fresh payload allocation. -/
def selectedRecoveryPlaced {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) :
    Circuit model (selectionCtx ctx width) (selectionCtx ctx width) :=
  selectedRecoveryBody (model := model) (underSelection input width) (underSelection modulus width)
    (underSelection success width) (selectionPayloadCell ctx width)
    (writeUnderSelection output width)

/-- Allocate the true payload, run the actual suffix and release exactly that payload. -/
def withSelectedRecovery {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh (selectedRecoveryPlaced (model := model) input modulus success
        output)

/-- Complete actual store and branch path through the payload allocation and release. -/
def withSelectedRecoveryStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx) :
    Store ctx × (withSelectedRecovery (model := model) input modulus success output).Path :=
  let result := selectedRecoveryBodyStep (model := model) (underSelection input width)
      (underSelection modulus width)
    (underSelection success width) (selectionPayloadCell ctx width)
    (writeUnderSelection output width) (store.pushWorkspace ctx.canonicalFreshKey
      (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
