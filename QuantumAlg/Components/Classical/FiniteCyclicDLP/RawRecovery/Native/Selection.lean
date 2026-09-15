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
def selectedRecoveryChoice (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then NormalizedRecovery.Native.withRecovery input modulus payload else .id ctx

/-- Actual selected store and path, including the unchanged store on failure. -/
def selectedRecoveryChoiceStep (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (selectedRecoveryChoice input modulus payload value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => NormalizedRecovery.Native.withRecoveryStep input modulus payload store

/-- One actual optional-result pack reads the stored status and computed payload. -/
def selectedRecoveryPackOp (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) :
    ClassicalOp (.product .bit (FiniteCyclicDLP.OutputShape width)) (OutputShape width) ctx ctx :=
  .packOption ctx (.product success (wordRead payload)) output

/-- Original selected suffix: status-controlled recovery, then common optional packing. -/
def selectedRecoveryBody (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) : Circuit ctx ctx :=
  .seq (.branch success (selectedRecoveryChoice input modulus payload))
    (.classical (selectedRecoveryPackOp success payload output))

/-- Actual selection followed by the actual common output write. -/
def selectedRecoveryBodyStep (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx) :
    Store ctx × (selectedRecoveryBody input modulus success payload output).Path :=
  let value := store.read success
  let chosen := selectedRecoveryChoiceStep input modulus payload value store
  (chosen.1.applyOp (selectedRecoveryPackOp success payload output), (⟨value, chosen.2⟩, ()))

/-- The real suffix is placed below its fresh payload allocation. -/
def selectedRecoveryPlaced (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) :
    Circuit (selectionCtx ctx width) (selectionCtx ctx width) :=
  selectedRecoveryBody (underSelection input width) (underSelection modulus width)
    (underSelection success width) (selectionPayloadCell ctx width)
    (writeUnderSelection output width)

/-- Allocate the true payload, run the actual suffix and release exactly that payload. -/
def withSelectedRecovery (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh (selectedRecoveryPlaced input modulus success output)

/-- Complete actual store and branch path through the payload allocation and release. -/
def withSelectedRecoveryStep (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx) :
    Store ctx × (withSelectedRecovery input modulus success output).Path :=
  let result := selectedRecoveryBodyStep (underSelection input width) (underSelection modulus width)
    (underSelection success width) (selectionPayloadCell ctx width)
    (writeUnderSelection output width) (store.pushWorkspace ctx.canonicalFreshKey
      (FiniteCyclicDLP.OutputShape width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
