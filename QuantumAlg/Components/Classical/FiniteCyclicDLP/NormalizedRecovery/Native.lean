/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.NormalizedRecovery.Model
import all QuantumAlg.Components.Classical.Modular.NativePower.ScopedLaws

/-!
# Actual normalized Fourier recovery and reconstruction

Two native full-product reductions compute the candidate and reconstruct the
negated right frequency. Actual equality and product materialization retain
the candidate and check. Three lexical scratch cells are released afterward.
The inverse is an actual input word; its upstream checked computation is a
separate component. This circuit has no secret-dependent runtime parameter.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native

open Execution Modular.NativePower

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- First actual persistent temporary holds the recovery candidate. -/
@[reducible] def candidateCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Second actual persistent temporary holds the reconstructed frequency. -/
@[reducible] def reconstructionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (candidateCtx ctx width).addWorkspace (candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh

/-- Third actual persistent temporary holds the equality result. -/
@[reducible] def recoveryCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (reconstructionCtx ctx width).addWorkspace (reconstructionCtx ctx width).canonicalFreshKey
    .bit (reconstructionCtx ctx width).canonicalFreshKey_fresh

/-- Every original structural read keeps its actual keys beneath the three scopes. -/
def underRecovery {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (recoveryCtx ctx width) shape :=
  ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (reconstructionCtx ctx width).canonicalFreshKey .bit
          (reconstructionCtx ctx width).canonicalFreshKey_fresh

/-- The final destination is the original caller cell under the three lexical scopes. -/
def writeUnderRecovery {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (recoveryCtx ctx width) shape :=
  ((output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (reconstructionCtx ctx width).canonicalFreshKey .bit
          (reconstructionCtx ctx width).canonicalFreshKey_fresh

/-- Actual candidate head retained across both later allocations. -/
def candidateCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (recoveryCtx ctx width) (.unsignedWord width) :=
  ((CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (reconstructionCtx ctx width).canonicalFreshKey .bit
          (reconstructionCtx ctx width).canonicalFreshKey_fresh

/-- Actual reconstructed-frequency head retained through the flag allocation. -/
def reconstructionCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (recoveryCtx ctx width) (.unsignedWord width) :=
  (CWriteRef.workspaceHead (candidateCtx ctx width) (candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh).underWorkspace
      (reconstructionCtx ctx width).canonicalFreshKey .bit
        (reconstructionCtx ctx width).canonicalFreshKey_fresh

/-- Actual stored equality flag. -/
def verifiedCell (ctx : RuntimeCtx kind) (width : Nat) : CWriteRef (recoveryCtx ctx width) .bit :=
  CWriteRef.workspaceHead (reconstructionCtx ctx width)
    (reconstructionCtx ctx width).canonicalFreshKey .bit
      (reconstructionCtx ctx width).canonicalFreshKey_fresh

/-- Equality reads the reconstructed and original negated-right words. -/
def recoveryEqualOp (right : CInputRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx (.unsignedWord width)) (verified : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product (wordRead reconstruction) right) verified

/-- Actual nominal product materialization retains both computed output components. -/
def recoveryPackOp (candidate : CWriteRef ctx (.unsignedWord width))
    (verified : CWriteRef ctx .bit) (output : CWriteRef ctx (OutputShape width)) :
    ClassicalOp (OutputShape width) (OutputShape width) ctx ctx :=
  .packProduct ctx (.product (wordRead candidate) (wordRead verified)) output

/-- Original native order: recover, reconstruct, compare and materialize the result. -/
def recoveryBody (left right inverse : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (candidate reconstruction : CWriteRef ctx (.unsignedWord width))
    (verified : CWriteRef ctx .bit) (output : CWriteRef ctx (OutputShape width)) :
    Circuit ctx ctx :=
  .seq (scopedMultiply right inverse modulus candidate)
    (.seq (scopedMultiply (wordRead candidate) left modulus reconstruction)
      (.seq (.classical (recoveryEqualOp right reconstruction verified))
        (.classical (recoveryPackOp candidate verified output))))

/-- Store and history path determined by precisely those actual instructions. -/
def recoveryBodyStep (left right inverse : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (candidate reconstruction : CWriteRef ctx (.unsignedWord width))
    (verified : CWriteRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (store : Store ctx) :
    Store ctx × (recoveryBody left right inverse modulus candidate reconstruction verified
      output).Path :=
  let recovered := scopedMultiplyStep right inverse modulus candidate store
  let reconstructed := scopedMultiplyStep (wordRead candidate) left modulus reconstruction
    recovered.1
  let checked := reconstructed.1.applyOp (recoveryEqualOp right reconstruction verified)
  (checked.applyOp (recoveryPackOp candidate verified output),
    (recovered.2, (reconstructed.2, ((), ()))))

/-- Actual lexical placement uses all three original input components without reordering. -/
def recoveryPlaced (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) :
    Circuit (recoveryCtx ctx width) (recoveryCtx ctx width) :=
  recoveryBody (underRecovery (.first input) width)
    (underRecovery (.first (.second input)) width)
    (underRecovery (.second (.second input)) width) (underRecovery modulus width)
    (candidateCell ctx width) (reconstructionCell ctx width) (verifiedCell ctx width)
    (writeUnderRecovery output width)

/-- Complete success component with real allocation and release of all three scratch cells. -/
def withRecovery (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (.workspace (candidateCtx ctx width) (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh
        (.workspace (reconstructionCtx ctx width) (reconstructionCtx ctx width).canonicalFreshKey
          .bit (reconstructionCtx ctx width).canonicalFreshKey_fresh
            (recoveryPlaced input modulus output)))

/-- Push precisely the three actual scratch entries. -/
def enterRecovery (store : Store ctx) (width : Nat) : Store (recoveryCtx ctx width) :=
  ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (candidateCtx ctx width).canonicalFreshKey_fresh).pushWorkspace
        (reconstructionCtx ctx width).canonicalFreshKey .bit
          (reconstructionCtx ctx width).canonicalFreshKey_fresh

/-- Release precisely the same entries in reverse order. -/
def leaveRecovery (store : Store (recoveryCtx ctx width)) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (candidateCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (candidateCtx ctx width).canonicalFreshKey_fresh
        (Store.popWorkspace (reconstructionCtx ctx width).canonicalFreshKey .bit
          (reconstructionCtx ctx width).canonicalFreshKey_fresh store))

/-- The complete actual outer update and native execution path. -/
def withRecoveryStep (input : CInputRef ctx (InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx) :
    Store ctx × (withRecovery input modulus output).Path :=
  let result := recoveryBodyStep (underRecovery (.first input) width)
    (underRecovery (.first (.second input)) width)
    (underRecovery (.second (.second input)) width) (underRecovery modulus width)
    (candidateCell ctx width) (reconstructionCell ctx width) (verifiedCell ctx width)
    (writeUnderRecovery output width) (enterRecovery store width)
  (leaveRecovery result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.NormalizedRecovery.Native
