/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.Reduce.Native

/-!
# Actual negative signed-remainder correction

The original negative arm allocates a widened word, resizes the remainder,
subtracts it from the already loaded modulus, and executes the original
division-and-resize reduction. Both the widened word and the division pair
are genuinely released. No additional modulus loader is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution Modular.Reduce.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original correction has one fresh widened word surrounding the division scope. -/
@[reducible] def correctionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh

/-- Original operand identities are retained below the widened-word scope. -/
def underCorrection {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (correctionCtx ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh

/-- The original writable result remains the same caller cell. -/
def writeUnderCorrection {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (correctionCtx ctx width) shape :=
  output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- Actual extended-remainder scratch cell. -/
def correctionExtendedCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (correctionCtx ctx width) (.unsignedWord (width + 1)) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- Original widening reads the remainder before any original output is written. -/
def correctionResizeOp (remainder : CInputRef ctx (.unsignedWord width))
    (extended : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx remainder extended

/-- Original widened subtraction uses the actual already loaded modulus word. -/
def correctionSubtractOp (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (extended : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
      (.unsignedWord (width + 1)) ctx ctx :=
  .wordBinary .sub (width + 1) ctx (.product modulus (reductionRead extended)) extended

/-- The original two-instruction prefix precedes the second real modular reduction. -/
def correctionBody (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (extended : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (correctionResizeOp remainder extended))
    (.seq (.classical (correctionSubtractOp modulus extended))
      (reduceWord (reductionRead extended) modulus output))

/-- Actual chronological store updates and the true nested division path. -/
def correctionBodyStep (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (extended : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (correctionBody remainder modulus extended output).Path :=
  let subtracted := (store.applyOp (correctionResizeOp remainder extended)).applyOp
    (correctionSubtractOp modulus extended)
  let result := reduceWordStep (reductionRead extended) modulus output subtracted
  (result.1, ((), ((), result.2)))

/-- The real negative arm uses the fresh extended word and original operand/result cells. -/
def correctionPlaced (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (correctionCtx ctx width) (correctionCtx ctx width) :=
  correctionBody (underCorrection remainder width) (underCorrection modulus width)
    (correctionExtendedCell ctx width) (writeUnderCorrection output width)

/-- Allocate the original extended word, run all four native operations, and release it. -/
def withNegativeCorrection (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (correctionPlaced remainder modulus output)

/-- Actual caller-store result and native path after both scratch scopes are released. -/
def withNegativeCorrectionStep (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (withNegativeCorrection remainder modulus output).Path :=
  let result := correctionBodyStep (underCorrection remainder width)
    (underCorrection modulus width) (correctionExtendedCell ctx width)
    (writeUnderCorrection output width) (store.pushWorkspace ctx.canonicalFreshKey
      (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
