/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual native unsigned modular reduction

The original full quotient/remainder operation precedes remainder resizing.
One genuine lexical pair stores both division outputs and is then released.
The modulus is an actual existing widened word; its loading belongs to the
caller and is neither hidden nor repeated by this reduction component.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.Reduce.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- The original division pair retains its full quotient and widened remainder. -/
def divisionShape (sourceWidth width : Nat) : CShape :=
  .product (.unsignedWord sourceWidth) (.unsignedWord (width + 1))

/-- One actual division-result lexical allocation. -/
@[reducible] def reductionCtx (ctx : RuntimeCtx kind) (sourceWidth width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (divisionShape sourceWidth width)
    ctx.canonicalFreshKey_fresh

/-- Structural read of an actual writable cell. -/
def reductionRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- Original input identities remain live below the division pair. -/
def underReduction {shape : CShape} (input : CInputRef ctx shape) (sourceWidth width : Nat) :
    CInputRef (reductionCtx ctx sourceWidth width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (divisionShape sourceWidth width)
    ctx.canonicalFreshKey_fresh

/-- The original result cell remains the real destination beneath the scratch scope. -/
def writeUnderReduction {shape : CShape} (output : CWriteRef ctx shape) (sourceWidth width : Nat) :
    CWriteRef (reductionCtx ctx sourceWidth width) shape :=
  output.underWorkspace ctx.canonicalFreshKey (divisionShape sourceWidth width)
    ctx.canonicalFreshKey_fresh

/-- Actual freshly allocated division pair. -/
def divisionCell (ctx : RuntimeCtx kind) (sourceWidth width : Nat) :
    CWriteRef (reductionCtx ctx sourceWidth width) (divisionShape sourceWidth width) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (divisionShape sourceWidth width)
    ctx.canonicalFreshKey_fresh

/-- Original full quotient/remainder instruction at its actual operand widths. -/
def reductionDivideOp (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (divisionShape sourceWidth width)) :
    ClassicalOp (.product (.unsignedWord sourceWidth) (.unsignedWord (width + 1)))
      (divisionShape sourceWidth width) ctx ctx :=
  .divRem sourceWidth (width + 1) ctx (.product numerator modulus) division

/-- Original remainder materialization selects the second component and narrows once. -/
def reductionResizeOp (division : CWriteRef ctx (divisionShape sourceWidth width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord width) ctx ctx :=
  .wordResize (width + 1) width ctx (.second (reductionRead division)) output

/-- The two original native instructions execute in their original dependency order. -/
def reductionBody (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (divisionShape sourceWidth width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (reductionDivideOp numerator modulus division))
    (.classical (reductionResizeOp division output))

/-- Literal actual two-operation store and history record. -/
def reductionBodyStep (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (division : CWriteRef ctx (divisionShape sourceWidth width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (reductionBody numerator modulus division output).Path :=
  ((store.applyOp (reductionDivideOp numerator modulus division)).applyOp
    (reductionResizeOp division output), ((), ()))

/-- Actual lexical placement of the original two operations. -/
def reductionPlaced (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (reductionCtx ctx sourceWidth width) (reductionCtx ctx sourceWidth width) :=
  reductionBody (underReduction numerator sourceWidth width)
    (underReduction modulus sourceWidth width) (divisionCell ctx sourceWidth width)
    (writeUnderReduction output sourceWidth width)

/-- Actual reduction with its complete division-pair allocation and release. -/
def reduceWord (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (divisionShape sourceWidth width)
    ctx.canonicalFreshKey_fresh (reductionPlaced numerator modulus output)

/-- Complete actual caller-store update and path after releasing the division pair. -/
def reduceWordStep (numerator : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (reduceWord numerator modulus output).Path :=
  let result := reductionBodyStep (underReduction numerator sourceWidth width)
    (underReduction modulus sourceWidth width) (divisionCell ctx sourceWidth width)
    (writeUnderReduction output sourceWidth width) (store.pushWorkspace ctx.canonicalFreshKey
      (divisionShape sourceWidth width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (divisionShape sourceWidth width)
    ctx.canonicalFreshKey_fresh result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.Modular.Reduce.Native
