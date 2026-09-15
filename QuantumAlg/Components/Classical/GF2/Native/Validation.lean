/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual validation of the original GF(2) sample equations

Every original sample bit and candidate bit is read by the real AND instruction,
then XORed into the actual parity cell. Each selected row clears parity inside
its original two bit scopes. The actual parity and success cells control the
original branches, including both failure markers and the final self-AND.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original ordered sample bit and candidate bit feed the actual product cell. -/
def validationProductOp (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (.bitsGet (.vectorGet input row) column)
    (.wordBitGet (.storage candidate.toCStorageRef) column)) product

/-- The current actual product is XORed into the current actual parity. -/
def validationParityOp (parity product : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (.storage parity.toCStorageRef)
    (.storage product.toCStorageRef)) parity

/-- Each original column executes AND before XOR. -/
def validationColumn (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) : Circuit ctx ctx :=
  .seq (.classical (validationProductOp input candidate product row column))
    (.classical (validationParityOp parity product))

/-- Real parity clear and the complete column traversal precede the stored parity branch. -/
def validationRowBody (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount) : Circuit ctx ctx :=
  .seq (.classical (pivotClearOp parity))
    (.seq (Circuit.forRange width (validationColumn input candidate parity product row))
      (.branch (.storage parity.toCStorageRef) (decisionChoice true success)))

/-- The original sample input passes through the actual parity and product cells. -/
def validationInput (input : CInputRef ctx (.fixedVector rowCount (.bits width))) :
    CInputRef (pivotSearchContext ctx) (.fixedVector rowCount (.bits width)) :=
  (input.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underWorkspace
    (pivotSinkContext ctx).canonicalFreshKey .bit (pivotSinkContext ctx).canonicalFreshKey_fresh

/-- The original parity cell remains live below the actual product cell. -/
def validationParity (ctx : RuntimeCtx kind) : CWriteRef (pivotSearchContext ctx) .bit :=
  (pivotLatch ctx).underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh

/-- The original row runs on the actual lifted caller cells and two real fresh bits. -/
def placedValidationRow (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) : Circuit (pivotSearchContext ctx) (pivotSearchContext ctx) :=
  validationRowBody (validationInput input) (pivotSearchWrite candidate)
    (pivotSearchWrite success) (validationParity ctx) (pivotLatch (pivotSinkContext ctx)) row

/-- The product bit is actually initialized and released inside the parity scope. -/
def scopedValidationRow (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) : Circuit (pivotSinkContext ctx) (pivotSinkContext ctx) :=
  .workspace (pivotSinkContext ctx) (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh (placedValidationRow input candidate success row)

/-- Both original row-validation cells have their actual ordered lexical lifetimes. -/
def validateRow (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (scopedValidationRow input candidate success row)

/-- The current actual success bit selects a row check or the original identity arm. -/
def validationRowChoice (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => validateRow input candidate success row

/-- Each original row first reads the actual current success cell. -/
def validationSample (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) : Circuit ctx ctx :=
  .branch (.storage success.toCStorageRef) (validationRowChoice input candidate success row)

/-- The original row traversal always retains its final real success self-AND. -/
def validateSamples (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit) :
    Circuit ctx ctx :=
  .seq (Circuit.forRange rowCount (validationSample input candidate success))
    (.classical (pivotSelectedOp success))

end QuantumAlg.ClassicalRoutines.GF2.Native
