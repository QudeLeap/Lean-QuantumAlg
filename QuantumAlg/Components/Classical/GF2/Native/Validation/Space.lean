/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Validation
import all QuantumAlg.Components.Classical.GF2.Native.Decision.Space
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual live space of original sample validation

An executed row really allocates its parity and product cells, even when the
column range is empty. The row traversal reuses those same two lexical slots.
Bounds keep the entire original resident and auxiliary contexts and do not
multiply simultaneous space by the row count or assume any success value.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private theorem column_resident
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width)
    (path : (validationColumn input candidate parity product row column).Path) :
    (validationColumn input candidate parity product row column).peakResidentSpace path =
      ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model)
      (validationProductOp input candidate product row column))
    (BitWord.instruction (execution := model) (validationParityOp parity product)) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_classical]
  exact SpacePool.max_self _

private theorem rowBody_resident
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount)
    (path : (validationRowBody input candidate success parity product row).Path) :
    (validationRowBody input candidate success parity product row).peakResidentSpace path =
      ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (pivotClearOp parity))
    (.seq (Circuit.forRange width (validationColumn input candidate parity product row))
      (.branch (.storage parity.toCStorageRef) (decisionChoice true success))) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq]
  apply SpacePool.max_eq_left
  refine SpacePool.max_le (Circuit.forRange_resident_le width _ _ le_rfl
    (fun column path => (column_resident input candidate parity product row column path).le)
    path.2.1) ?_
  exact (choice_resident true success path.2.2.1 path.2.2.2).le

/-- An executed row has both real bit cells plus the full resident context. -/
theorem gf2ValidationRow_resident
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (path : (validateRow input candidate success row).Path) :
    (validateRow input candidate success row).peakResidentSpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace) := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh (scopedValidationRow input candidate success row) path).trans ?_
  have inner := Circuit.peakResidentSpace_workspace (pivotSinkContext ctx).canonicalFreshKey
    .bit (pivotSinkContext ctx).canonicalFreshKey_fresh
    (placedValidationRow input candidate success row) path
  have body := rowBody_resident (validationInput input) (pivotSearchWrite candidate)
    (pivotSearchWrite success) (validationParity ctx) (pivotLatch (pivotSinkContext ctx)) row path
  have enclosed := inner.trans
    (congrArg (SpacePool.max (pivotSinkContext ctx).residentSpace) body)
  refine (congrArg (SpacePool.max ctx.residentSpace) enclosed).trans ?_
  apply SpacePool.ext
  intro axis
  change max (ctx.residentSpace axis)
      (max (SpacePool.ofShape .bit axis + ctx.residentSpace axis)
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis))) =
    SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis)
  omega

/-- The success branch charges the same two bits and full resident context. -/
theorem gf2ValidationSample_resident_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (path : (validationSample input candidate success row).Path) :
    (validationSample input candidate success row).peakResidentSpace path ≤
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · refine (SpacePool.max_zero _).le.trans ?_
        intro axis
        change ctx.residentSpace axis ≤ SpacePool.ofShape .bit axis +
          (SpacePool.ofShape .bit axis + ctx.residentSpace axis)
        omega
      · exact (gf2ValidationRow_resident input candidate success row path).le

/-- Actual row scopes are reused; the final marker keeps the whole original resident context. -/
theorem gf2ValidationSamples_resident_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (path : (validateSamples input candidate success).Path) :
    (validateSamples input candidate success).peakResidentSpace path ≤
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace) := by
  have entry : ctx.residentSpace ≤
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace) := by
    intro axis
    change ctx.residentSpace axis ≤ SpacePool.ofShape .bit axis +
      (SpacePool.ofShape .bit axis + ctx.residentSpace axis)
    omega
  refine (Circuit.peakResidentSpace_seq
    (Circuit.forRange rowCount (validationSample input candidate success))
    (BitWord.instruction (execution := model) (pivotSelectedOp success)) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical]
  exact SpacePool.max_le (Circuit.forRange_resident_le rowCount _ _ entry
    (gf2ValidationSample_resident_le input candidate success) path.1) entry

private theorem column_auxiliary
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width)
    (path : (validationColumn input candidate parity product row column).Path) :
    (validationColumn input candidate parity product row column).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model)
      (validationProductOp input candidate product row column))
    (BitWord.instruction (execution := model) (validationParityOp parity product)) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_classical]
  exact SpacePool.max_self _

private theorem rowBody_auxiliary
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount)
    (path : (validationRowBody input candidate success parity product row).Path) :
    (validationRowBody input candidate success parity product row).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (pivotClearOp parity))
    (.seq (Circuit.forRange width (validationColumn input candidate parity product row))
      (.branch (.storage parity.toCStorageRef) (decisionChoice true success))) path).trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_eq_left
  refine SpacePool.max_le (Circuit.forRange_auxiliary_le width _ _ le_rfl
    (fun column path => (column_auxiliary input candidate parity product row column path).le)
    path.2.1) ?_
  exact (choice_auxiliary true success path.2.2.1 path.2.2.2).le

/-- An executed row has both real bit cells plus the full auxiliary context. -/
theorem gf2ValidationRow_auxiliary
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (path : (validateRow input candidate success row).Path) :
    (validateRow input candidate success row).peakAuxiliarySpace path =
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace) := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh (scopedValidationRow input candidate success row) path).trans ?_
  have inner := Circuit.peakAuxiliarySpace_workspace (pivotSinkContext ctx).canonicalFreshKey
    .bit (pivotSinkContext ctx).canonicalFreshKey_fresh
    (placedValidationRow input candidate success row) path
  have body := rowBody_auxiliary (validationInput input) (pivotSearchWrite candidate)
    (pivotSearchWrite success) (validationParity ctx) (pivotLatch (pivotSinkContext ctx)) row path
  have enclosed := inner.trans
    (congrArg (SpacePool.max (pivotSinkContext ctx).auxiliarySpace) body)
  refine (congrArg (SpacePool.max ctx.auxiliarySpace) enclosed).trans ?_
  apply SpacePool.ext
  intro axis
  change max (ctx.auxiliarySpace axis)
      (max (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis)
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis))) =
    SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis)
  omega

/-- The success branch charges the same two bits and full auxiliary context. -/
theorem gf2ValidationSample_auxiliary_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (path : (validationSample input candidate success row).Path) :
    (validationSample input candidate success row).peakAuxiliarySpace path ≤
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · refine (SpacePool.max_zero _).le.trans ?_
        intro axis
        change ctx.auxiliarySpace axis ≤ SpacePool.ofShape .bit axis +
          (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis)
        omega
      · exact (gf2ValidationRow_auxiliary input candidate success row path).le

/-- Actual row scopes are reused; the final marker keeps the whole original auxiliary context. -/
theorem gf2ValidationSamples_auxiliary_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (path : (validateSamples input candidate success).Path) :
    (validateSamples input candidate success).peakAuxiliarySpace path ≤
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace) := by
  have entry : ctx.auxiliarySpace ≤
      SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace) := by
    intro axis
    change ctx.auxiliarySpace axis ≤ SpacePool.ofShape .bit axis +
      (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis)
    omega
  refine (Circuit.peakAuxiliarySpace_seq
    (Circuit.forRange rowCount (validationSample input candidate success))
    (BitWord.instruction (execution := model) (pivotSelectedOp success)) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical]
  exact SpacePool.max_le (Circuit.forRange_auxiliary_le rowCount _ _ entry
    (gf2ValidationSample_auxiliary_le input candidate success) path.1) entry

end QuantumAlg.ClassicalRoutines.GF2.Native
