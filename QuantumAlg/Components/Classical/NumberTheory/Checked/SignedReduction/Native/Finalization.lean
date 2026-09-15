/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Correction.Semantics
import all
  QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Correction.Resources

/-!
# Actual sign-selected final correction

The retained stored sign chooses the original four-operation negative
correction or the single nonnegative copy. The caller result is written only
after the required original operands have been read.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution Modular.Reduce.Native ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original nonnegative arm performs one charged native copy. -/
def correctionCopyOp (remainder : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx remainder output

/-- Actual sign selection retains both original correction arms. -/
def finalCorrectionChoice (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then withNegativeCorrection remainder modulus output
  else .classical (correctionCopyOp remainder output)

/-- True branch-local store updates and native paths. -/
def finalCorrectionChoiceStep (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (finalCorrectionChoice remainder modulus output value).Path :=
  match value with
  | .bit false => (store.applyOp (correctionCopyOp remainder output), ())
  | .bit true => withNegativeCorrectionStep remainder modulus output store

/-- The selector reads the actual sign bit left by classification. -/
def finalCorrection (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .branch negative (finalCorrectionChoice remainder modulus output)

/-- Actual original sign value and selected native path are both recorded. -/
def finalCorrectionStep (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (finalCorrection remainder modulus negative output).Path :=
  let value := store.read negative
  let chosen := finalCorrectionChoiceStep remainder modulus output value store
  (chosen.1, ⟨value, chosen.2⟩)

/-- Both real arms preserve the full reference-correlated quantum blocks and old histories. -/
theorem finalCorrectionChoice_execute (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (finalCorrectionChoice remainder modulus output value).execute Reference state =
      state.mapClassical (fun entry =>
        ((finalCorrectionChoiceStep remainder modulus output value entry.1).1,
          (entry.2, (finalCorrectionChoiceStep remainder modulus output value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_classical_mapClassical
          (correctionCopyOp remainder output) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · exact withNegativeCorrection_execute remainder modulus output Reference state

/-- The actual sign branch composes its full-state equation with its genuine stored selector. -/
theorem finalCorrection_execute (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (finalCorrection remainder modulus negative output).execute Reference state =
      state.mapClassical (fun entry =>
        ((finalCorrectionStep remainder modulus negative output entry.1).1,
          (entry.2, (finalCorrectionStep remainder modulus negative output entry.1).2))) :=
  Circuit.execute_branch_mapClassical negative (finalCorrectionChoice remainder modulus output)
    (finalCorrectionChoiceStep remainder modulus output)
    (finalCorrectionChoice_execute remainder modulus output) Reference state

/-- Both actual arms yield the precise finite word determined by their incoming stored sign. -/
theorem finalCorrectionChoice_value (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit) (store : Store ctx) :
    (finalCorrectionChoiceStep remainder modulus output value store).1.read (reductionRead output) =
      if value.toBool then negativeCorrectionValue (store.read remainder) (store.read modulus)
      else store.read remainder := by
  cases value with
  | bit value =>
      cases value
      · exact Store.read_applyOp_output store (correctionCopyOp remainder output)
      · exact withNegativeCorrection_value remainder modulus output store

/-- Every actual branch preserves structural reads outside the original output cell. -/
theorem finalCorrectionChoice_read_other (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (finalCorrectionChoiceStep remainder modulus output value store).1.read other =
      store.read other := by
  cases value with
  | bit value =>
      cases value
      · exact Store.read_applyOp_of_not_mem_storageKeys _
          (correctionCopyOp remainder output) other separate
      · exact withNegativeCorrection_read_other remainder modulus output other separate store

/-- The actual sign-controlled finalization writes only the original result cell. -/
theorem finalCorrection_read_other (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (finalCorrectionStep remainder modulus negative output store).1.read other = store.read other :=
  finalCorrectionChoice_read_other remainder modulus output _ other separate store

/-- Original canonical remainders give exactly the sign-dependent integer normalization. -/
theorem finalCorrection_original_value (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) (store : Store ctx)
    (modulusValue : (store.read modulus).toNat = spec.modulus)
    (remainderRange : (store.read remainder).toNat < spec.modulus) :
    ((finalCorrectionStep remainder modulus negative output store).1.read
      (reductionRead output)).toNat =
      if (store.read negative).toBool then
        if (store.read remainder).toNat = 0 then 0
        else spec.modulus - (store.read remainder).toNat
      else (store.read remainder).toNat := by
  change ((finalCorrectionChoiceStep remainder modulus output (store.read negative) store).1.read
    (reductionRead output)).toNat = _
  rw [finalCorrectionChoice_value]
  cases value : (store.read negative).toBool
  · rfl
  · simp only [if_true]
    exact (negativeCorrectionValue_original_toNat _ _ spec modulusValue remainderRange).trans
      (correctionRemainder_eq_normalized spec _ remainderRange)

/-- Original branch-dependent finalization events, without any replacement arithmetic. -/
def finalCorrectionEvents (kind : ProblemKind) (width : Nat) (negative : Bool) :
    List (Resource.Event kind) :=
  if negative then negativeCorrectionEvents kind width
  else [.classicalOperation (.wordUnary .copy width)]

/-- The actual selected finalization emits exactly the original four-or-one event list. -/
theorem finalCorrection_eventTrace (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (finalCorrection remainder modulus negative output).Path) :
    (finalCorrection remainder modulus negative output).eventTrace path =
      finalCorrectionEvents kind width path.1.toBool := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Actual finalization resource multiplicities retain the selected instruction list. -/
theorem finalCorrection_resourcePool (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (finalCorrection remainder modulus negative output).Path) :
    (finalCorrection remainder modulus negative output).resourcePool path =
      ResourcePool.ofList (finalCorrectionEvents kind width path.1.toBool) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Each actual branch charges precisely its original serial native durations. -/
theorem finalCorrection_durationDepth (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (finalCorrection remainder modulus negative output).Path) :
    (finalCorrection remainder modulus negative output).depth duration path =
      ((finalCorrectionEvents kind width path.1.toBool).map duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Exactly the selected real scratch scopes contribute to the resident peak. -/
theorem finalCorrection_resident (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (finalCorrection remainder modulus negative output).Path) :
    (finalCorrection remainder modulus negative output).peakResidentSpace path =
      (if path.1.toBool then negativeCorrectionScratchSpace width else 0) + ctx.residentSpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.residentSpace 0 = 0 + ctx.residentSpace
        simp only [SpacePool.max_zero, zero_add]
      · exact withNegativeCorrection_resident remainder modulus output path

/-- The auxiliary peak counts the same selected actual scratch allocation and release. -/
theorem finalCorrection_auxiliary (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (negative : CInputRef ctx .bit)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (finalCorrection remainder modulus negative output).Path) :
    (finalCorrection remainder modulus negative output).peakAuxiliarySpace path =
      (if path.1.toBool then negativeCorrectionScratchSpace width else 0) + ctx.auxiliarySpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.auxiliarySpace 0 = 0 + ctx.auxiliarySpace
        simp only [SpacePool.max_zero, zero_add]
      · exact withNegativeCorrection_auxiliary remainder modulus output path

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
