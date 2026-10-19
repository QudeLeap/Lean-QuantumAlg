/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Magnitude
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Finalization

/-!
# Actual signed-reduction body

Classification, actual sign-controlled magnitude, genuine modular reduction
and final correction execute in their original order. The internal work,
sign and remainder conditions are discharged by the enclosing fresh lexical
allocation. The output remains an arbitrary caller-owned destination.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution Modular.Reduce.Native ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Four original phases on the same real work, sign and remainder cells. -/
def signedReductionBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (signClassification (model := model) raw work negative)
    (.seq (signedMagnitude (model := model) raw work (signedRead negative))
      (.seq (reduceWord (model := model) (signedRead work) modulus remainder)
        (finalCorrection (model := model) (signedRead remainder) modulus (signedRead negative)
          output)))

/-- Actual intermediate stores, retained signs and instruction paths compose chronologically. -/
def signedReductionBodyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (signedReductionBody (model := model) raw modulus work negative remainder
      output).Path :=
  let classified := signClassificationStep (model := model) raw work negative store
  let magnitude := signedMagnitudeStep (model := model) raw work (signedRead negative) classified.1
  let reduced := reduceWordStep (model := model) (signedRead work) modulus remainder magnitude.1
  let result := finalCorrectionStep (model := model) (signedRead remainder) modulus (signedRead
    negative)
    output reduced.1
  (result.1, (classified.2, (magnitude.2, (reduced.2, result.2))))

/-- All real phases preserve complete quantum-reference blocks and retain the actual histories. -/
lemma signedReductionBody_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (signedReductionBody (model := model) raw modulus work negative remainder output).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        ((signedReductionBodyStep (model := model) raw modulus work negative remainder output
          entry.1).1,
          (entry.2.1, (entry.2.2, (signedReductionBodyStep (model := model) raw modulus work
            negative remainder output
            entry.1).2)))) := by
  simp only [signedReductionBody, Circuit.execute_seq, signClassification_execute,
    signedMagnitude_execute, reduceWord_execute, finalCorrection_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The only writes target the three true internal cells and the original output. -/
lemma signedReductionBody_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (workFree : work.key ∉ other.storageKeys)
    (negativeFree : negative.key ∉ other.storageKeys)
    (remainderFree : remainder.key ∉ other.storageKeys)
    (outputFree : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (signedReductionBodyStep (model := model) raw modulus work negative remainder output
      store).1.read other =
      store.read other := by
  unfold signedReductionBodyStep
  dsimp only
  rw [finalCorrection_read_other _ _ _ _ other outputFree,
    reduceWord_read_other _ _ _ other remainderFree,
    signedMagnitude_read_other _ _ _ other workFree]
  exact signClassification_read_other raw work negative other workFree negativeFree store

/-- Internal fresh-cell obligations suffice for the exact original canonical signed residue. -/
lemma signedReductionBody_original_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CWriteRef ctx .bit)
    (remainder output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width)
    (store : Store ctx) (initialZero : (store.read (signedRead work)).toNat = 0)
    (rawWork : work.key ∉ raw.storageKeys) (rawNegative : negative.key ∉ raw.storageKeys)
    (modulusWork : work.key ∉ modulus.storageKeys)
    (modulusNegative : negative.key ∉ modulus.storageKeys)
    (modulusRemainder : remainder.key ∉ modulus.storageKeys)
    (workNegative : work.key ≠ negative.key) (remainderNegative : remainder.key ≠ negative.key)
    (modulusValue : (store.read modulus).toNat = spec.modulus) :
    ((signedReductionBodyStep (model := model) raw modulus work negative remainder output
      store).1.read
      (signedRead output)).toNat = rawCanonicalNat spec (store.read raw) := by
  let classified := signClassificationStep (model := model) raw work negative store
  let magnitude := signedMagnitudeStep (model := model) raw work (signedRead negative) classified.1
  let reduced := reduceWordStep (model := model) (signedRead work) modulus remainder magnitude.1
  have signClassified : (classified.1.read (signedRead negative)).toBool =
      rawIsNegative (store.read raw) :=
    (signClassification_values raw work negative store initialZero rawWork workNegative.symm).1
  have rawClassified : classified.1.read raw = store.read raw :=
    signClassification_read_other raw work negative raw rawWork rawNegative store
  have modulusClassified : classified.1.read modulus = store.read modulus :=
    signClassification_read_other raw work negative modulus modulusWork modulusNegative store
  have magnitudeValue : (magnitude.1.read (signedRead work)).toNat =
      rawMagnitude (store.read raw) := by
    have classifiedValue : (classified.1.read (signedRead negative)).toBool =
        rawIsNegative (classified.1.read raw) := by rw [rawClassified, signClassified]
    exact (signedMagnitude_original_value raw work (signedRead negative)
      classified.1 classifiedValue).trans (congrArg rawMagnitude rawClassified)
  have workFree : work.key ∉ (signedRead negative).storageKeys := by
    simpa only [signedRead, CInputRef.storageKeys, List.mem_singleton] using workNegative
  have remainderFree : remainder.key ∉ (signedRead negative).storageKeys := by
    simpa only [signedRead, CInputRef.storageKeys, List.mem_singleton] using remainderNegative
  have signMagnitude : magnitude.1.read (signedRead negative) =
      classified.1.read (signedRead negative) :=
    signedMagnitude_read_other raw work _ (signedRead negative) workFree classified.1
  have modulusMagnitude : magnitude.1.read modulus = store.read modulus :=
    (signedMagnitude_read_other raw work _ modulus modulusWork classified.1).trans modulusClassified
  have reducedValue : (reduced.1.read (signedRead remainder)).toNat =
      rawMagnitude (store.read raw) % spec.modulus := by
    have loaded : (magnitude.1.read modulus).toNat = spec.modulus := by
      rw [modulusMagnitude, modulusValue]
    exact (reduceWord_original_value (signedRead work) modulus remainder spec magnitude.1
      loaded).trans (congrArg (· % spec.modulus) magnitudeValue)
  have modulusReduced : reduced.1.read modulus = store.read modulus :=
    (reduceWord_read_other (signedRead work) modulus remainder modulus modulusRemainder
      magnitude.1).trans modulusMagnitude
  have signReduced : (reduced.1.read (signedRead negative)).toBool =
      rawIsNegative (store.read raw) := by
    have same := reduceWord_read_other (signedRead work) modulus remainder
      (signedRead negative) remainderFree magnitude.1
    exact (congrArg CShape.Value.toBool (same.trans signMagnitude)).trans signClassified
  have remainderRange : (reduced.1.read (signedRead remainder)).toNat < spec.modulus := by
    rw [reducedValue]
    exact Nat.mod_lt _ (modulusSpec_modulus_pos spec)
  have loaded : (reduced.1.read modulus).toNat = spec.modulus := by
    rw [modulusReduced, modulusValue]
  change ((finalCorrectionStep (model := model) (signedRead remainder) modulus (signedRead negative)
    output reduced.1).1.read (reductionRead output)).toNat = _
  rw [finalCorrection_original_value _ _ _ _ spec reduced.1 loaded remainderRange,
    signReduced, reducedValue]
  rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
