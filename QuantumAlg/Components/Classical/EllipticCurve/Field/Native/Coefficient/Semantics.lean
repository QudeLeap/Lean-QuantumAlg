/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient
import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Semantics
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Complete actual total field-coefficient semantics

Actual loading and lexical allocation establish the original widened XGCD
input, with no caller promises about temporary values. The returned residue
is the original right Bezout coefficient reduced modulo the intrinsic field
modulus. This total statement applies to raw denominators, including non-units;
it does not assert that every returned coefficient is a multiplicative inverse.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open NumberTheory.XGCD NumberTheory.XGCD.Native
open NumberTheory.Checked.SignedReduction

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The total original field result is the reduced right coefficient of widened raw XGCD. -/
def coefficientResidue (spec : ModulusSpec width) (denominator : CShape.Word width) :
    Residue spec :=
  residueOfInt spec
    (PureXGCD.finalState (NumberTheory.Checked.Native.widenedXgcdInput
      (CShape.wordOfNat (width + 1) spec.modulus) denominator)).secondRightCoefficient

/-- Original persistent scratch identities in chronological allocation order. -/
def CoefficientScratch.keys (scratch : CoefficientScratch ctx width) : List StorageKey :=
  [scratch.modulus.key, scratch.outputs.gcd.key,
    scratch.outputs.leftCoefficient.key, scratch.outputs.rightCoefficient.key]

/-- Actual allocation supplies these internal separation facts. -/
structure CoefficientScratch.Separation (denominator : CInputRef ctx (.unsignedWord width))
    (scratch : CoefficientScratch ctx width) : Prop where
  distinct : scratch.keys.Nodup
  modulusInput : scratch.modulus.key ∉ denominator.storageKeys

omit [BitWord.Selected model] in
private theorem coefficient_scratch_separated
    (denominator : CInputRef ctx (.unsignedWord width)) (scratch : CoefficientScratch ctx width)
    (separate : scratch.Separation denominator) :
    scratch.outputs.Distinct ∧ scratch.outputs.gcd.key ≠ scratch.modulus.key ∧
      scratch.outputs.leftCoefficient.key ≠ scratch.modulus.key ∧
      scratch.outputs.rightCoefficient.key ≠ scratch.modulus.key := by
  have distinct :
      (scratch.modulus.key ≠ scratch.outputs.gcd.key ∧
        scratch.modulus.key ≠ scratch.outputs.leftCoefficient.key ∧
        scratch.modulus.key ≠ scratch.outputs.rightCoefficient.key) ∧
      (scratch.outputs.gcd.key ≠ scratch.outputs.leftCoefficient.key ∧
        scratch.outputs.gcd.key ≠ scratch.outputs.rightCoefficient.key) ∧
      scratch.outputs.leftCoefficient.key ≠ scratch.outputs.rightCoefficient.key := by
    simpa [CoefficientScratch.keys] using separate.distinct
  exact ⟨⟨distinct.2.1.1, distinct.2.1.2, distinct.2.2⟩,
    distinct.1.1.symm, distinct.1.2.1.symm, distinct.1.2.2.symm⟩

omit [BitWord.Selected model] in
private theorem coefficient_word_eq {bits : Nat} (first second : CShape.Word bits)
    (same : first.toNat = second.toNat) : first = second := by
  cases first with
  | unsignedWord first =>
    cases second with
    | unsignedWord second => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- Original loader, raw engine and signed reducer share their actual intermediate stores. -/
theorem coefficientBody_actualRecord (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width)) (scratch : CoefficientScratch ctx width)
    (separate : scratch.Separation denominator) (output : CWriteRef ctx (.unsignedWord width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (coefficientBody (model := model) spec denominator scratch output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (coefficientBody (model := model) spec denominator scratch output).execute
          Reference state = state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          (∀ key ∈ scratch.keys, key ∉ other.storageKeys) →
          output.key ∉ other.storageKeys →
            (record before).1.1.read other = before.1.read other) ∧
        ((record before).1.1.read (coefficientRead output)).toNat =
          (coefficientResidue spec (before.1.read denominator)).val := by
  obtain ⟨distinct, gcdModulus, leftModulus, rightModulus⟩ :=
    coefficient_scratch_separated denominator scratch separate
  let modulus := coefficientRead scratch.modulus
  let raw := coefficientRead scratch.outputs.rightCoefficient
  let xgcd := NumberTheory.Checked.Native.withWidenedXgcd denominator modulus scratch.outputs
  let reduction := Native.withSignedReduction raw modulus output
  obtain ⟨xgcdRecord, xgcdEquation, xgcdCorrect⟩ :=
    NumberTheory.Checked.Native.withWidenedXgcd_actualRecord (model := model)
      denominator modulus scratch.outputs distinct
  obtain ⟨reductionRecord, reductionEquation, reductionCorrect⟩ :=
    Native.withSignedReduction_actualRecord (model := model) raw modulus output spec
  let tailRecord := Circuit.sequenceRecord xgcd reduction xgcdRecord reductionRecord
  let loader := ConstantWord.circuit scratch.modulus spec.modulus
  let loaderStep := ConstantWord.foldStep (model := model) scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))
  let loaderRecord := fun before : Store ctx × model.HiddenState =>
    let result := loaderStep before.1
    ((result.1, before.2), result.2)
  let record := Circuit.sequenceRecord loader (.seq xgcd reduction) loaderRecord tailRecord
  have tailEquation := Circuit.execute_sequenceRecord xgcd reduction xgcdRecord reductionRecord
    xgcdEquation reductionEquation
  refine ⟨record, Circuit.execute_sequenceRecord loader (.seq xgcd reduction)
    loaderRecord tailRecord
      (by
        intro reference history historyFinite initial
        exact (ConstantWord.constantWord_fold_execute (model := model) scratch.modulus _
          reference initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl))
      tailEquation, ?_⟩
  intro before
  let loaded := (loaderRecord before).1.1
  let loadedHidden := (loaderRecord before).1.2
  let computed := (xgcdRecord (loaded, loadedHidden)).1.1
  let computedHidden := (xgcdRecord (loaded, loadedHidden)).1.2
  have loadedModulus : (loaded.read modulus).toNat = spec.modulus :=
    (ConstantWord.constantWord_read (model := model)
      scratch.modulus spec.modulus before.1).trans
      (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec))
  have retainedDenominator : loaded.read denominator = before.1.read denominator :=
    ConstantWord.constantWord_fold_read_other (model := model) scratch.modulus _ denominator
      separate.modulusInput before.1
  have retainedModulus : computed.read modulus = loaded.read modulus :=
    (xgcdCorrect (loaded, loadedHidden)).1 modulus
      (by simpa [modulus, coefficientRead, CInputRef.storageKeys] using gcdModulus)
      (by simpa [modulus, coefficientRead, CInputRef.storageKeys] using leftModulus)
      (by simpa [modulus, coefficientRead, CInputRef.storageKeys] using rightModulus)
  constructor
  · intro shape other scratchFree outputFree
    exact ((reductionCorrect (computed, computedHidden)).1 other outputFree).trans
      (((xgcdCorrect (loaded, loadedHidden)).1 other
        (scratchFree _ (by simp [CoefficientScratch.keys]))
        (scratchFree _ (by simp [CoefficientScratch.keys]))
        (scratchFree _ (by simp [CoefficientScratch.keys]))).trans
          (ConstantWord.constantWord_fold_read_other (model := model) scratch.modulus _ other
            (scratchFree _ (by simp [CoefficientScratch.keys])) before.1))
  · have actual := (reductionCorrect (computed, computedHidden)).2
      ((congrArg CShape.Value.toNat retainedModulus).trans loadedModulus)
    have modulusWord : loaded.read modulus = CShape.wordOfNat (width + 1) spec.modulus := by
      apply coefficient_word_eq
      exact loadedModulus.trans (Nat.mod_eq_of_lt
        (modulusSpec_modulus_lt_extended spec)).symm
    have decoded : decodeRawSignedWord (computed.read raw) =
        (PureXGCD.finalState (NumberTheory.Checked.Native.widenedXgcdInput
          (loaded.read modulus) (loaded.read denominator))).secondRightCoefficient :=
      (xgcdCorrect (loaded, loadedHidden)).2.2.2
    have residueValue : reduceRawCoefficient spec (computed.read raw) =
        coefficientResidue spec (before.1.read denominator) := by
      unfold reduceRawCoefficient coefficientResidue
      change residueOfInt spec (decodeRawSignedWord (computed.read raw)) = _
      rw [decoded, modulusWord, retainedDenominator]
    exact actual.trans (congrArg Fin.val residueValue)

omit [BitWord.Selected model] in
private theorem coefficientScratch_keys (cells : Cells ctx (coefficientShapes width)) :
    (coefficientScratch cells).keys = cells.keys.reverse := by
  cases cells with
  | cons right rest =>
    cases rest with
    | cons left rest =>
      cases rest with
      | cons gcd rest =>
        cases rest with
        | cons modulus rest =>
          cases rest
          rfl

omit [BitWord.Selected model] in
private theorem coefficientScratch_separation {outer : RuntimeCtx model.kind}
    (denominator : CInputRef outer (.unsignedWord width))
    (cells : Cells ctx (coefficientShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    (coefficientScratch cells).Separation (transport.liftInput denominator) := by
  constructor
  · rw [coefficientScratch_keys]
    simpa only [List.nodup_reverse] using Cells.workspaceCells_distinct_keys_nodup cells distinct
  · apply Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (input := denominator)
    have member : (coefficientScratch cells).modulus.key ∈ (coefficientScratch cells).keys := by
      simp [CoefficientScratch.keys]
    rw [coefficientScratch_keys] at member
    exact List.mem_reverse.mp member

/-- Actual allocation supplies every internal condition for the original total coefficient. -/
theorem coefficientIntoWord_actualRecord (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (coefficientIntoWord (model := model) spec denominator output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (coefficientIntoWord (model := model) spec denominator output).execute
          Reference state = state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (∀ {shape : CShape} (other : CInputRef ctx shape), output.key ∉ other.storageKeys →
          (record before).1.1.read other = before.1.read other) ∧
        ((record before).1.1.read (coefficientRead output)).toNat =
          (coefficientResidue spec (before.1.read denominator)).val := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape), output.key ∉ other.storageKeys →
      after.read other = before.read other) ∧
    (after.read (coefficientRead output)).toNat =
      (coefficientResidue spec (before.read denominator)).val
  refine withCells_actualRecord_initialized_restricted_post ctx (coefficientShapes width)
    (fun cells _ transport _ => coefficientBody (model := model) spec
      (transport.liftInput denominator)
      (coefficientScratch cells) (transport.liftWrite output)) Post ?_
  intro inner cells distinct transport separated
  obtain ⟨record, equation, correct⟩ := coefficientBody_actualRecord (model := model) spec
    (transport.liftInput denominator) (coefficientScratch cells)
    (coefficientScratch_separation denominator cells distinct transport separated)
    (transport.liftWrite output)
  refine ⟨record, equation, ?_⟩
  intro before _initialized
  have entered : transport.ReadsAs (transport.restrict before.1) before.1 :=
    transport.workspaceTransport_restrict_readsAs before.1
  have returned : transport.ReadsAs (transport.restrict (record before).1.1)
      (record before).1.1 :=
    transport.workspaceTransport_restrict_readsAs (record before).1.1
  constructor
  · intro shape other outputFree
    have bodyFrame := (correct before).1 (transport.liftInput other) (fun key member => ?_)
      (by simpa only [transport.liftWrite_key, transport.liftInput_storageKeys] using outputFree)
    · exact (returned other).symm.trans (bodyFrame.trans (entered other))
    · rw [coefficientScratch_keys] at member
      exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
        (List.mem_reverse.mp member) other
  · have actual := (correct before).2
    have outputRead : (record before).1.1.read
        (coefficientRead (transport.liftWrite output)) =
        (transport.restrict (record before).1.1).read (coefficientRead output) := by
      simpa only [coefficientRead, transport.liftWrite_input] using
        returned (coefficientRead output)
    change ((transport.restrict (record before).1.1).read (coefficientRead output)).toNat = _
    refine (congrArg CShape.Value.toNat outputRead.symm).trans (actual.trans ?_)
    rw [entered denominator]

/-- The complete record is certified by the original total native sequence and lexical releases. -/
def coefficientIntoWordStep (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (coefficientIntoWord (model := model) spec denominator output).Path :=
  Classical.choose (coefficientIntoWord_actualRecord spec denominator output)

/-- All raw engine and signed-reduction paths preserve the complete actual quantum reference. -/
theorem coefficientIntoWord_execute (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (coefficientIntoWord (model := model) spec denominator output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := coefficientIntoWordStep spec denominator output (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  (Classical.choose_spec (coefficientIntoWord_actualRecord spec denominator output)).1
    Reference state

/-- The actual result is the original canonical right-coefficient residue on every raw input. -/
theorem coefficientIntoWord_toNat (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (hidden : model.HiddenState) :
    ((coefficientIntoWordStep spec denominator output (store, hidden)).1.1.read
      (coefficientRead output)).toNat =
      (coefficientResidue spec (store.read denominator)).val :=
  ((Classical.choose_spec (coefficientIntoWord_actualRecord spec denominator output)).2
    (store, hidden)).2

/-- Every caller read outside the result retains its original value through all actual scopes. -/
theorem coefficientIntoWord_read_other (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx)
    (hidden : model.HiddenState) :
    (coefficientIntoWordStep spec denominator output (store, hidden)).1.1.read other =
      store.read other :=
  ((Classical.choose_spec (coefficientIntoWord_actualRecord spec denominator output)).2
    (store, hidden)).1 other separate

/-- The complete returned Store is one canonical coefficient write, including operand aliases. -/
theorem coefficientIntoWordStep_store (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (hidden : model.HiddenState) :
    (coefficientIntoWordStep spec denominator output (store, hidden)).1.1 = store.write output
      (CShape.wordOfNat width (coefficientResidue spec (store.read denominator)).val) := by
  apply Store.store_eq_write_of_read_frame
  · apply coefficient_word_eq
    have fitted : (coefficientResidue spec (store.read denominator)).val < 2 ^ width :=
      lt_of_lt_of_le (coefficientResidue spec (store.read denominator)).isLt spec.le_capacity
    exact (coefficientIntoWord_toNat spec denominator output store hidden).trans
      (Nat.mod_eq_of_lt fitted).symm
  · intro shape input separate
    exact coefficientIntoWord_read_other spec denominator output (.storage input)
      (by simpa [CInputRef.storageKeys] using separate) store hidden

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
