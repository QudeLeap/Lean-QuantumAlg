/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Interpretation
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Selection
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Correctness
import all QuantumAlg.Components.Classical.ConstantWord.Semantics

/-!
# Actual checked-inverse body and its original mathematical result

The body loads its own modulus, runs the original widened raw XGCD and uses
the actually computed gcd decision to select signed reduction. The complete
record proves the original unit decision and deterministic inverse coefficient.
All separation conditions below describe internal persistent cells; lexical
allocation discharges them at the complete caller entry.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution ClassicalAlgorithms.Modular SignedReduction XGCD.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original loaded-modulus, widened-XGCD and checked signed-reduction sequence. -/
def checkedInverseBody (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width)) :
    Circuit ctx ctx :=
  .seq (ConstantWord.circuit modulus spec.modulus)
    (.seq (withWidenedXgcd denominator (decisionRead modulus) outputs)
      (checkedCoefficientSelection (decisionRead outputs.gcd)
        (decisionRead outputs.rightCoefficient) (decisionRead modulus) success inverse))

/-- The actual complete body produces the original unit test and canonical inverse coefficient. -/
theorem checkedInverseBody_actualRecord (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (outputs : RawOutputs ctx (width + 1))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (distinct : outputs.Distinct) (denominatorFree : modulus.key ∉ denominator.storageKeys)
    (gcdModulus : outputs.gcd.key ≠ modulus.key)
    (leftModulus : outputs.leftCoefficient.key ≠ modulus.key)
    (rightModulus : outputs.rightCoefficient.key ≠ modulus.key)
    (successRaw : success.key ≠ outputs.rightCoefficient.key)
    (successModulus : success.key ≠ modulus.key)
    (modulusInverse : modulus.key ≠ inverse.key)
    (gcdInverse : outputs.gcd.key ≠ inverse.key)
    (leftInverse : outputs.leftCoefficient.key ≠ inverse.key)
    (rightInverse : outputs.rightCoefficient.key ≠ inverse.key) :
    ∃ record : Store ctx → Store ctx ×
        (checkedInverseBody spec denominator modulus outputs success inverse).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (checkedInverseBody spec denominator modulus outputs success inverse).execute
          Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          modulus.key ∉ other.storageKeys → outputs.gcd.key ∉ other.storageKeys →
          outputs.leftCoefficient.key ∉ other.storageKeys →
          outputs.rightCoefficient.key ∉ other.storageKeys →
          success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
            (record before).1.read other = before.read other) ∧
        ∀ semantic : Residue spec, (before.read denominator).toNat = semantic.val →
          (record before).1.read (decisionRead success) = .bit (Engine.unitDecision spec semantic) ∧
          (Engine.unitDecision spec semantic = true →
            ((record before).1.read (decisionRead inverse)).toNat =
              (Engine.inverseCoefficient spec semantic).val) ∧
          (Engine.unitDecision spec semantic = false →
            (record before).1.read (decisionRead inverse) =
              before.read (decisionRead inverse)) := by
  obtain ⟨rawRecord, rawEquation, rawCorrect⟩ := withWidenedXgcd_actualRecord denominator
    (decisionRead modulus) outputs distinct
  obtain ⟨selectedRecord, selectedEquation, selectedCorrect⟩ :=
    checkedCoefficientSelection_actualRecord (decisionRead outputs.gcd)
      (decisionRead outputs.rightCoefficient) (decisionRead modulus) success inverse spec
      (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton] using successRaw)
      (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton] using successModulus)
  let loader := ConstantWord.circuit modulus spec.modulus
  let raw := withWidenedXgcd denominator (decisionRead modulus) outputs
  let selected := checkedCoefficientSelection (decisionRead outputs.gcd)
    (decisionRead outputs.rightCoefficient) (decisionRead modulus) success inverse
  let loadRecord := ConstantWord.foldStep modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))
  let suffixRecord := Circuit.sequenceRecord raw selected rawRecord selectedRecord
  refine ⟨Circuit.sequenceRecord loader (Circuit.seq raw selected) loadRecord suffixRecord, ?_, ?_⟩
  · intro reference history historyFinite state
    exact Circuit.execute_sequenceRecord loader (Circuit.seq raw selected) loadRecord suffixRecord
      (ConstantWord.constantWord_fold_execute modulus _) (by
        intro reference history historyFinite state
        exact Circuit.execute_sequenceRecord raw selected rawRecord selectedRecord
          rawEquation selectedEquation reference state) reference state
  · intro before
    let loaded := (loadRecord before).1
    let produced := (rawRecord loaded).1
    let final := (selectedRecord produced).1
    have loadedModulus : (loaded.read (decisionRead modulus)).toNat = spec.modulus :=
      (ConstantWord.constantWord_read modulus spec.modulus before).trans
        (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec))
    have loadedDenominator : loaded.read denominator = before.read denominator :=
      ConstantWord.constantWord_fold_read_other modulus _ denominator denominatorFree before
    have producedModulus : produced.read (decisionRead modulus) =
        loaded.read (decisionRead modulus) :=
      (rawCorrect loaded).1 (decisionRead modulus)
        (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton] using gcdModulus)
        (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton] using leftModulus)
        (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton] using rightModulus)
    change (∀ {shape : CShape} (other : CInputRef ctx shape), _ → _ → _ → _ → _ → _ →
      final.read other = before.read other) ∧ _
    constructor
    · intro shape other modulusFree gcdFree leftFree rightFree successFree inverseFree
      exact ((selectedCorrect produced).1 other successFree inverseFree).trans
        (((rawCorrect loaded).1 other gcdFree leftFree rightFree).trans
          (ConstantWord.constantWord_fold_read_other modulus _ other modulusFree before))
    · intro semantic represented
      have inputEq := widenedXgcdInput_eq_xgcdInput spec
        (loaded.read (decisionRead modulus)) (loaded.read denominator) semantic loadedModulus
        ((congrArg CShape.Value.toNat loadedDenominator).trans represented)
      have actual := (rawCorrect loaded).2
      rw [inputEq] at actual
      have values := xgcdNativeRawOutputs_finalState_values outputs produced
        (Engine.xgcdInput spec semantic) actual.1 actual.2.1 actual.2.2
      have oneIff := Engine.checkedEngine_rawGcdOne_iff_unitDecision spec semantic
        (produced.read (decisionRead outputs.gcd)) values.1
      have decisionEq : decide ((produced.read (decisionRead outputs.gcd)).toNat = 1) =
          Engine.unitDecision spec semantic := by
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using oneIff
      refine ⟨((selectedCorrect produced).2.1).trans
        (congrArg CShape.Value.bit decisionEq), ?_, ?_⟩
      · intro successValue
        have coefficientEq := Engine.reduceRawCoefficient_eq_inverseCoefficient spec semantic
          (produced.read (decisionRead outputs.rightCoefficient)) values.2.2
        exact ((selectedCorrect produced).2.2.1 (oneIff.mpr successValue)
          ((congrArg CShape.Value.toNat producedModulus).trans loadedModulus)).trans
            (congrArg Fin.val coefficientEq)
      · intro failureValue
        have notOne : (produced.read (decisionRead outputs.gcd)).toNat ≠ 1 := by
          intro one
          have trueValue := oneIff.mp one
          rw [failureValue] at trueValue
          contradiction
        have producedInverse : produced.read (decisionRead inverse) =
            loaded.read (decisionRead inverse) :=
          (rawCorrect loaded).1 (decisionRead inverse)
            (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton]
              using gcdInverse)
            (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton]
              using leftInverse)
            (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton]
              using rightInverse)
        exact ((selectedCorrect produced).2.2.2 notOne).trans (producedInverse.trans
          (ConstantWord.constantWord_fold_read_other modulus _ (decisionRead inverse)
            (by simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton]
              using modulusInverse) before))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
