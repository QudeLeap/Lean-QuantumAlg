/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Decision
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual raw-gcd decision and selected signed coefficient

The original fresh-one comparison writes the actual status bit. That bit
selects complete signed reduction or identity. Failure preserves the old
inverse destination; success computes the original canonical right coefficient.
The upstream raw XGCD producer supplies the meaning of the gcd and coefficient.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native

open Execution ClassicalAlgorithms.Modular SignedReduction

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original stored status selects signed reduction or a true no-operation branch. -/
def checkedCoefficientChoice (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then SignedReduction.Native.withSignedReduction raw modulus inverse else .id ctx

/-- Gcd-equals-one is actually computed before the original status-controlled signed reduction. -/
def checkedCoefficientSelection (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width)) :
    Circuit ctx ctx :=
  .seq (withUnitDecision gcd success)
    (.branch (decisionRead success) (checkedCoefficientChoice raw modulus inverse))

/-- Each real branch has a complete execution record with exact success and failure behavior. -/
theorem checkedCoefficientChoice_actualRecord
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (inverse : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width)
    (value : CShape.Value .bit) :
    ∃ record : Store ctx → Store ctx × (checkedCoefficientChoice raw modulus inverse value).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (checkedCoefficientChoice raw modulus inverse value).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape), inverse.key ∉ other.storageKeys →
          (record before).1.read other = before.read other) ∧
        (value.toBool = true → (before.read modulus).toNat = spec.modulus →
          ((record before).1.read (decisionRead inverse)).toNat =
            (reduceRawCoefficient spec (before.read raw)).val) ∧
        (value.toBool = false → (record before).1 = before) := by
  cases value with
  | bit value =>
      cases value
      · refine ⟨fun before => (before, ()), ?_, ?_⟩
        · intro reference history historyFinite state
          refine (Circuit.execute_id_mapClassical reference state).trans ?_
          congr 1
          exact Subsingleton.elim _ _
        · intro before
          exact ⟨fun _ _ => rfl, by simp [CShape.Value.toBool], fun _ => rfl⟩
      · obtain ⟨record, equation, correct⟩ :=
          SignedReduction.Native.withSignedReduction_actualRecord raw modulus inverse spec
        refine ⟨record, equation, ?_⟩
        intro before
        exact ⟨(correct before).1, fun _ => (correct before).2, by simp [CShape.Value.toBool]⟩

/-- Nominal bit and word destinations necessarily have distinct actual storage identities. -/
theorem checkedCoefficient_status_inverse_distinct (success : CWriteRef ctx .bit)
    (inverse : CWriteRef ctx (.unsignedWord width)) : inverse.key ≠ success.key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key inverse.toCStorageRef
    success.toCStorageRef same
  cases shapes

/-- The actual decision and selected coefficient preserve full state and both original outcomes. -/
theorem checkedCoefficientSelection_actualRecord
    (gcd : CInputRef ctx (.unsignedWord (width + 1)))
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (spec : ModulusSpec width) (rawFree : success.key ∉ raw.storageKeys)
    (modulusFree : success.key ∉ modulus.storageKeys) :
    ∃ record : Store ctx → Store ctx ×
        (checkedCoefficientSelection gcd raw modulus success inverse).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (checkedCoefficientSelection gcd raw modulus success inverse).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
            (record before).1.read other = before.read other) ∧
        (record before).1.read (decisionRead success) =
          .bit (decide ((before.read gcd).toNat = 1)) ∧
        ((before.read gcd).toNat = 1 → (before.read modulus).toNat = spec.modulus →
          ((record before).1.read (decisionRead inverse)).toNat =
            (reduceRawCoefficient spec (before.read raw)).val) ∧
        ((before.read gcd).toNat ≠ 1 →
          (record before).1.read (decisionRead inverse) = before.read (decisionRead inverse)) := by
  choose choiceRecord choiceEquation choiceCorrect using
    (fun value => checkedCoefficientChoice_actualRecord raw modulus inverse spec value)
  let branch := Circuit.branch (decisionRead success) (checkedCoefficientChoice raw modulus inverse)
  let branchRecord : Store ctx → Store ctx × branch.Path := fun before =>
    let value := before.read (decisionRead success)
    let chosen := choiceRecord value before
    (chosen.1, ⟨value, chosen.2⟩)
  refine ⟨Circuit.sequenceRecord (withUnitDecision gcd success) branch
    (withUnitDecisionStep gcd success) branchRecord, ?_, ?_⟩
  · intro reference history historyFinite state
    exact Circuit.execute_sequenceRecord _ _ _ _ (withUnitDecision_execute gcd success) (by
      intro reference history historyFinite state
      exact Circuit.execute_branch_mapClassical (decisionRead success)
        (checkedCoefficientChoice raw modulus inverse) choiceRecord choiceEquation reference state)
      reference state
  · intro before
    let decided := (withUnitDecisionStep gcd success before).1
    let value := decided.read (decisionRead success)
    let final := (choiceRecord value decided).1
    have valueEq : value = .bit (decide ((before.read gcd).toNat = 1)) :=
      withUnitDecision_value gcd success before
    have inverseStatus := checkedCoefficient_status_inverse_distinct success inverse
    have statusFree : inverse.key ∉ (decisionRead success).storageKeys := by
      simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton] using inverseStatus
    have inverseFree : success.key ∉ (decisionRead inverse).storageKeys := by
      simpa only [decisionRead, CInputRef.storageKeys, List.mem_singleton] using inverseStatus.symm
    have oldRaw : decided.read raw = before.read raw :=
      withUnitDecision_read_other gcd success raw rawFree before
    have oldModulus : decided.read modulus = before.read modulus :=
      withUnitDecision_read_other gcd success modulus modulusFree before
    change (∀ {shape : CShape} (other : CInputRef ctx shape),
      success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
        final.read other = before.read other) ∧ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro shape other successFree inverseFree
      exact ((choiceCorrect value decided).1 other inverseFree).trans
        (withUnitDecision_read_other gcd success other successFree before)
    · exact ((choiceCorrect value decided).1 (decisionRead success) statusFree).trans valueEq
    · intro one loaded
      have trueValue : value.toBool = true := by simp [valueEq, one, CShape.Value.toBool]
      have actual := (choiceCorrect value decided).2.1 trueValue (by rw [oldModulus, loaded])
      exact actual.trans (congrArg (fun input => (reduceRawCoefficient spec input).val) oldRaw)
    · intro notOne
      have falseValue : value.toBool = false := by simp [valueEq, notOne, CShape.Value.toBool]
      have unchanged := (choiceCorrect value decided).2.2 falseValue
      exact (congrArg (fun store => store.read (decisionRead inverse)) unchanged).trans
        (withUnitDecision_read_other gcd success (decisionRead inverse) inverseFree before)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Native
