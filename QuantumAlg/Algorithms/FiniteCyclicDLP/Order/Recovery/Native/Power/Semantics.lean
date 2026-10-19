/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power.Values
public import QuantumAlg.Core.Execution.Classical.Step.Deterministic
public import QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power
import all QuantumAlg.Components.Classical.Oracle.FiniteGroup
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Step.Deterministic
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Exact execution of the hidden finite-group power service

The records below use the selected oracle's declared transitions. They retain
the caller store, persistent hidden accumulator and arbitrary quantum-reference
blocks. The final value theorem connects the real reset/scan/equality sequence
to the mathematical group power without allocating an encoded group element.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {oracles : OracleModel}
variable {quantumEnvironment : oracles.Interpretation}
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- Exact record of the explicit service reset. -/
@[expose] public def resetRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) × (resetQuery (oracles := oracles) P
      result).Path :=
  ((entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G 1), .bit false)

public lemma resetQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (resetQuery (oracles := oracles) P result).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := resetRecord (oracles := oracles) P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [resetQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _ (ClassicalFiniteGroupOracle.interpretation G) (fun _hidden _input =>
    (ClassicalFiniteGroupOracle.encode G 1, .bit false)) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_reset G hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exact record of one hidden-accumulator square. -/
@[expose] public def squareRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) × (squareQuery (oracles := oracles) P
      result).Path :=
  ((entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G
    (ClassicalFiniteGroupOracle.decode G entry.2 *
      ClassicalFiniteGroupOracle.decode G entry.2)), .bit false)

public lemma squareQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (squareQuery (oracles := oracles) P result).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := squareRecord (oracles := oracles) P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [squareQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _ (ClassicalFiniteGroupOracle.interpretation G) (fun hidden _input =>
    (ClassicalFiniteGroupOracle.encode G
      (ClassicalFiniteGroupOracle.decode G hidden *
        ClassicalFiniteGroupOracle.decode G hidden), .bit false)) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_square G hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exact record of multiplication by the sealed generator. -/
@[expose] public def multiplyGeneratorRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) ×
      (multiplyGeneratorQuery (oracles := oracles) P result).Path :=
  ((entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G
    (ClassicalFiniteGroupOracle.decode G entry.2 * P.generator)), .bit false)

public lemma multiplyGeneratorQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (multiplyGeneratorQuery (oracles := oracles) P result).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := multiplyGeneratorRecord (oracles := oracles) P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [multiplyGeneratorQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _ (ClassicalFiniteGroupOracle.interpretation G)
    (fun hidden _input => (ClassicalFiniteGroupOracle.encode G
      (ClassicalFiniteGroupOracle.decode G hidden * P.generator), .bit false)) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_multiplyRightQuery G P.generator hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exact record of comparison with the sealed target. -/
@[expose] public def targetEqualityRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) ×
      (targetEqualityQuery (oracles := oracles) P result).Path :=
  let value := .bit (ClassicalFiniteGroupOracle.equalResult G entry.2
    (ClassicalFiniteGroupOracle.encode G P.target))
  ((entry.1.write result value, entry.2), value)

public lemma targetEqualityQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (targetEqualityQuery (oracles := oracles) P result).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := targetEqualityRecord (oracles := oracles) P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [targetEqualityQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _ (ClassicalFiniteGroupOracle.interpretation G)
    (fun hidden _input => (hidden, .bit (ClassicalFiniteGroupOracle.equalResult G hidden
      (ClassicalFiniteGroupOracle.encode G P.target)))) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_equalsQuery G P.target hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual conditional multiplication and the selected branch path. -/
@[expose] public def multiplyChoiceRecord (result : CWriteRef ctx .bit)
    (value : CShape.Value .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) ×
      (multiplyChoice (oracles := oracles) P result value).Path :=
  match value with
  | .bit false => (entry, ())
  | .bit true => multiplyGeneratorRecord (oracles := oracles) P result entry

private lemma multiplyChoice_execute (result : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (multiplyChoice (oracles := oracles) P result value).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := multiplyChoiceRecord (oracles := oracles) P result value (entry.1,
          entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  cases value with
  | bit value =>
      cases value
      · simp only [multiplyChoice, multiplyChoiceRecord]
        refine (Circuit.execute_id_mapClassical
          (model := recoveryModel P oracles) (ctx := ctx)
          (recoveryEnvironment P quantumEnvironment) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · simpa only [multiplyChoice, multiplyChoiceRecord] using
          multiplyGeneratorQuery_execute (oracles := oracles) P result Reference state

/-- One real square, bit read and selected multiplication, in execution order. -/
@[expose] public def powerStepRecord (bit : CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) ×
      (powerStep (oracles := oracles) P bit result).Path :=
  let squared := squareRecord (oracles := oracles) P result entry
  let value := squared.1.1.read bit
  let selected := multiplyChoiceRecord (oracles := oracles) P result value squared.1
  (selected.1, (squared.2, ⟨value, selected.2⟩))

public lemma powerStep_execute (bit : CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (powerStep (oracles := oracles) P bit result).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := powerStepRecord (oracles := oracles) P bit result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  exact Circuit.execute_sequenceRecord
    (environment := recoveryEnvironment P quantumEnvironment)
    (squareQuery (oracles := oracles) P result)
    (.branch bit (multiplyChoice (oracles := oracles) P result))
    (squareRecord (oracles := oracles) P result)
    (fun entry =>
      let value := entry.1.read bit
      let selected := multiplyChoiceRecord (oracles := oracles) P result value entry
      (selected.1, ⟨value, selected.2⟩))
    (fun Reference {_} _ state => squareQuery_execute (oracles := oracles) P result Reference state)
    (fun Reference {_} _ state =>
      Circuit.execute_branch_mapClassical
    (environment := recoveryEnvironment P quantumEnvironment)
        (model := recoveryModel P oracles) (ctx := ctx)
        bit (multiplyChoice (oracles := oracles) P result) (multiplyChoiceRecord (oracles :=
          oracles) P result)
        (multiplyChoice_execute (oracles := oracles) P result) Reference state) Reference state

/-- Complete record of the actual most-significant-first scan. -/
@[expose] public def powerScanRecord {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) ×
      (powerScan (oracles := oracles) P candidate result).Path :=
  Circuit.forRangeRecord width
    (fun index => powerStep (oracles := oracles) P (.wordBitGet candidate index) result)
    (fun index => powerStepRecord (oracles := oracles) P (.wordBitGet candidate index) result) entry

public lemma powerScan_execute {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (powerScan (oracles := oracles) P candidate result).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := powerScanRecord (oracles := oracles) P candidate result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simpa only [powerScan, powerScanRecord] using
    (Circuit.execute_forRangeRecord
    (environment := recoveryEnvironment P quantumEnvironment) width
      (fun index => powerStep (oracles := oracles) P (.wordBitGet candidate index) result)
      (fun index => powerStepRecord (oracles := oracles) P (.wordBitGet candidate index) result)
      (fun index => powerStep_execute (oracles := oracles) P (.wordBitGet candidate index) result)
      Reference state)

/-- A power step changes no structural read outside its Boolean result cell. -/
public lemma powerStep_preserves_read (bit : CInputRef ctx .bit)
    (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (powerStepRecord (oracles := oracles) P bit result entry).1.1.read other = entry.1.read
      other := by
  have first := Store.read_write_of_not_mem_storageKeys entry.1 result (.bit false) other separate
  change (multiplyChoiceRecord (oracles := oracles) P result
    ((entry.1.write result (.bit false)).read bit)
    (entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G
      (ClassicalFiniteGroupOracle.decode G entry.2 *
        ClassicalFiniteGroupOracle.decode G entry.2))).1.1.read other = _
  generalize (entry.1.write result (.bit false)).read bit = value
  cases value with
  | bit value =>
      cases value
      · exact first
      · exact (Store.read_write_of_not_mem_storageKeys
          (entry.1.write result (.bit false)) result (.bit false) other separate).trans first

/-- A consecutive scan changes no structural read outside the result cell. -/
public lemma powerRange_preserves_read (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (Circuit.forRangeRecord count
      (fun index => powerStep (oracles := oracles) P (bits index) result)
      (fun index => powerStepRecord (oracles := oracles) P (bits index) result) entry).1.1.read
        other =
      entry.1.read other := by
  induction count generalizing entry with
  | zero => rfl
  | succ count ih =>
      have tail := ih (bits := fun index => bits index.succ)
        (entry := (powerStepRecord (oracles := oracles) P (bits 0) result entry).1)
      exact tail.trans
        (powerStep_preserves_read (oracles := oracles) P (bits 0) result entry other separate)

public lemma powerScan_preserves_read {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (powerScanRecord (oracles := oracles) P candidate result entry).1.1.read other =
      entry.1.read other :=
  powerRange_preserves_read (oracles := oracles) P width (fun index => .wordBitGet candidate index)
    result entry other separate

/-- One stable candidate bit advances the mathematical hidden exponent. -/
public lemma powerStep_hidden (bit : CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) (exponent : Nat)
    (hidden : entry.2 = ClassicalFiniteGroupOracle.encode G (P.generator ^ exponent))
    (separate : result.key ∉ bit.storageKeys) :
    (powerStepRecord (oracles := oracles) P bit result entry).1.2 =
      ClassicalFiniteGroupOracle.encode G
        (P.generator ^ (2 * exponent + (entry.1.read bit).toBool.toNat)) := by
  have bitSame : (entry.1.write result (.bit false)).read bit = entry.1.read bit :=
    Store.read_write_of_not_mem_storageKeys entry.1 result _ bit separate
  change (multiplyChoiceRecord (oracles := oracles) P result
    ((entry.1.write result (.bit false)).read bit)
    (entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G
      (ClassicalFiniteGroupOracle.decode G entry.2 *
        ClassicalFiniteGroupOracle.decode G entry.2))).1.2 = _
  rw [bitSame, hidden]
  generalize entry.1.read bit = value
  cases value with
  | bit value =>
      cases value <;> simp [multiplyChoiceRecord, multiplyGeneratorRecord,
        ClassicalFiniteGroupOracle.decode_encode, CShape.Value.toBool, pow_add, two_mul]

/-- The ordered range computes the big-endian exponent fold in hidden state. -/
public lemma powerRange_hidden (count : Nat) (bits : Fin count → CInputRef ctx .bit)
    (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) (exponent : Nat)
    (hidden : entry.2 = ClassicalFiniteGroupOracle.encode G (P.generator ^ exponent))
    (separate : ∀ index, result.key ∉ (bits index).storageKeys) :
    (Circuit.forRangeRecord count
      (fun index => powerStep (oracles := oracles) P (bits index) result)
      (fun index => powerStepRecord (oracles := oracles) P (bits index) result) entry).1.2 =
      ClassicalFiniteGroupOracle.encode G
        (P.generator ^ ClassicalAlgorithms.TerminalDecode.accumulatorFold count exponent
          (fun index => (entry.1.read (bits index)).toBool)) := by
  induction count generalizing exponent entry with
  | zero =>
      simpa only [Circuit.forRangeRecord,
        ClassicalAlgorithms.TerminalDecode.accumulatorFold_zero] using hidden
  | succ count ih =>
      have first := powerStep_hidden (oracles := oracles) P (bits 0) result entry exponent
        hidden (separate 0)
      have remaining := ih
        (bits := fun index => bits index.succ)
        (entry := (powerStepRecord (oracles := oracles) P (bits 0) result entry).1)
        (exponent := 2 * exponent + (entry.1.read (bits 0)).toBool.toNat)
        first (fun index => separate index.succ)
      have reads :
          (fun index : Fin count =>
            ((powerStepRecord (oracles := oracles) P (bits 0) result entry).1.1.read
              (bits index.succ)).toBool) =
            (fun index : Fin count => (entry.1.read (bits index.succ)).toBool) := by
        funext index
        rw [powerStep_preserves_read (oracles := oracles) P (bits 0) result entry
          (bits index.succ) (separate index.succ)]
      rw [reads] at remaining
      simpa only [Circuit.forRangeRecord,
        Circuit.sequenceRecord, Function.comp_def,
        ClassicalAlgorithms.TerminalDecode.accumulatorFold_succ] using remaining

/-- The complete stored word is the exponent held by the hidden accumulator. -/
public lemma powerScan_hidden {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState)
    (hidden : entry.2 = ClassicalFiniteGroupOracle.encode G 1)
    (separate : result.key ∉ candidate.storageKeys) :
    (powerScanRecord (oracles := oracles) P candidate result entry).1.2 =
      ClassicalFiniteGroupOracle.encode G
        (P.generator ^ (entry.1.read candidate).toNat) := by
  have computed := powerRange_hidden (oracles := oracles) P width
    (fun index => .wordBitGet candidate index) result entry 0
    (by simpa only [pow_zero] using hidden) (fun _ => separate)
  exact computed.trans (congrArg (fun value => ClassicalFiniteGroupOracle.encode G
    (P.generator ^ value))
    (word_accumulatorFold_eq_toNat (entry.1.read candidate)))

/-- Record of explicit reset, power scan and target comparison. -/
@[expose] public def powerCheckRecord {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) ×
      (powerCheck (oracles := oracles) P candidate result).Path :=
  Circuit.sequenceRecord (resetQuery (oracles := oracles) P result)
    (.seq (powerScan (oracles := oracles) P candidate result) (targetEqualityQuery (oracles :=
      oracles) P result))
    (resetRecord (oracles := oracles) P result)
    (Circuit.sequenceRecord (powerScan (oracles := oracles) P candidate result)
      (targetEqualityQuery (oracles := oracles) P result)
      (powerScanRecord (oracles := oracles) P candidate result) (targetEqualityRecord (oracles
        := oracles) P result)) entry

public lemma powerCheck_execute {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (powerCheck (oracles := oracles) P candidate result).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let selected := powerCheckRecord (oracles := oracles) P candidate result (entry.1,
          entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  have suffix := Circuit.execute_sequenceRecord
    (environment := recoveryEnvironment P quantumEnvironment)
    (powerScan (oracles := oracles) P candidate result) (targetEqualityQuery (oracles :=
      oracles) P result)
    (powerScanRecord (oracles := oracles) P candidate result) (targetEqualityRecord (oracles :=
      oracles) P result)
    (powerScan_execute (oracles := oracles) P candidate result)
    (targetEqualityQuery_execute (oracles := oracles) P result)
  exact Circuit.execute_sequenceRecord
    (environment := recoveryEnvironment P quantumEnvironment)
    (resetQuery (oracles := oracles) P result)
    (.seq (powerScan (oracles := oracles) P candidate result) (targetEqualityQuery (oracles :=
      oracles) P result))
    (resetRecord (oracles := oracles) P result)
    (Circuit.sequenceRecord (powerScan (oracles := oracles) P candidate result)
      (targetEqualityQuery (oracles := oracles) P result) (powerScanRecord (oracles := oracles)
        P candidate result)
      (targetEqualityRecord (oracles := oracles) P result))
    (resetQuery_execute (oracles := oracles) P result) suffix Reference state

/-- The actual service check writes exactly the mathematical group equation. -/
public lemma powerCheckRecord_value {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState)
    (separate : result.key ∉ candidate.storageKeys) :
    (powerCheckRecord (oracles := oracles) P candidate result entry).1.1.read
        (.storage result.toCStorageRef) =
      .bit (decide (P.generator ^ (entry.1.read candidate).toNat = P.target)) := by
  have resetCandidate :
      (entry.1.write result (.bit false)).read candidate = entry.1.read candidate :=
    Store.read_write_of_not_mem_storageKeys entry.1 result _ candidate separate
  have scanHidden := powerScan_hidden (oracles := oracles) P candidate result (resetRecord
    (oracles := oracles) P result entry).1
    rfl separate
  simp only [resetRecord] at scanHidden
  rw [resetCandidate] at scanHidden
  change (targetEqualityRecord (oracles := oracles) P result
    (powerScanRecord (oracles := oracles) P candidate result (resetRecord (oracles := oracles)
      P result entry).1).1).1.1.read
      (.storage result.toCStorageRef) = _
  rw [targetEqualityRecord, Store.read_write_same]
  simp only [resetRecord]
  rw [scanHidden]
  simp only [ClassicalFiniteGroupOracle.equalResult,
    ClassicalFiniteGroupOracle.encode_inj]

/-- The complete service check changes no caller read outside its result cell. -/
public lemma powerCheckRecord_preserves_read {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (recoveryModel P oracles).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (powerCheckRecord (oracles := oracles) P candidate result entry).1.1.read other =
      entry.1.read other := by
  change (targetEqualityRecord (oracles := oracles) P result
    (powerScanRecord (oracles := oracles) P candidate result (resetRecord (oracles := oracles)
      P result entry).1).1).1.1.read other = _
  rw [targetEqualityRecord,
    Store.read_write_of_not_mem_storageKeys _ result _ other separate,
    powerScan_preserves_read (oracles := oracles) P candidate result _ other separate,
    resetRecord,
    Store.read_write_of_not_mem_storageKeys _ result _ other separate]

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
