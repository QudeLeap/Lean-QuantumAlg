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
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- Exact record of the explicit service reset. -/
@[expose] public def resetRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) × (resetQuery P result).Path :=
  ((entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G 1), .bit false)

public theorem resetQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (resetQuery P result).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := resetRecord P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [resetQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _ (fun _hidden _input =>
    (ClassicalFiniteGroupOracle.encode G 1, .bit false)) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_reset G hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exact record of one hidden-accumulator square. -/
@[expose] public def squareRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) × (squareQuery P result).Path :=
  ((entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G
    (ClassicalFiniteGroupOracle.decode G entry.2 *
      ClassicalFiniteGroupOracle.decode G entry.2)), .bit false)

public theorem squareQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (squareQuery P result).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := squareRecord P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [squareQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _ (fun hidden _input =>
    (ClassicalFiniteGroupOracle.encode G
      (ClassicalFiniteGroupOracle.decode G hidden *
        ClassicalFiniteGroupOracle.decode G hidden), .bit false)) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_square G hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exact record of multiplication by the sealed generator. -/
@[expose] public def multiplyGeneratorRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (multiplyGeneratorQuery P result).Path :=
  ((entry.1.write result (.bit false), ClassicalFiniteGroupOracle.encode G
    (ClassicalFiniteGroupOracle.decode G entry.2 * P.generator)), .bit false)

public theorem multiplyGeneratorQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (multiplyGeneratorQuery P result).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := multiplyGeneratorRecord P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [multiplyGeneratorQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _
    (fun hidden _input => (ClassicalFiniteGroupOracle.encode G
      (ClassicalFiniteGroupOracle.decode G hidden * P.generator), .bit false)) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_multiplyRightQuery G P.generator hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exact record of comparison with the sealed target. -/
@[expose] public def targetEqualityRecord (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (targetEqualityQuery P result).Path :=
  let value := .bit (ClassicalFiniteGroupOracle.equalResult G entry.2
    (ClassicalFiniteGroupOracle.encode G P.target))
  ((entry.1.write result value, entry.2), value)

public theorem targetEqualityQuery_execute (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (targetEqualityQuery P result).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := targetEqualityRecord P result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simp only [targetEqualityQuery, Circuit.execute_classicalQuery]
  refine (queryStep_of_pure _
    (fun hidden _input => (hidden, .bit (ClassicalFiniteGroupOracle.equalResult G hidden
      (ClassicalFiniteGroupOracle.encode G P.target)))) ?_ state).trans ?_
  · intro hidden input
    exact ClassicalFiniteGroupOracle.transition_equalsQuery G P.target hidden input
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual conditional multiplication and the selected branch path. -/
@[expose] public def multiplyChoiceRecord (result : CWriteRef ctx .bit)
    (value : CShape.Value .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (multiplyChoice P result value).Path :=
  match value with
  | .bit false => (entry, ())
  | .bit true => multiplyGeneratorRecord P result entry

private theorem multiplyChoice_execute (result : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (multiplyChoice P result value).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := multiplyChoiceRecord P result value (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  cases value with
  | bit value =>
      cases value
      · simp only [multiplyChoice, multiplyChoiceRecord]
        refine (Circuit.execute_id_mapClassical
          (model := OrderExecution.model P) (ctx := ctx) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · simpa only [multiplyChoice, multiplyChoiceRecord] using
          multiplyGeneratorQuery_execute P result Reference state

/-- One real square, bit read and selected multiplication, in execution order. -/
@[expose] public def powerStepRecord (bit : CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (powerStep P bit result).Path :=
  let squared := squareRecord P result entry
  let value := squared.1.1.read bit
  let selected := multiplyChoiceRecord P result value squared.1
  (selected.1, (squared.2, ⟨value, selected.2⟩))

public theorem powerStep_execute (bit : CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (powerStep P bit result).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := powerStepRecord P bit result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  exact Circuit.execute_sequenceRecord (squareQuery P result)
    (.branch bit (multiplyChoice P result))
    (squareRecord P result)
    (fun entry =>
      let value := entry.1.read bit
      let selected := multiplyChoiceRecord P result value entry
      (selected.1, ⟨value, selected.2⟩))
    (fun Reference {_} _ state => squareQuery_execute P result Reference state)
    (fun Reference {_} _ state =>
      Circuit.execute_branch_mapClassical
        (model := OrderExecution.model P) (ctx := ctx)
        bit (multiplyChoice P result) (multiplyChoiceRecord P result)
        (multiplyChoice_execute P result) Reference state) Reference state

/-- Complete record of the actual most-significant-first scan. -/
@[expose] public def powerScanRecord {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (powerScan P candidate result).Path :=
  Circuit.forRangeRecord width
    (fun index => powerStep P (.wordBitGet candidate index) result)
    (fun index => powerStepRecord P (.wordBitGet candidate index) result) entry

public theorem powerScan_execute {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (powerScan P candidate result).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := powerScanRecord P candidate result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  simpa only [powerScan, powerScanRecord] using
    (Circuit.execute_forRangeRecord width
      (fun index => powerStep P (.wordBitGet candidate index) result)
      (fun index => powerStepRecord P (.wordBitGet candidate index) result)
      (fun index => powerStep_execute P (.wordBitGet candidate index) result)
      Reference state)

/-- A power step changes no structural read outside its Boolean result cell. -/
public theorem powerStep_preserves_read (bit : CInputRef ctx .bit)
    (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (powerStepRecord P bit result entry).1.1.read other = entry.1.read other := by
  have first := Store.read_write_of_not_mem_storageKeys entry.1 result (.bit false) other separate
  change (multiplyChoiceRecord P result
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
public theorem powerRange_preserves_read (count : Nat)
    (bits : Fin count → CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (Circuit.forRangeRecord count
      (fun index => powerStep P (bits index) result)
      (fun index => powerStepRecord P (bits index) result) entry).1.1.read other =
      entry.1.read other := by
  induction count generalizing entry with
  | zero => rfl
  | succ count ih =>
      have tail := ih (bits := fun index => bits index.succ)
        (entry := (powerStepRecord P (bits 0) result entry).1)
      exact tail.trans
        (powerStep_preserves_read P (bits 0) result entry other separate)

public theorem powerScan_preserves_read {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (powerScanRecord P candidate result entry).1.1.read other = entry.1.read other :=
  powerRange_preserves_read P width (fun index => .wordBitGet candidate index)
    result entry other separate

/-- One stable candidate bit advances the mathematical hidden exponent. -/
public theorem powerStep_hidden (bit : CInputRef ctx .bit) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) (exponent : Nat)
    (hidden : entry.2 = ClassicalFiniteGroupOracle.encode G (P.generator ^ exponent))
    (separate : result.key ∉ bit.storageKeys) :
    (powerStepRecord P bit result entry).1.2 =
      ClassicalFiniteGroupOracle.encode G
        (P.generator ^ (2 * exponent + (entry.1.read bit).toBool.toNat)) := by
  have bitSame : (entry.1.write result (.bit false)).read bit = entry.1.read bit :=
    Store.read_write_of_not_mem_storageKeys entry.1 result _ bit separate
  change (multiplyChoiceRecord P result
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
public theorem powerRange_hidden (count : Nat) (bits : Fin count → CInputRef ctx .bit)
    (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) (exponent : Nat)
    (hidden : entry.2 = ClassicalFiniteGroupOracle.encode G (P.generator ^ exponent))
    (separate : ∀ index, result.key ∉ (bits index).storageKeys) :
    (Circuit.forRangeRecord count
      (fun index => powerStep P (bits index) result)
      (fun index => powerStepRecord P (bits index) result) entry).1.2 =
      ClassicalFiniteGroupOracle.encode G
        (P.generator ^ ClassicalAlgorithms.TerminalDecode.accumulatorFold count exponent
          (fun index => (entry.1.read (bits index)).toBool)) := by
  induction count generalizing exponent entry with
  | zero =>
      simpa only [Circuit.forRangeRecord,
        ClassicalAlgorithms.TerminalDecode.accumulatorFold_zero] using hidden
  | succ count ih =>
      have first := powerStep_hidden P (bits 0) result entry exponent hidden (separate 0)
      have remaining := ih
        (bits := fun index => bits index.succ)
        (entry := (powerStepRecord P (bits 0) result entry).1)
        (exponent := 2 * exponent + (entry.1.read (bits 0)).toBool.toNat)
        first (fun index => separate index.succ)
      have reads :
          (fun index : Fin count =>
            ((powerStepRecord P (bits 0) result entry).1.1.read
              (bits index.succ)).toBool) =
            (fun index : Fin count => (entry.1.read (bits index.succ)).toBool) := by
        funext index
        rw [powerStep_preserves_read P (bits 0) result entry
          (bits index.succ) (separate index.succ)]
      rw [reads] at remaining
      simpa only [Circuit.forRangeRecord,
        Circuit.sequenceRecord, Function.comp_def,
        ClassicalAlgorithms.TerminalDecode.accumulatorFold_succ] using remaining

/-- The complete stored word is the exponent held by the hidden accumulator. -/
public theorem powerScan_hidden {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    (hidden : entry.2 = ClassicalFiniteGroupOracle.encode G 1)
    (separate : result.key ∉ candidate.storageKeys) :
    (powerScanRecord P candidate result entry).1.2 =
      ClassicalFiniteGroupOracle.encode G
        (P.generator ^ (entry.1.read candidate).toNat) := by
  have computed := powerRange_hidden P width
    (fun index => .wordBitGet candidate index) result entry 0
    (by simpa only [pow_zero] using hidden) (fun _ => separate)
  exact computed.trans (congrArg (fun value => ClassicalFiniteGroupOracle.encode G
    (P.generator ^ value))
    (word_accumulatorFold_eq_toNat (entry.1.read candidate)))

/-- Record of explicit reset, power scan and target comparison. -/
@[expose] public def powerCheckRecord {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (powerCheck P candidate result).Path :=
  Circuit.sequenceRecord (resetQuery P result)
    (.seq (powerScan P candidate result) (targetEqualityQuery P result))
    (resetRecord P result)
    (Circuit.sequenceRecord (powerScan P candidate result) (targetEqualityQuery P result)
      (powerScanRecord P candidate result) (targetEqualityRecord P result)) entry

public theorem powerCheck_execute {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (powerCheck P candidate result).execute Reference state =
      state.mapClassical (fun entry =>
        let selected := powerCheckRecord P candidate result (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  have suffix := Circuit.execute_sequenceRecord
    (powerScan P candidate result) (targetEqualityQuery P result)
    (powerScanRecord P candidate result) (targetEqualityRecord P result)
    (powerScan_execute P candidate result)
    (targetEqualityQuery_execute P result)
  exact Circuit.execute_sequenceRecord
    (resetQuery P result)
    (.seq (powerScan P candidate result) (targetEqualityQuery P result))
    (resetRecord P result)
    (Circuit.sequenceRecord (powerScan P candidate result)
      (targetEqualityQuery P result) (powerScanRecord P candidate result)
      (targetEqualityRecord P result))
    (resetQuery_execute P result) suffix Reference state

/-- The actual service check writes exactly the mathematical group equation. -/
public theorem powerCheckRecord_value {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    (separate : result.key ∉ candidate.storageKeys) :
    (powerCheckRecord P candidate result entry).1.1.read
        (.storage result.toCStorageRef) =
      .bit (decide (P.generator ^ (entry.1.read candidate).toNat = P.target)) := by
  have resetCandidate :
      (entry.1.write result (.bit false)).read candidate = entry.1.read candidate :=
    Store.read_write_of_not_mem_storageKeys entry.1 result _ candidate separate
  have scanHidden := powerScan_hidden P candidate result (resetRecord P result entry).1
    rfl separate
  simp only [resetRecord] at scanHidden
  rw [resetCandidate] at scanHidden
  change (targetEqualityRecord P result
    (powerScanRecord P candidate result (resetRecord P result entry).1).1).1.1.read
      (.storage result.toCStorageRef) = _
  rw [targetEqualityRecord, Store.read_write_same]
  simp only [resetRecord]
  rw [scanHidden]
  simp only [ClassicalFiniteGroupOracle.equalResult,
    ClassicalFiniteGroupOracle.encode_inj]

/-- The complete service check changes no caller read outside its result cell. -/
public theorem powerCheckRecord_preserves_read {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width)) (result : CWriteRef ctx .bit)
    (entry : Store ctx × (OrderExecution.model P).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : result.key ∉ other.storageKeys) :
    (powerCheckRecord P candidate result entry).1.1.read other = entry.1.read other := by
  change (targetEqualityRecord P result
    (powerScanRecord P candidate result (resetRecord P result entry).1).1).1.1.read other = _
  rw [targetEqualityRecord,
    Store.read_write_of_not_mem_storageKeys _ result _ other separate,
    powerScan_preserves_read P candidate result _ other separate,
    resetRecord,
    Store.read_write_of_not_mem_storageKeys _ result _ other separate]

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
