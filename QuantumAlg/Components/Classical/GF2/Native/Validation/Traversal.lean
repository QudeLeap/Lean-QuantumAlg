/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Validation.Scope
import all QuantumAlg.Components.Classical.GF2.Native.State
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation

/-!
# Actual success-controlled sample traversal and original equation satisfaction

The original current success bit controls every row, including all original
identity arms. The final real self-AND remains part of the executed record.
The original seven-cell transport supplies source separation; arbitrary old
success and candidate values, empty samples and zero width remain covered.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem candidate_free (candidate : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) :
    success.key ∉ (CInputRef.storage candidate.toCStorageRef).storageKeys := by
  simp only [CInputRef.storageKeys, List.mem_singleton]
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key success.toCStorageRef
    candidate.toCStorageRef same
  cases impossible

private theorem sample_read
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : success.key ∉ other.storageKeys) :
    (validationSampleStep input candidate success row store).1.read other = store.read other := by
  dsimp only [validationSampleStep]
  cases original : store.read (.storage success.toCStorageRef) with
  | bit value =>
    cases value
    · rfl
    · exact gf2ValidationRow_read_other input candidate success row store other separate

private theorem sample_success
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) :
    let word : ClassicalAlgorithms.Word width :=
      ⟨(store.read (.storage candidate.toCStorageRef)).toNat,
        (store.read (.storage candidate.toCStorageRef)).toNat_lt⟩
    ((validationSampleStep input candidate success row store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        decide (ClassicalAlgorithms.GF2.dot (ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian ((store.read input).get row))) word = 0)) := by
  dsimp only [validationSampleStep]
  cases original : store.read (.storage success.toCStorageRef) with
  | bit value =>
    cases value
    · simp only [validationRowChoiceStep, original, CShape.Value.toBool, Bool.false_and]
    · simpa only [validationRowChoiceStep, original, CShape.Value.toBool, Bool.true_and] using
        gf2ValidationRow_success input candidate success row store

private theorem rows_read
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (count : Nat) (indices : Fin count → Fin rowCount) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : success.key ∉ other.storageKeys) :
    (Circuit.forRangeRecord count
      (fun index => validationSample input candidate success (indices index))
      (fun index => validationSampleStep input candidate success (indices index)) store).1.read
        other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (Circuit.forRangeRecord count _ _
        (validationSampleStep input candidate success (indices 0) store).1).1.read other = _
      exact (ih (fun index => indices index.succ) _).trans
        (sample_read input candidate success (indices 0) store other separate)

private theorem rows_success
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (separate : success.key ∉ input.storageKeys)
    (count : Nat) (indices : Fin count → Fin rowCount) (store : Store ctx) :
    let word : ClassicalAlgorithms.Word width :=
      ⟨(store.read (.storage candidate.toCStorageRef)).toNat,
        (store.read (.storage candidate.toCStorageRef)).toNat_lt⟩
    ((Circuit.forRangeRecord count
      (fun index => validationSample input candidate success (indices index))
      (fun index => validationSampleStep input candidate success (indices index)) store).1.read
        (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        (List.ofFn indices).all fun row =>
          decide (ClassicalAlgorithms.GF2.dot (ClassicalAlgorithms.TerminalDecode.eval
            (TerminalDecode.decodeInput .bigEndian ((store.read input).get row))) word = 0)) := by
  induction count generalizing store with
  | zero => simp only [Circuit.forRangeRecord, List.ofFn_zero, List.all_nil, Bool.and_true]
  | succ count ih =>
      let first := (validationSampleStep input candidate success (indices 0) store).1
      have firstInput : first.read input = store.read input :=
        sample_read input candidate success (indices 0) store input separate
      have firstCandidate : first.read (.storage candidate.toCStorageRef) =
          store.read (.storage candidate.toCStorageRef) :=
        sample_read input candidate success (indices 0) store (.storage candidate.toCStorageRef)
          (candidate_free candidate success)
      change ((Circuit.forRangeRecord count _ _ first).1.read _).toBool = _
      rw [ih (fun index => indices index.succ) first, firstInput, firstCandidate,
        sample_success input candidate success (indices 0) store, List.ofFn_succ, List.all_cons]
      exact Bool.and_assoc _ _ _

private theorem selected_read (success : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (pivotSelectedOp success)).read (.storage success.toCStorageRef) =
      store.read (.storage success.toCStorageRef) := by
  refine (Store.read_applyOp_output store (pivotSelectedOp success)).trans ?_
  change Resource.BitOpcode.eval .and (.product (store.read (.storage success.toCStorageRef))
    (store.read (.storage success.toCStorageRef))) = _
  cases store.read (.storage success.toCStorageRef) with
  | bit value => cases value <;> rfl

/-- The real row branches and final marker preserve every other structural caller read. -/
theorem gf2ValidationSamples_read_other
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : success.key ∉ other.storageKeys) :
    (validateSamplesStep input candidate success store).1.read other = store.read other := by
  dsimp only [validateSamplesStep, Circuit.sequenceRecord]
  refine (Store.read_applyOp_of_not_mem_storageKeys _ (pivotSelectedOp success)
    other separate).trans ?_
  exact rows_read input candidate success rowCount id store other separate

/-- Actual row validation keeps incoming success exactly when all original equations hold. -/
theorem gf2ValidationSamples_success
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (store : Store ctx) (separate : success.key ∉ input.storageKeys) :
    let word : ClassicalAlgorithms.Word width :=
      ⟨(store.read (.storage candidate.toCStorageRef)).toNat,
        (store.read (.storage candidate.toCStorageRef)).toNat_lt⟩
    ((validateSamplesStep input candidate success store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        ClassicalAlgorithms.GF2.satisfies? (fun row => ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian ((store.read input).get row))) word) := by
  dsimp only [validateSamplesStep, Circuit.sequenceRecord]
  rw [selected_read]
  simpa only [List.ofFn_id, id_eq, ClassicalAlgorithms.GF2.satisfies?] using
    rows_success input candidate success separate rowCount id store

/-- The original seven-cell allocator supplies the only caller-source separation internally. -/
theorem gf2ValidationSamples_cellSuccess {outer : RuntimeCtx kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (store : Store ctx) :
    let word : ClassicalAlgorithms.Word width :=
      ⟨(store.read (.storage cells.tail.tail.head.ref.toCStorageRef)).toNat,
        (store.read (.storage cells.tail.tail.head.ref.toCStorageRef)).toNat_lt⟩
    ((validateSamplesStep (transport.liftInput input) cells.tail.tail.head.ref cells.head.ref
      store).1.read (.storage cells.head.ref.toCStorageRef)).toBool =
      ((store.read (.storage cells.head.ref.toCStorageRef)).toBool &&
        ClassicalAlgorithms.GF2.satisfies? (fun row => ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian
            ((store.read (transport.liftInput input)).get row))) word) := by
  have sourceFree : cells.head.ref.key ∉ (transport.liftInput input).storageKeys := by
    cases cells with
    | cons success tail => exact separated.1 input
  exact gf2ValidationSamples_success (transport.liftInput input) cells.tail.tail.head.ref
    cells.head.ref store sourceFree

end

end QuantumAlg.ClassicalRoutines.GF2.Native
