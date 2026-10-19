/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write
import all QuantumAlg.Core.Execution.Retained.Composition

/-!
# Complete actual order-one recovery state

The original equality instruction constructs the true tag from the same
actual candidate word. Real lexical allocation supplies the zero candidate
and all separation. The original option pack writes that candidate, then
both work cells are released. The enclosing actual retention preserves every
caller cell, quantum reference and previous execution history.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
variable {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Store and exact native outputs of the equality and option-pack sequence. -/
def zeroBodyStep (candidate : CInputRef ctx (.unsignedWord width))
    (tag : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))
    (before : Store ctx) : Store ctx × (zeroBody candidate tag output).Path :=
  let tagged := BitWord.instructionStep (execution := model) (tagOp candidate tag) before
  let packed := BitWord.instructionStep (execution := model) (packOp candidate tag output) tagged.1
  (packed.1, (tagged.2, packed.2))

/-- Both original native instructions preserve the full quantum reference and actual history. -/
lemma zeroBody_execute (candidate : CInputRef ctx (.unsignedWord width))
    (tag : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (zeroBody candidate tag output).execute environment Reference state = state.mapClassical
      (fun entry =>
        let result := zeroBodyStep candidate tag output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [zeroBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The record's store is the deterministic update used by the value proof. -/
lemma zeroBodyStep_store (candidate : CInputRef ctx (.unsignedWord width))
    (tag : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))
    (before : Store ctx) :
    (zeroBodyStep candidate tag output before).1 =
      zeroBodyStore candidate tag output before := by
  rfl

omit [BitWord.Selected model] in
/-- The same actual candidate determines both the true comparison and the packed word. -/
lemma zeroBodyStore_eq (candidate : CInputRef ctx (.unsignedWord width))
    (tag : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))
    (store : Store ctx) (separate : tag.key ∉ candidate.storageKeys) :
    zeroBodyStore candidate tag output store =
      (store.applyOp (tagOp candidate tag)).write output (.optionSome (store.read candidate)) := by
  have tagRead : (store.applyOp (tagOp candidate tag)).read (.storage tag.toCStorageRef) =
      .bit true := by
    change (store.applyOp (tagOp candidate tag)).read
      (.storage (tagOp candidate tag).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.Value.bit (decide
      ((store.read candidate).toNat = (store.read candidate).toNat)) = CShape.Value.bit true
    simp
  have candidateRead := Store.read_applyOp_of_not_mem_storageKeys store
    (tagOp candidate tag) candidate separate
  change (store.applyOp (tagOp candidate tag)).write output
    (CShape.packOption (.product
      ((store.applyOp (tagOp candidate tag)).read (.storage tag.toCStorageRef))
      ((store.applyOp (tagOp candidate tag)).read candidate))) = _
  rw [tagRead, candidateRead]
  rfl

omit [BitWord.Selected model] in
private lemma candidate_initialized (cells : Cells ctx (zeroShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) :
    store.read (.storage cells.tail.head.ref.toCStorageRef) = CShape.wordOfNat width 0 := by
  cases cells with
  | cons tag rest =>
    cases rest with
    | cons candidate rest =>
      cases rest
      change store.read (.storage candidate.ref.toCStorageRef) = CShape.wordOfNat width 0
      simpa [CShape.wordOfNat] using initialized.2.1

omit [BitWord.Selected model] in
private lemma tag_candidate_separate (cells : Cells ctx (zeroShapes width))
    (distinct : cells.Distinct) :
    cells.head.ref.key ∉ (CInputRef.storage cells.tail.head.ref.toCStorageRef).storageKeys := by
  cases cells with
  | cons tag rest =>
    cases rest with
    | cons candidate rest =>
      cases rest
      have different : tag.ref.key ≠ candidate.ref.key := Ne.symm distinct.1.1
      change tag.ref.key ∉ (CInputRef.storage candidate.ref.toCStorageRef).storageKeys
      simpa only [CInputRef.storageKeys, List.mem_singleton] using different

omit [BitWord.Selected model] in
private lemma tag_avoids {outer : RuntimeCtx model.kind} (cells : Cells ctx (zeroShapes width))
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    {shape : CShape} (input : CInputRef outer shape) :
    cells.head.ref.key ∉ (transport.liftInput input).storageKeys := by
  cases cells with
  | cons tag rest => exact separated.1 input

/-- Actual original allocation supplies the candidate and returns precisely one caller write. -/
lemma zeroInto_actualRecord (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ∃ record : Store ctx × model.HiddenState →
        (Store ctx × model.HiddenState) × (zeroInto output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (zeroInto output).execute environment Reference state = state.mapClassical
          (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        before.1.write output (.optionSome (CShape.wordOfNat width 0)) := by
  apply withCells_actualRecord_initialized_post (environment := environment) ctx (zeroShapes width)
    (fun cells _ transport _ => zeroBody (.storage cells.tail.head.ref.toCStorageRef)
      cells.head.ref (transport.liftWrite output))
    (fun source target => target = source.write output (.optionSome (CShape.wordOfNat width 0)))
  intro inner cells distinct transport separated
  refine ⟨fun before =>
    let result := zeroBodyStep (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
      (transport.liftWrite output) before.1
    ((result.1, before.2), result.2), ?_, ?_⟩
  · intro reference history _ initial
    exact zeroBody_execute _ _ _ reference initial
  intro source before reads initialized
  refine ⟨source.write output (.optionSome (CShape.wordOfNat width 0)), rfl, ?_⟩
  have bodyResult := zeroBodyStore_eq (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
    (transport.liftWrite output) before.1 (tag_candidate_separate cells distinct)
  rw [candidate_initialized cells before.1 initialized] at bodyResult
  have afterTag : transport.ReadsAs source
      (before.1.applyOp (tagOp (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref)) := by
    intro shape input
    exact (Store.read_applyOp_of_not_mem_storageKeys before.1
      (tagOp (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref)
      (transport.liftInput input) (tag_avoids cells transport separated input)).trans (reads input)
  apply (congrArg (transport.ReadsAs
    (source.write output (.optionSome (CShape.wordOfNat width 0)))) bodyResult).mpr
  exact transport.workspaceTransport_readsAs_write afterTag output
    (.optionSome (CShape.wordOfNat width 0))

/-- The actual zero routine has its certified Store and actual lexical execution path. -/
def zeroIntoStep (output : CWriteRef ctx (.option (.unsignedWord width))) :
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (zeroInto output).Path :=
  Classical.choose (zeroInto_actualRecord (environment := environment) output)

/-- Complete zero-routine execution follows the same actual record for every input state. -/
lemma zeroInto_execute (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (zeroInto output).execute environment Reference state = state.mapClassical (fun entry =>
      let result := zeroIntoStep (environment := environment) output (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  (Classical.choose_spec (zeroInto_actualRecord
    (environment := environment) output)).1 Reference state

/-- The actual zero-routine return changes exactly the selected destination. -/
lemma zeroIntoStep_store (output : CWriteRef ctx (.option (.unsignedWord width)))
    (before : Store ctx × model.HiddenState) :
    (zeroIntoStep (environment := environment) output before).1.1 =
      before.1.write output (.optionSome (CShape.wordOfNat width 0)) :=
  (Classical.choose_spec (zeroInto_actualRecord (environment := environment) output)).2 before

/-- The retained original endpoint preserves every caller entry and returns the actual some-zero. -/
lemma zeroRetained_actualRecord (ctx : RuntimeCtx model.kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx × model.HiddenState →
        (Store (ctx.addRetained key (.option (.unsignedWord width)) fresh) × model.HiddenState) ×
          (zeroRetained ctx width key fresh).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (zeroRetained ctx width key fresh).execute environment Reference state = state.mapClassical
          (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        (before.1.pushRetained key (.option (.unsignedWord width)) fresh).write
          (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)
          (.optionSome (CShape.wordOfNat width 0)) := by
  let output := CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh
  let record (before : Store ctx × model.HiddenState) :=
    let final := zeroIntoStep (environment := environment) output
      (before.1.pushRetained key (.option (.unsignedWord width)) fresh, before.2)
    (final.1, ((), final.2))
  refine ⟨record, ?_, ?_⟩
  · intro reference history historyFinite state
    refine (Circuit.execute_retain_seq_mapClassical
      (environment := environment) ctx key (.option (.unsignedWord width)) fresh
      (zeroInto output) (zeroIntoStep
        (environment := environment) output) (zeroInto_execute output) reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · intro before
    exact zeroIntoStep_store (environment := environment) output
      (before.1.pushRetained key (.option (.unsignedWord width)) fresh, before.2)

/-- The original retained endpoint has its certified actual Store and retained execution path. -/
def zeroRetainedStep (ctx : RuntimeCtx model.kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Store ctx × model.HiddenState →
      (Store (ctx.addRetained key (.option (.unsignedWord width)) fresh) × model.HiddenState) ×
        (zeroRetained ctx width key fresh).Path :=
  Classical.choose (zeroRetained_actualRecord (environment := environment) ctx width key fresh)

/-- The same actual retained record preserves every complete quantum-reference block. -/
lemma zeroRetained_execute (ctx : RuntimeCtx model.kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (zeroRetained ctx width key fresh).execute environment Reference state =
      state.mapClassical (fun entry =>
      let result := zeroRetainedStep
        (environment := environment) ctx width key fresh (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  (Classical.choose_spec (zeroRetained_actualRecord
    (environment := environment) ctx width key fresh)).1 Reference state

/-- Actual retention leaves the original caller Store and the single retained some-zero result. -/
lemma zeroRetainedStep_store (ctx : RuntimeCtx model.kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (before : Store ctx × model.HiddenState) :
    (zeroRetainedStep (environment := environment) ctx width key fresh before).1.1 =
      (before.1.pushRetained key (.option (.unsignedWord width)) fresh).write
        (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)
        (.optionSome (CShape.wordOfNat width 0)) :=
  (Classical.choose_spec (zeroRetained_actualRecord
    (environment := environment) ctx width key fresh)).2 before

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native
