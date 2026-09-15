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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Both original native instructions preserve the full quantum reference and actual history. -/
theorem zeroBody_execute (candidate : CInputRef ctx (.unsignedWord width))
    (tag : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (zeroBody candidate tag output).execute Reference state = state.mapClassical
      (fun entry => (zeroBodyStore candidate tag output entry.1, (entry.2, ((), ())))) := by
  simp only [zeroBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The same actual candidate determines both the true comparison and the packed word. -/
theorem zeroBodyStore_eq (candidate : CInputRef ctx (.unsignedWord width))
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

private theorem candidate_initialized (cells : Cells ctx (zeroShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) :
    store.read (.storage cells.tail.head.ref.toCStorageRef) = CShape.wordOfNat width 0 := by
  cases cells with
  | cons tag rest =>
    cases rest with
    | cons candidate rest =>
      cases rest
      change store.read (.storage candidate.ref.toCStorageRef) = CShape.wordOfNat width 0
      simpa [CShape.wordOfNat] using initialized.2.1

private theorem tag_candidate_separate (cells : Cells ctx (zeroShapes width))
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

private theorem tag_avoids {outer : RuntimeCtx kind} (cells : Cells ctx (zeroShapes width))
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    {shape : CShape} (input : CInputRef outer shape) :
    cells.head.ref.key ∉ (transport.liftInput input).storageKeys := by
  cases cells with
  | cons tag rest => exact separated.1 input

/-- Actual original allocation supplies the candidate and returns precisely one caller write. -/
theorem zeroInto_actualRecord (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ∃ record : Store ctx → Store ctx × (zeroInto output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (zeroInto output).execute Reference state = state.mapClassical
          (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        before.write output (.optionSome (CShape.wordOfNat width 0)) := by
  apply withCells_actualRecord_initialized_post ctx (zeroShapes width)
    (fun cells _ transport _ => zeroBody (.storage cells.tail.head.ref.toCStorageRef)
      cells.head.ref (transport.liftWrite output))
    (fun source target => target = source.write output (.optionSome (CShape.wordOfNat width 0)))
  intro inner cells distinct transport separated
  refine ⟨fun store => (zeroBodyStore (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
    (transport.liftWrite output) store, ((), ())), ?_, ?_⟩
  · intro reference history _ initial
    refine (zeroBody_execute _ _ _ reference initial).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  intro source before reads initialized
  refine ⟨source.write output (.optionSome (CShape.wordOfNat width 0)), rfl, ?_⟩
  have bodyResult := zeroBodyStore_eq (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
    (transport.liftWrite output) before (tag_candidate_separate cells distinct)
  rw [candidate_initialized cells before initialized] at bodyResult
  have afterTag : transport.ReadsAs source
      (before.applyOp (tagOp (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref)) := by
    intro shape input
    exact (Store.read_applyOp_of_not_mem_storageKeys before
      (tagOp (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref)
      (transport.liftInput input) (tag_avoids cells transport separated input)).trans (reads input)
  apply (congrArg (transport.ReadsAs
    (source.write output (.optionSome (CShape.wordOfNat width 0)))) bodyResult).mpr
  exact transport.workspaceTransport_readsAs_write afterTag output
    (.optionSome (CShape.wordOfNat width 0))

/-- The actual zero routine has its certified Store and actual lexical execution path. -/
def zeroIntoStep (output : CWriteRef ctx (.option (.unsignedWord width))) :
    Store ctx → Store ctx × (zeroInto output).Path :=
  Classical.choose (zeroInto_actualRecord output)

/-- Complete zero-routine execution follows the same actual record for every input state. -/
theorem zeroInto_execute (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (zeroInto output).execute Reference state = state.mapClassical (fun entry =>
      ((zeroIntoStep output entry.1).1, (entry.2, (zeroIntoStep output entry.1).2))) :=
  (Classical.choose_spec (zeroInto_actualRecord output)).1 Reference state

/-- The actual zero-routine return changes exactly the selected destination. -/
theorem zeroIntoStep_store (output : CWriteRef ctx (.option (.unsignedWord width)))
    (before : Store ctx) :
    (zeroIntoStep output before).1 = before.write output (.optionSome (CShape.wordOfNat width 0)) :=
  (Classical.choose_spec (zeroInto_actualRecord output)).2 before

/-- The retained original endpoint preserves every caller entry and returns the actual some-zero. -/
theorem zeroRetained_actualRecord (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx → Store (ctx.addRetained key (.option (.unsignedWord width)) fresh) ×
        (zeroRetained ctx width key fresh).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (zeroRetained ctx width key fresh).execute Reference state = state.mapClassical
          (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        (before.pushRetained key (.option (.unsignedWord width)) fresh).write
          (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)
          (.optionSome (CShape.wordOfNat width 0)) := by
  let output := CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh
  let record (before : Store ctx) :=
    let final := zeroIntoStep output (before.pushRetained key (.option (.unsignedWord width)) fresh)
    (final.1, ((), final.2))
  refine ⟨record, ?_, ?_⟩
  · intro reference history historyFinite state
    refine (Circuit.execute_retain_seq_mapClassical ctx key (.option (.unsignedWord width)) fresh
      (zeroInto output) (zeroIntoStep output) (zeroInto_execute output) reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · intro before
    exact zeroIntoStep_store output (before.pushRetained key (.option (.unsignedWord width)) fresh)

/-- The original retained endpoint has its certified actual Store and retained execution path. -/
def zeroRetainedStep (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Store ctx → Store (ctx.addRetained key (.option (.unsignedWord width)) fresh) ×
      (zeroRetained ctx width key fresh).Path :=
  Classical.choose (zeroRetained_actualRecord ctx width key fresh)

/-- The same actual retained record preserves every complete quantum-reference block. -/
theorem zeroRetained_execute (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (zeroRetained ctx width key fresh).execute Reference state = state.mapClassical (fun entry =>
      ((zeroRetainedStep ctx width key fresh entry.1).1,
        (entry.2, (zeroRetainedStep ctx width key fresh entry.1).2))) :=
  (Classical.choose_spec (zeroRetained_actualRecord ctx width key fresh)).1 Reference state

/-- Actual retention leaves the original caller Store and the single retained some-zero result. -/
theorem zeroRetainedStep_store (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) (before : Store ctx) :
    (zeroRetainedStep ctx width key fresh before).1 =
      (before.pushRetained key (.option (.unsignedWord width)) fresh).write
        (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)
        (.optionSome (CShape.wordOfNat width 0)) :=
  (Classical.choose_spec (zeroRetained_actualRecord ctx width key fresh)).2 before

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native
