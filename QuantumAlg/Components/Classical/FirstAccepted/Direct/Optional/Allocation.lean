/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Fold
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Three actual lexical cells and one caller-owned optional output

The allocator establishes the false accepted flag and zero selected word in
its real store. Every source and the existing caller output are structurally
lifted. The complete loop precedes one paid pack instruction, which writes the
caller output before all three lexical cells are popped.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Allocation

noncomputable section

open Execution ClassicalWorkspace

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- The accepted flag, selected word and actual unpacked optional candidate. -/
def shapes (width : Nat) : List CShape :=
  [.bit, .unsignedWord width, .product .bit (.unsignedWord width)]

/-- The allocated physical cells are exactly the three destinations of optional selection. -/
def refs (cells : Cells ctx (shapes width)) : Optional.Refs ctx width where
  selection := ⟨cells.head.ref, cells.tail.head.ref⟩
  unpacked := cells.tail.tail.head.ref

/-- Actual fresh allocation supplies every pairwise destination separation. -/
lemma refs_separated (cells : Cells ctx (shapes width)) (distinct : cells.Distinct) :
    Optional.Separation (refs cells) := by
  cases cells with
  | cons accepted remaining =>
      cases remaining with
      | cons selected remaining =>
          cases remaining with
          | cons unpacked remaining =>
              cases remaining
              exact ⟨distinct.1.1.symm, distinct.1.2.1.symm, distinct.2.1.1.symm⟩

/-- Fresh lexical slots avoid every structural caller read automatically. -/
lemma refs_avoid {outer : RuntimeCtx kind} (cells : Cells ctx (shapes width))
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    {shape : CShape} (input : CInputRef outer shape) :
    Fold.Avoids (refs cells) (transport.liftInput input) := by
  cases cells with
  | cons accepted remaining =>
      cases remaining with
      | cons selected remaining =>
          cases remaining with
          | cons unpacked remaining =>
              cases remaining
              exact ⟨separated.1 input, separated.2.1 input, separated.2.2.1 input⟩

/-- Real allocation initializes the complete selector to the empty optional value. -/
lemma refs_initialized (cells : Cells ctx (shapes width)) (store : Store ctx)
    (initialized : cells.Initialized store) :
    Optional.selectedValue (refs cells).selection store = .optionNone := by
  cases cells with
  | cons accepted remaining =>
      cases remaining with
      | cons selected remaining =>
          cases remaining with
          | cons unpacked remaining =>
              cases remaining
              change CShape.packOption (.product (store.read (.storage accepted.ref.toCStorageRef))
                (store.read (.storage selected.ref.toCStorageRef))) = _
              rw [initialized.1, initialized.2.1]
              rfl

/-- Mathematical specification of the first populated chronological source word. -/
def value (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (store : Store ctx) : (CShape.option (.unsignedWord width)).Value :=
  (List.ofFn (fun index => store.read (inputs index))).foldl Optional.retainValue .optionNone

/-- The final paid instruction packs the existing selector cells into the caller output. -/
def packOp (selected : Optional.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) :=
  ClassicalOp.packOption ctx
    (.product (Direct.writeInput selected.selection.accepted)
      (Direct.writeInput selected.selection.selected)) output

variable {model : ExecutionModel} {environment : model.Environment}
  [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- All actual selection steps precede the sole caller-output pack. -/
def body (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner) : Circuit model inner
      inner :=
  .seq (Fold.into (model := model) (fun index => transport.liftInput (inputs index)) (refs cells))
    (BitWord.instruction (execution := model) (packOp (refs cells) (transport.liftWrite output)))

/-- The body record follows the actual fold and then writes its result through the real pack. -/
def bodyStep (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (store : Store inner × model.HiddenState) : (Store inner × model.HiddenState) × (body (model :=
      model) inputs output cells transport).Path :=
  Circuit.sequenceRecord
    (Fold.into (model := model) (fun index => transport.liftInput (inputs index)) (refs cells))
    (BitWord.instruction (execution := model) (packOp (refs cells) (transport.liftWrite output)))
    (Fold.step (model := model) (fun index => transport.liftInput (inputs index)) (refs cells))
    (fun current =>
      let actual := BitWord.instructionStep (execution := model)
        (packOp (refs cells) (transport.liftWrite output)) current.1
      ((actual.1, current.2), actual.2)) store

/-- The complete body executes on the same full store, history and quantum-reference state. -/
lemma body_execute (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (transport : Transport ctx inner)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State inner Reference (model.HiddenState × History)) :
    (body (model := model) inputs output cells transport).execute environment Reference state =
      state.mapClassical (fun entry =>
      let actual := bodyStep (model := model) inputs output cells transport (entry.1, entry.2.1)
      (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))) := by
  apply Circuit.execute_sequenceRecord (environment := environment)
  · exact Fold.into_execute _ _
  · intro reference _history _ current
    refine (BitWord.bitWord_instruction_execute (environment := environment)
      (packOp (refs cells) (transport.liftWrite output)) current).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual initialized body changes precisely the original caller output. -/
lemma body_store (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) {inner : RuntimeCtx model.kind}
    (cells : Cells inner (shapes width)) (distinct : cells.Distinct)
    (transport : Transport ctx inner) (separated : cells.TransportSeparated transport)
    (before : Store inner × model.HiddenState) (initialized : cells.Initialized before.1) :
    transport.restrict (bodyStep (model := model) inputs output cells transport before).1.1 =
      (transport.restrict before.1).write output (value inputs (transport.restrict before.1)) := by
  let lifted := fun index => transport.liftInput (inputs index)
  have unchanged : transport.restrict (Fold.step (model := model) lifted (refs cells) before).1.1 =
      transport.restrict before.1 := by
    apply Store.store_eq_of_storage_reads
    intro shape other
    exact (transport.workspaceTransport_restrict_readsAs _ (.storage other)).symm.trans
      ((Fold.into_callerFrame lifted (refs cells) before (transport.liftInput (.storage other))
        (refs_avoid cells transport separated (.storage other))).trans
        (transport.workspaceTransport_restrict_readsAs before.1 (.storage other)))
  have selected := Fold.into_correct lifted (refs cells) (refs_separated cells distinct)
    (fun index => refs_avoid cells transport separated (inputs index)) before
  rw [refs_initialized cells before.1 initialized] at selected
  have reads : (fun index => before.1.read (lifted index)) =
      (fun index => (transport.restrict before.1).read (inputs index)) :=
    funext (fun index => transport.workspaceTransport_restrict_readsAs before.1 (inputs index))
  rw [reads] at selected
  change transport.restrict ((Fold.step (model := model) lifted (refs cells) before).1.1.write
    (transport.liftWrite output)
    (Optional.selectedValue (refs cells).selection (Fold.step (model := model) lifted (refs cells)
      before).1.1)) = _
  rw [transport.workspaceTransport_restrict_write, unchanged, selected]
  rfl

/-- The actual allocator introduces only the three declared lexical workspaces. -/
def into (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) : Circuit model ctx ctx :=
  withCells ctx (shapes width) fun cells _distinct transport _separated =>
    body (model := model) inputs output cells transport

/-- Existing push/body/pop semantics provide the initialized full record and caller-store
equation. -/
lemma actualRecord (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (into (model :=
      model) inputs output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (into (model := model) inputs output).execute
          environment Reference state = state.mapClassical (fun
          entry =>
          let actual := record (entry.1, entry.2.1)
          (actual.1.1, (actual.1.2, (entry.2.2, actual.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (record before).1.1 = before.1.write output (value inputs before.1) := by
  apply withCells_actualRecord_initialized_restricted_post
    (environment := environment) ctx (shapes width)
    (fun cells _distinct transport _separated => body (model := model) inputs output cells
      transport)
    (fun before after => after = before.write output (value inputs before))
  intro inner cells distinct transport separated
  exact ⟨bodyStep (model := model) inputs output cells transport, body_execute inputs output cells
    transport,
    fun before initialized => body_store inputs output cells distinct transport separated
      before initialized⟩

/-- The chosen record is supplied by the proved actual lexical execution, not a second
interpreter. -/
def step (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (into (model := model) inputs
      output).Path :=
  Classical.choose (actualRecord (environment := environment) inputs output)

/-- Actual allocation, all selection steps, packing and release preserve the complete
reference state. -/
lemma into_execute (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) inputs output).execute
      environment Reference state = state.mapClassical (fun entry =>
      let actual := step
        (environment := environment) (model := model) inputs output (entry.1, entry.2.1)
      (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))) :=
  (Classical.choose_spec (actualRecord
    (environment := environment) inputs output)).1 Reference state

/-- The full returned caller store differs precisely by the specified output write. -/
lemma into_store (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx ×
      model.HiddenState) :
    (step
      (environment := environment)
      (model := model) inputs output store).1.1 = store.1.write output (value inputs store.1) :=
  (Classical.choose_spec (actualRecord (environment := environment) inputs output)).2 store

/-- The actual retained caller output contains the first populated original candidate. -/
lemma into_correct (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx ×
      model.HiddenState) :
    (step
      (environment := environment)
      (model := model) inputs output store).1.1.read (Direct.writeInput output) = value inputs
      store.1 := by
  rw [into_store]
  exact Store.read_write_same _ _ _

/-- Every structural caller read outside the sole final output write is preserved. -/
lemma into_callerFrame (inputs : Fin count → CInputRef ctx (.option (.unsignedWord width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx × model.HiddenState)
    {shape : CShape} (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) :
    (step
      (environment := environment)
      (model := model) inputs output store).1.1.read other = store.1.read other := by
  rw [into_store]
  exact Store.read_write_of_not_mem_storageKeys store.1 output _ other separate

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional.Allocation
