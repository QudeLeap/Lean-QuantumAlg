/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Loop.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!+# Actual initialization followed by the original extended-Euclidean loop

Fresh state cells and the enclosing fresh zero sentinel establish readiness.
The original input and width-derived fuel then determine the complete decoded
loop result, without intermediate range premises. The same actual loop record
is available for the original right-associated final output composition.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual fresh initialization establishes both the zero sentinel and current activity. -/
theorem xgcdNativeInitialization_ready {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) (store : Store ctx)
    (initialized : cells.Initialized store)
    (zeroValue : (store.read (transport.liftInput zero)).toNat = 0) :
    storedReady cells (transport.liftInput zero)
      (initializationStore cells (transport.liftInput input) (transport.liftInput zero) store) := by
  constructor
  · rw [xgcdNativeInitialization_read_caller cells transport separated
      (transport.liftInput input) (transport.liftInput zero) zero store]
    exact zeroValue
  · exact xgcdNativeInitialization_activity cells distinct transport separated
      input zero store initialized zeroValue

/-- One actual loop record follows initialization and preserves every transported caller read. -/
theorem xgcdNativeInitializedLoop_actualRecord {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {outer : RuntimeCtx model.kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
          (guardedActive (model := model) cells (transport.liftInput zero))).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
          (guardedActive (model := model) cells (transport.liftInput zero))).execute
            Reference state =
            state.mapClassical (fun entry =>
              let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        let initial := initializationStore cells
          (transport.liftInput input) (transport.liftInput zero) before.1
        (∀ {shape : CShape} (other : CInputRef outer shape),
          ((record (initial, before.2)).1.1).read (transport.liftInput other) =
            before.1.read (transport.liftInput other)) ∧
        (cells.Initialized before.1 →
          (before.1.read (transport.liftInput zero)).toNat = 0 →
          storedReady cells (transport.liftInput zero) (record (initial, before.2)).1.1 ∧
            storedState cells (record (initial, before.2)).1.1 =
              PureXGCD.run (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
                (PureXGCD.initialState
                  (GCD.decodeOperands (before.1.read (transport.liftInput input))))) := by
  obtain ⟨record, equation, correct⟩ := xgcdNativeLoop_actualRecord (model := model) cells distinct
    (transport.liftInput zero)
    (xgcdNativeState_input_separated cells transport separated zero)
    (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
  refine ⟨record, equation, ?_⟩
  intro before
  let initial := initializationStore cells
    (transport.liftInput input) (transport.liftInput zero) before.1
  constructor
  · intro shape other
    exact ((correct (initial, before.2)).1 (transport.liftInput other)
      (xgcdNativeState_input_separated cells transport separated other)).trans
        (xgcdNativeInitialization_read_caller cells transport separated
          (transport.liftInput input) (transport.liftInput zero) other before.1)
  · intro initialized zeroValue
    exact (correct (initial, before.2)).2
      (GCD.decodeOperands (before.1.read (transport.liftInput input)))
      (xgcdNativeInitialization_ready cells distinct transport separated
        input zero before.1 initialized zeroValue)
      (xgcdNativeInitialization_state cells distinct transport separated
        input zero before.1 initialized zeroValue) le_rfl

/-- Combine the real initialization store with a proved actual loop record. -/
def initializedLoopRecord {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).Path) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (Circuit.seq (initializationBody (model := model) cells input zero)
        (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
          (guardedActive (model := model) cells zero))).Path :=
  Circuit.sequenceRecord (initializationBody (model := model) cells input zero)
    (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive (model := model) cells zero))
    (fun before =>
      let result := initializationStep (model := model) cells input zero before.1
      ((result.1, before.2), result.2)) record

/-- The initialized loop record returns precisely the actual loop's post-initialization store. -/
theorem xgcdNativeInitializedLoop_record_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).Path) (store : Store ctx × model.HiddenState) :
    (initializedLoopRecord (model := model) cells input zero record store).1 =
      (record (initializationStore cells input zero store.1, store.2)).1 := rfl

/-- The existing sequential interpreter retains every quantum-reference block and both paths. -/
theorem xgcdNativeInitializedLoop_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero)).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (initializationBody (model := model) cells input zero)
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive (model := model) cells zero))).execute Reference state =
      state.mapClassical (fun entry =>
        let result := initializedLoopRecord (model := model) cells input zero record
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  exact Circuit.execute_sequenceRecord (initializationBody (model := model) cells input zero)
    (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive (model := model) cells zero))
    (fun before =>
      let result := initializationStep (model := model) cells input zero before.1
      ((result.1, before.2), result.2)) record
    (fun reference {_} _ initial => by
      refine (xgcdNativeInitialization_execute cells input zero reference initial).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl)
    equation Reference state

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
