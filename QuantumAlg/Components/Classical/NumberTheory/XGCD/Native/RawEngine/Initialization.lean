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
theorem xgcdNativeInitializedLoop_actualRecord {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (input : CInputRef outer (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef outer (.unsignedWord width)) :
    ∃ record : Store ctx → Store ctx ×
        (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
          (guardedActive cells (transport.liftInput zero))).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
          (guardedActive cells (transport.liftInput zero))).execute Reference state =
            state.mapClassical (fun entry =>
              ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        let initial := initializationStore cells
          (transport.liftInput input) (transport.liftInput zero) before
        (∀ {shape : CShape} (other : CInputRef outer shape),
          ((record initial).1).read (transport.liftInput other) =
            before.read (transport.liftInput other)) ∧
        (cells.Initialized before →
          (before.read (transport.liftInput zero)).toNat = 0 →
          storedReady cells (transport.liftInput zero) (record initial).1 ∧
            storedState cells (record initial).1 =
              PureXGCD.run (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
                (PureXGCD.initialState
                  (GCD.decodeOperands (before.read (transport.liftInput input))))) := by
  obtain ⟨record, equation, correct⟩ := xgcdNativeLoop_actualRecord cells distinct
    (transport.liftInput zero)
    (xgcdNativeState_input_separated cells transport separated zero)
    (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
  refine ⟨record, equation, ?_⟩
  intro before
  let initial := initializationStore cells
    (transport.liftInput input) (transport.liftInput zero) before
  constructor
  · intro shape other
    exact ((correct initial).1 (transport.liftInput other)
      (xgcdNativeState_input_separated cells transport separated other)).trans
        (xgcdNativeInitialization_read_caller cells transport separated
          (transport.liftInput input) (transport.liftInput zero) other before)
  · intro initialized zeroValue
    exact (correct initial).2 (GCD.decodeOperands (before.read (transport.liftInput input)))
      (xgcdNativeInitialization_ready cells distinct transport separated
        input zero before initialized zeroValue)
      (xgcdNativeInitialization_state cells distinct transport separated
        input zero before initialized zeroValue) le_rfl

/-- Combine the real initialization store with a proved actual loop record. -/
def initializedLoopRecord (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)).Path) : Store ctx → Store ctx ×
      (Circuit.seq (initializationBody cells input zero)
        (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
          (guardedActive cells zero))).Path :=
  Circuit.sequenceRecord (initializationBody cells input zero)
    (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive cells zero))
    (fun before => (initializationStore cells input zero before,
      ((), ((), ((), ((), ((), ()))))))) record

/-- The initialized loop record returns precisely the actual loop's post-initialization store. -/
theorem xgcdNativeInitializedLoop_record_store (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)).Path) (store : Store ctx) :
    (initializedLoopRecord cells input zero record store).1 =
      (record (initializationStore cells input zero store)).1 := rfl

/-- The existing sequential interpreter retains every quantum-reference block and both paths. -/
theorem xgcdNativeInitializedLoop_execute (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx ×
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero)).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (initializationBody cells input zero)
      (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
        (guardedActive cells zero))).execute Reference state =
      state.mapClassical (fun entry =>
        ((initializedLoopRecord cells input zero record entry.1).1,
          (entry.2, (initializedLoopRecord cells input zero record entry.1).2))) := by
  exact Circuit.execute_sequenceRecord (initializationBody cells input zero)
    (Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedActive cells zero))
    (fun before => (initializationStore cells input zero before,
      ((), ((), ((), ((), ((), ()))))))) record
    (fun reference {_} _ initial => by
      refine (xgcdNativeInitialization_execute cells input zero reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    equation Reference state

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
