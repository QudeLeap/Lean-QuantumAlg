/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Loop.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Depth
import all QuantumAlg.Core.Execution.Classical.Composition.Uniqueness

/-!
# Exact events of the same actual extended-Euclidean loop record

The recorded activity bit selects fourteen original operations or no events.
The full interpreter equation fixes that path, including when another proof
supplied the record existentially. The original mathematical unpadded path
therefore counts exactly the executed active steps, not the public fuel slots.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem scheduled_events_eq_path {Event : Type} (events : List Event)
    (count : Nat) (state : PureXGCD.State) :
    (List.ofFn (fun index : Fin count =>
      if (PureXGCD.run index.val state).first = 0 then [] else events)).flatten =
        (PureXGCD.path count state).flatMap (fun _ => events) := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.ofFn_succ, List.flatten_cons]
      by_cases stopped : state.first = 0
      · simp only [PureXGCD.run, PureXGCD.path,
          ClassicalAlgorithms.NumberTheory.XGCD.path, if_pos stopped,
          ClassicalAlgorithms.NumberTheory.XGCD.xgcdRun_of_stopped _ state stopped,
          List.flatMap_nil, List.nil_append]
        simp
      · simp only [Fin.val_zero, Fin.val_succ, PureXGCD.run, PureXGCD.path,
          ClassicalAlgorithms.NumberTheory.XGCD.run,
          ClassicalAlgorithms.NumberTheory.XGCD.path, if_neg stopped, List.flatMap_cons]
        rw [inductionHypothesis]

/-- Every certified record of the real branch retains precisely its actual incoming active bit. -/
theorem xgcdNativeGuardedRecord_eventTrace
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys)
    (record : Store ctx → Store ctx × (guardedActive cells zero).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (guardedActive cells zero).execute Reference state = state.mapClassical (fun entry =>
        ((record entry.1).1, (entry.2, (record entry.1).2)))) (store : Store ctx) :
    (guardedActive cells zero).eventTrace (record store).2 =
      if (store.read (GCD.cellRead (activeCell cells))).toBool then
        activeEvents kind width else [] := by
  obtain ⟨scopedRecord, scopedEquation, _⟩ :=
    xgcdNativeScopedActive_actualRecord cells distinct zero stateZero
  have same := Circuit.executionRecord_unique (guardedActive cells zero) record
    (guardedActiveRecord cells zero scopedRecord) equation
    (xgcdNativeGuardedActive_execute cells zero scopedRecord scopedEquation)
  rw [same, xgcdNativeGuardedActive_eventTrace]
  rfl

/-- The same actual loop record emits precisely the original unpadded mathematical path events. -/
theorem xgcdNativeLoop_record_eventTrace
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys) (count : Nat)
    (record : Store ctx → Store ctx × (Circuit.iterate count (guardedActive cells zero)).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (Circuit.iterate count (guardedActive cells zero)).execute Reference state =
        state.mapClassical (fun entry =>
          ((record entry.1).1, (entry.2, (record entry.1).2))))
    (store : Store ctx) (input : PureXGCD.Input width)
    (ready : storedReady cells zero store)
    (initial : storedState cells store = PureXGCD.initialState input)
    (within : count ≤ ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width) :
    (Circuit.iterate count (guardedActive cells zero)).eventTrace (record store).2 =
      (PureXGCD.path count (PureXGCD.initialState input)).flatMap
        (fun _ => activeEvents kind width) := by
  obtain ⟨bodyRecord, bodyEquation, correct⟩ :=
    xgcdNativeGuardedActive_actualRecord cells distinct zero stateZero
  have same := Circuit.executionRecord_unique (Circuit.iterate count (guardedActive cells zero))
    record (iteratedActiveRecord cells zero bodyRecord count) equation
    (xgcdNativeLoop_execute cells zero bodyRecord bodyEquation count)
  rw [same]
  change (List.ofFn (fun index : Fin count =>
    (guardedActive cells zero).eventTrace
      (bodyRecord ((fun before => (bodyRecord before).1)^[index.val] store)).2)).flatten = _
  calc
    _ = (List.ofFn (fun index : Fin count =>
        if (PureXGCD.run index.val (PureXGCD.initialState input)).first = 0 then []
        else activeEvents kind width)).flatten := by
      congr 1
      apply congrArg List.ofFn
      funext index
      have invariant := xgcdNativeLoop_state cells zero bodyRecord
        (fun before => (correct before).2) index.val store input ready initial (by omega)
      have currentReady : storedReady cells zero
          ((fun before => (bodyRecord before).1)^[index.val] store) := invariant.1
      have currentState : storedState cells
          ((fun before => (bodyRecord before).1)^[index.val] store) =
            PureXGCD.run index.val (PureXGCD.initialState input) := invariant.2
      rw [xgcdNativeGuardedRecord_eventTrace cells distinct zero stateZero
        bodyRecord bodyEquation, currentReady.2, currentState]
      by_cases stopped : (PureXGCD.run index.val (PureXGCD.initialState input)).first = 0
      · simp only [stopped, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          if_false, if_true]
      · simp only [stopped, ne_eq, not_false_eq_true, decide_true, if_true, if_false]
    _ = _ := scheduled_events_eq_path (activeEvents kind width) count (PureXGCD.initialState input)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
