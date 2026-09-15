/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Records
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution
import all QuantumAlg.Components.Classical.FirstAccepted.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Complete execution of the ordered actual factor scan

The record follows the literal finite sequence of stored input references.
Each visit records the full native factor scope and the existing selector;
the initial latch clear and final option pack are real instructions in that
same circuit. These equations retain every Store-history block and arbitrary
external quantum reference, with no initialization or separation premise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The real nominal unpack feeds the existing selector's actual path. -/
def selectionStep (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (selection cells result).Path :=
  let selected := FirstAccepted.step (selectorInputs cells) (selectorRefs cells)
    (store.applyOp (unpackOp cells result))
  (selected.1, ((), selected.2))

/-- A real factor-recovery record precedes the actual first-success latch record. -/
def visitStep (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (visit source inputs cells result).Path :=
  let recovered := FactorRecovery.NativeFactorScope.step source
    inputs.parameter inputs.phase result store
  let selected := selectionStep cells result recovered.1
  (selected.1, (recovered.2, selected.2))

/-- Actual stores and paths of the literal reference list in its original order. -/
def scanStep (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (inputs : List (Inputs ctx N)) → Store ctx →
      Store ctx × (scan source cells result inputs).Path
  | [], store => (store, ())
  | inputs :: rest, store =>
      let visited := visitStep source inputs cells result store
      let later := scanStep source cells result rest visited.1
      (later.1, (visited.2, later.2))

/-- The real latch clear, complete scan and final nominal option write. -/
def step (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code source inputs cells result).Path :=
  let scanned := scanStep source cells result inputs (store.applyOp (clearAcceptedOp cells))
  (scanned.1.applyOp (packOp cells result), ((), (scanned.2, ())))

/-- The actual unpack and native selector preserve the full quantum-reference block. -/
theorem selection_execute (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (selection cells result).execute Reference state =
      state.mapClassical (fun entry => ((selectionStep cells result entry.1).1,
        (entry.2, (selectionStep cells result entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (unpackOp cells result))
    (FirstAccepted.circuit (selectorInputs cells) (selectorRefs cells))
    (fun store => (store.applyOp (unpackOp cells result), ()))
    (FirstAccepted.step (selectorInputs cells) (selectorRefs cells))
    (fun reference _ _ initial => FactorRecovery.NativeHalfPower.classical_path_execute
      (unpackOp cells result) reference initial _)
    (FirstAccepted.firstAccepted_execute (selectorInputs cells) (selectorRefs cells))
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (selection cells result).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((selectionStep cells result entry.1).1,
          (entry.2, (selectionStep cells result entry.1).2)))) (Subsingleton.elim _ _)

/-- Each actual visit uses its own genuine stored parameter and measured phase. -/
theorem visit_execute (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (visit source inputs cells result).execute Reference state =
      state.mapClassical (fun entry => ((visitStep source inputs cells result entry.1).1,
        (entry.2, (visitStep source inputs cells result entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (FactorRecovery.NativeFactorScope.code source inputs.parameter inputs.phase result)
    (selection cells result)
    (FactorRecovery.NativeFactorScope.step source inputs.parameter inputs.phase result)
    (selectionStep cells result)
    (FactorRecovery.NativeFactorScope.code_execute source inputs.parameter inputs.phase result)
    (selection_execute cells result) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (visit source inputs cells result).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((visitStep source inputs cells result entry.1).1,
          (entry.2, (visitStep source inputs cells result entry.1).2)))) (Subsingleton.elim _ _)

/-- The original finite ordering is the actual sequence executed on complete CQ blocks. -/
theorem scan_execute (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (inputs : List (Inputs ctx N)) :
    ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (scan source cells result inputs).execute Reference state =
        state.mapClassical (fun entry => ((scanStep source cells result inputs entry.1).1,
          (entry.2, (scanStep source cells result inputs entry.1).2))) := by
  induction inputs with
  | nil =>
      intro Reference History _ state
      refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      exact congrArg
        (fun decision : DecidableEq (Store ctx × (History × (Circuit.id ctx).Path)) =>
          @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
            decision state (fun entry => (entry.1, (entry.2, ())))) (Subsingleton.elim _ _)
  | cons inputs rest ih =>
      intro Reference History _ state
      refine (Circuit.execute_seq_mapClassical (visit source inputs cells result)
        (scan source cells result rest) (visitStep source inputs cells result)
        (scanStep source cells result rest) (visit_execute source inputs cells result)
        ih Reference state).trans ?_
      exact congrArg
        (fun decision : DecidableEq
            (Store ctx × (History × (scan source cells result (inputs :: rest)).Path)) =>
          @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
            decision state (fun entry => ((scanStep source cells result (inputs :: rest)
              entry.1).1, (entry.2, (scanStep source cells result (inputs :: rest) entry.1).2))))
        (Subsingleton.elim _ _)

private def scanPackStep (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (scan source cells result inputs)
      (.classical (packOp cells result))).Path :=
  let scanned := scanStep source cells result inputs store
  (scanned.1.applyOp (packOp cells result), (scanned.2, ()))

private theorem scanPack_execute (source : Input N) (inputs : List (Inputs ctx N))
    (cells : Cells ctx N) (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (scan source cells result inputs) (.classical (packOp cells result))).execute
      Reference state = state.mapClassical (fun entry =>
        ((scanPackStep source inputs cells result entry.1).1,
          (entry.2, (scanPackStep source inputs cells result entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (scan source cells result inputs)
    (.classical (packOp cells result)) (scanStep source cells result inputs)
    (fun store => (store.applyOp (packOp cells result), ()))
    (scan_execute source cells result inputs)
    (fun reference _ _ initial => FactorRecovery.NativeHalfPower.classical_path_execute
      (packOp cells result) reference initial _) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History ×
        (Circuit.seq (scan source cells result inputs) (.classical (packOp cells result))).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((scanPackStep source inputs cells result entry.1).1,
          (entry.2, (scanPackStep source inputs cells result entry.1).2)))) (Subsingleton.elim _ _)

/-- One actual execution includes initialization, every visit and the surviving result write. -/
theorem code_execute (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code source inputs cells result).execute Reference state =
      state.mapClassical (fun entry => ((step source inputs cells result entry.1).1,
        (entry.2, (step source inputs cells result entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (clearAcceptedOp cells))
    (.seq (scan source cells result inputs) (.classical (packOp cells result)))
    (fun store => (store.applyOp (clearAcceptedOp cells), ()))
    (scanPackStep source inputs cells result)
    (fun reference _ _ initial => FactorRecovery.NativeHalfPower.classical_path_execute
      (clearAcceptedOp cells) reference initial _)
    (scanPack_execute source inputs cells result) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (code source inputs cells result).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((step source inputs cells result entry.1).1,
          (entry.2, (step source inputs cells result entry.1).2)))) (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
