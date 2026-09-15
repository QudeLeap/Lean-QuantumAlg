/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete store execution of the actual adjacent-word instructions

These records track the genuine widening, adjacent arithmetic and selected
underflow arm. Each theorem follows the existing circuit interpreter on its
entire store-history block and quantum-reference register.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual selected arm leaves the word alone or performs its real self-XOR. -/
def trimArmStep (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    (value : CShape.Value .bit) → Store ctx → Store ctx × (trimArm output value).Path
  | .bit false, store => (store, ())
  | .bit true, store => (store.applyOp (clearOp output), ())

/-- Record the actual bit read, the selected path and its true store update. -/
def trimStep (output : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (trim output).Path :=
  let value := store.read (highBit output)
  let next := trimArmStep output value store
  (next.1, ⟨value, next.2⟩)

/-- The two compile-time directions use their actual atomic or sequential paths. -/
def tailStep (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    (successor : Bool) → Store ctx → Store ctx × (tail successor output).Path
  | false, store =>
      let next := trimStep output (store.applyOp (adjacentOp false output))
      (next.1, ((), next.2))
  | true, store => (store.applyOp (adjacentOp true output), ())

/-- The actual complete adjacent-word record starts with its physical widening instruction. -/
def step (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (code successor input output).Path :=
  let next := tailStep output successor (store.applyOp (resizeOp input output))
  (next.1, ((), next.2))

private theorem trimArm_execute (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (trimArm output value).execute Reference state =
      state.mapClassical (fun entry => ((trimArmStep output value entry.1).1,
        (entry.2, (trimArmStep output value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        exact congrArg
          (fun decision : DecidableEq (Store ctx × (History × Unit)) =>
            @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
              decision state (fun entry => (entry.1, (entry.2, ())))) (Subsingleton.elim _ _)
      · refine (Circuit.execute_classical_mapClassical (clearOp output) Reference state).trans ?_
        exact congrArg
          (fun decision : DecidableEq (Store ctx × (History × Unit)) =>
            @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
              decision state (fun entry => (entry.1.applyOp (clearOp output), (entry.2, ()))))
          (Subsingleton.elim _ _)

/-- The actual stored highest bit chooses the same complete store-reference execution. -/
theorem trim_execute (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (trim output).execute Reference state =
      state.mapClassical (fun entry => ((trimStep output entry.1).1,
        (entry.2, (trimStep output entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (highBit output) (trimArm output) (trimArmStep output)
    (trimArm_execute output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (trim output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((trimStep output entry.1).1, (entry.2, (trimStep output entry.1).2))))
    (Subsingleton.elim _ _)

/-- Both actual adjacent tails preserve every original quantum-reference matrix block. -/
theorem tail_execute (successor : Bool) (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (tail successor output).execute Reference state =
      state.mapClassical (fun entry => ((tailStep output successor entry.1).1,
        (entry.2, (tailStep output successor entry.1).2))) := by
  cases successor
  · have actual := Circuit.execute_seq_mapClassical (.classical (adjacentOp false output))
      (trim output) (fun store => (store.applyOp (adjacentOp false output), ()))
      (trimStep output)
      (fun reference {_} _ initial => by
        simpa only [Circuit.mapClassical_canonicalDecision] using
          Circuit.execute_classical_mapClassical (adjacentOp false output) reference initial)
      (trim_execute output) Reference state
    refine actual.trans ?_
    exact congrArg
      (fun decision : DecidableEq (Store ctx × (History × (tail false output).Path)) =>
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
          (fun entry => ((tailStep output false entry.1).1,
            (entry.2, (tailStep output false entry.1).2)))) (Subsingleton.elim _ _)
  · refine (Circuit.execute_classical_mapClassical
      (adjacentOp true output) Reference state).trans ?_
    exact congrArg
      (fun decision : DecidableEq (Store ctx × (History × Unit)) =>
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
          (fun entry => (entry.1.applyOp (adjacentOp true output), (entry.2, ()))))
      (Subsingleton.elim _ _)

/-- Actual widening and the selected native tail compose on the unchanged complete register. -/
theorem code_execute (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code successor input output).execute Reference state =
      state.mapClassical (fun entry => ((step successor input output entry.1).1,
        (entry.2, (step successor input output entry.1).2))) := by
  have actual := Circuit.execute_seq_mapClassical (.classical (resizeOp input output))
    (tail successor output) (fun store => (store.applyOp (resizeOp input output), ()))
    (tailStep output successor)
    (fun reference {_} _ initial => by
      simpa only [Circuit.mapClassical_canonicalDecision] using
        Circuit.execute_classical_mapClassical (resizeOp input output) reference initial)
    (tail_execute successor output) Reference state
  refine actual.trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (code successor input output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((step successor input output entry.1).1,
          (entry.2, (step successor input output entry.1).2)))) (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord
