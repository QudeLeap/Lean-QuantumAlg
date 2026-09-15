/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.LexicalSemantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Total execution of the retained native GCD circuit

The circuit itself allocates its zero result before entering the Euclidean
work scopes. Its exact state equation keeps the full incoming quantum block,
external reference and real selected paths. The final read is the original
total GCD evaluator, including zero operands and width zero, without an
initialization or nonaliasing condition on caller storage.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual retained allocation followed by the exact lexical store transformation. -/
def retainedStep (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx) :
    Store (retainedCtx ctx width key fresh) × (retainedCircuit input key fresh).Path :=
  let final := lexicalStep (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)
    (store.pushRetained key (.unsignedWord width) fresh)
  (final.1, ((), final.2))

/-- Every complete block undergoes the actual store and path update of the retained circuit. -/
theorem gcdRetained_execute (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (retainedCircuit input key fresh).execute Reference state =
      state.mapClassical (fun entry =>
        ((retainedStep input key fresh entry.1).1,
          (entry.2, (retainedStep input key fresh entry.1).2))) := by
  let body := lexicalBody (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)
  let entered : State (ctx.addRetained key (.unsignedWord width) fresh)
      Reference (History × Unit) :=
    state.mapClassical (fun entry =>
      (entry.1.pushRetained key (.unsignedWord width) fresh, (entry.2, ())))
  have enteredEquation := Circuit.execute_retain state key (.unsignedWord width) fresh
  have bodyEquation := gcdLexical_execute
    (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh) Reference entered
  refine (Circuit.execute_seq (Circuit.retain ctx key (.unsignedWord width) fresh)
    body state).trans ?_
  refine (congrArg
    (fun initial : State (ctx.addRetained key (.unsignedWord width) fresh)
        Reference (History × Unit) =>
      (body.execute Reference initial).mapHistory
        (fun history => (history.1.1, (history.1.2, history.2)))) enteredEquation).trans ?_
  refine (congrArg
    (fun final : State (ctx.addRetained key (.unsignedWord width) fresh)
        Reference ((History × Unit) × body.Path) =>
      final.mapHistory (fun history => (history.1.1, (history.1.2, history.2))))
    bodyEquation).trans ?_
  simp only [State.mapHistory, entered,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def, retainedStep]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual fresh allocation supplies the zero used internally, and the result is total GCD. -/
theorem gcdRetained_read_result (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx) :
    ((retainedStep input key fresh store).1).read (retainedRead ctx width key fresh) =
      encodeWord (ClassicalAlgorithms.NumberTheory.GCD.eval
        (decodeOperands (store.read input))) := by
  have initialized : ((store.pushRetained key (.unsignedWord width) fresh).read
      (cellRead (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh))).toNat = 0 := rfl
  have actual := gcdLexical_read_result (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)
    (store.pushRetained key (.unsignedWord width) fresh) initialized
  exact actual.trans (congrArg
    (fun value => encodeWord (ClassicalAlgorithms.NumberTheory.GCD.eval
      (decodeOperands value)))
    (Store.read_pushRetained_underRetained store key (.unsignedWord width) fresh input))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
