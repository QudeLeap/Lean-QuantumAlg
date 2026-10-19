/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.LexicalSemantics
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Retained.Composition

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

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual retained allocation followed by the exact lexical store transformation. -/
def retainedStep (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx) :
    Store (retainedCtx ctx width key fresh) × (retainedCircuit (model := model) input key
      fresh).Path :=
  let final := lexicalStep (model := model) (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)
    (store.pushRetained key (.unsignedWord width) fresh)
  (final.1, ((), final.2))

/-- Every complete block undergoes the actual store and path update of the retained circuit. -/
lemma gcdRetained_execute (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    {environment : model.Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (retainedCircuit (model := model) input key fresh).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := retainedStep (model := model) input key fresh entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  let body := lexicalBody (model := model) (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)
  let record := fun before : Store (ctx.addRetained key (.unsignedWord width) fresh) ×
      model.HiddenState =>
    let result := lexicalStep (model := model) (input.underRetained key (.unsignedWord width) fresh)
      (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh) before.1
    ((result.1, before.2), result.2)
  refine (Circuit.execute_retain_seq_mapClassical
    (environment := environment) ctx key (.unsignedWord width) fresh body record
    (fun reference history _ state => by
      exact (gcdLexical_execute (model := model)
        (input.underRetained key (.unsignedWord width) fresh)
        (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh) reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)) Reference state).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl)


/-- Actual fresh allocation supplies the zero used internally, and the result is total GCD. -/
lemma gcdRetained_read_result (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx) :
    ((retainedStep (model := model) input key fresh store).1).read (retainedRead ctx width key
      fresh) =
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
