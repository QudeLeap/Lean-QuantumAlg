/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Retained
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Semantics
import all QuantumAlg.Core.Execution.Retained.Composition

/-!
# Complete actual retained raw recovery

The actual retained allocation and the actual complete single recovery share
one execution record. Their final store is precisely the initialized original
caller store with the original optional recovery result written to the new
retained cell. Every complete quantum-reference block and old history remains.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual result retention and complete recovery have the exact original optional output. -/
lemma retainedCircuit_actualRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx × model.HiddenState →
        (Store (retainedCtx ctx width key fresh) × model.HiddenState) × (retainedCircuit (model
          := model) spec input key fresh).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (retainedCircuit (model := model) spec input key fresh).execute
          environment Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        (before.1.pushRetained key (OutputShape width) fresh).write
          (CWriteRef.retainedHead ctx key (OutputShape width) fresh)
          (encodedRawOutput spec
            (RawRecovery.outputOf spec (preparationInput (before.1.read input)))) := by
  let lifted := input.underRetained key (OutputShape width) fresh
  let output := CWriteRef.retainedHead ctx key (OutputShape width) fresh
  obtain ⟨bodyRecord, bodyEquation, bodyCorrect⟩ := singleIntoResult_actualRecord (model :=
    model) spec lifted output
  let record (before : Store ctx × model.HiddenState) :=
    let final := bodyRecord (before.1.pushRetained key (OutputShape width) fresh, before.2)
    (final.1, ((), final.2))
  refine ⟨record, ?_, ?_⟩
  · intro reference history historyFinite state
    refine (Circuit.execute_retain_seq_mapClassical
      (environment := environment) ctx key (OutputShape width) fresh
      (singleIntoResult (model := model) spec lifted output) bodyRecord bodyEquation reference
        state).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  · intro before
    have actual := bodyCorrect (before.1.pushRetained key (OutputShape width) fresh, before.2)
    rw [show (before.1.pushRetained key (OutputShape width) fresh).read lifted =
      before.1.read input from Store.read_pushRetained_underRetained before.1 key
        (OutputShape width) fresh input] at actual
    exact actual

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
