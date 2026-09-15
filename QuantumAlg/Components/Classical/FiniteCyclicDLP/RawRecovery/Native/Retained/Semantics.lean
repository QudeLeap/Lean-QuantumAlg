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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual result retention and complete recovery have the exact original optional output. -/
theorem retainedCircuit_actualRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx →
        Store (retainedCtx ctx width key fresh) × (retainedCircuit spec input key fresh).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (retainedCircuit spec input key fresh).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        (before.pushRetained key (OutputShape width) fresh).write
          (CWriteRef.retainedHead ctx key (OutputShape width) fresh)
          (encodedRawOutput spec
            (RawRecovery.outputOf spec (preparationInput (before.read input)))) := by
  let lifted := input.underRetained key (OutputShape width) fresh
  let output := CWriteRef.retainedHead ctx key (OutputShape width) fresh
  obtain ⟨bodyRecord, bodyEquation, bodyCorrect⟩ := singleIntoResult_actualRecord spec lifted output
  let record (before : Store ctx) :=
    let final := bodyRecord (before.pushRetained key (OutputShape width) fresh)
    (final.1, ((), final.2))
  refine ⟨record, ?_, ?_⟩
  · intro reference history historyFinite state
    refine (Circuit.execute_retain_seq_mapClassical ctx key (OutputShape width) fresh
      (singleIntoResult spec lifted output) bodyRecord bodyEquation reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · intro before
    have actual := bodyCorrect (before.pushRetained key (OutputShape width) fresh)
    rw [show (before.pushRetained key (OutputShape width) fresh).read lifted =
      before.read input from Store.read_pushRetained_underRetained before key
        (OutputShape width) fresh input] at actual
    exact actual

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
