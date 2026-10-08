/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Retained.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.State.Correctness

/-!
# Original recovery in the actual retained result

Real retention precedes the existing seven-cell program. Its same complete
record writes the original recovery into the fresh optional output while
preserving every caller cell and every quantum-reference correlation.
There is no caller workspace, initial-zero, or successful-recovery premise.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- Actual retention returns the original recovery and the same complete interpreter record. -/
theorem gf2Retained_actualRecord_correct
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx × model.HiddenState →
        (Store (retainedCtx ctx width key fresh) × model.HiddenState) ×
          (retainedCircuit input key fresh).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (retainedCircuit (model := model) input key fresh).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (record before).1.1 =
          (before.1.pushRetained key (.option (.unsignedWord width)) fresh).write
            (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)
            (gf2RecoveryValue (before.1.read input)) := by
  let lifted := input.underRetained key (.option (.unsignedWord width)) fresh
  let output := CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh
  obtain ⟨bodyRecord, bodyEquation, bodyCorrect⟩ :=
    gf2WithState_actualRecord_correct lifted output
  let record (before : Store ctx × model.HiddenState) :=
    let final := bodyRecord
      (before.1.pushRetained key (.option (.unsignedWord width)) fresh, before.2)
    (final.1, ((), final.2))
  refine ⟨record, ?_, ?_⟩
  · intro reference history historyFinite state
    refine (Circuit.execute_retain_seq_mapClassical (model := model) ctx key
      (.option (.unsignedWord width)) fresh
      (withState lifted output) bodyRecord bodyEquation reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · intro before
    have correct := bodyCorrect
      (before.1.pushRetained key (.option (.unsignedWord width)) fresh, before.2)
    simpa only [retainedCtx, record, lifted, output,
      Store.read_pushRetained_underRetained] using correct

end

end QuantumAlg.ClassicalRoutines.GF2.Native
