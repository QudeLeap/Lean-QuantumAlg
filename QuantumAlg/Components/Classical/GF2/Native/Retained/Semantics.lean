/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Retained
import all QuantumAlg.Components.Classical.GF2.Native.State.Semantics
import all QuantumAlg.Core.Execution.Retained.Composition

/-!
# Complete actual state of retained GF(2) recovery

The real retained allocation and the real seven-cell recovery share one
complete actual record. Its final context includes the actual optional
output cell. No pure recovery function, initial caller workspace values,
success premise or alternative interpreter is used in this equation.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- Actual result retention and all original recovery scopes preserve the full state record. -/
theorem gf2Retained_actualRecord (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx × model.HiddenState →
        (Store (retainedCtx ctx width key fresh) × model.HiddenState) ×
          (retainedCircuit input key fresh).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (retainedCircuit (model := model) input key fresh).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  let lifted := input.underRetained key (.option (.unsignedWord width)) fresh
  let output := CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh
  obtain ⟨bodyRecord, bodyEquation⟩ := gf2WithState_actualRecord lifted output
  let record (before : Store ctx × model.HiddenState) :=
    let final := bodyRecord
      (before.1.pushRetained key (.option (.unsignedWord width)) fresh, before.2)
    (final.1, ((), final.2))
  refine ⟨record, ?_⟩
  intro reference history historyFinite state
  refine (Circuit.execute_retain_seq_mapClassical (model := model) ctx key
    (.option (.unsignedWord width)) fresh
    (withState lifted output) bodyRecord bodyEquation reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.GF2.Native
