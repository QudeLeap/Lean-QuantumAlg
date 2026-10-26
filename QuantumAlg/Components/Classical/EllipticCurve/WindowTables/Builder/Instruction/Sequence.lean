/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction

/-!
# Actual chronological sequences of table-row instructions

The complete native row record feeds each actual returned Store and service
state to the next slot. Its Store projection is exactly the total finite-word
update sequence; all original histories and quantum-reference blocks remain.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.RowInstruction

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Chronological finite-word interpretation of the original indexed slots. -/
def updates (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) :
    (count : Nat) → (Fin count → RowInstruction ctx width length) → Store ctx → Store ctx
  | 0, _instructions, store => store
  | count + 1, instructions, store =>
      updates spec modulus count (fun index => instructions index.succ)
        ((instructions 0).update spec modulus store)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The original indexed circuits retain each actual predecessor's result and service state. -/
def rangeRecord (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment)
    (count : Nat) (instructions : Fin count → RowInstruction ctx width length) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (Circuit.forRange count (fun index =>
        (instructions index).circuit (model := model) spec modulus)).Path :=
  Circuit.forRangeRecord count (fun index => (instructions index).circuit spec modulus)
    (fun index => (instructions index).record spec modulus environment)

/-- No free field operation is substituted: these are exactly the actual slots' Store updates. -/
lemma rangeRecord_store (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment)
    (count : Nat) (instructions : Fin count → RowInstruction ctx width length)
    (before : Store ctx × model.HiddenState) :
    (rangeRecord spec modulus environment count instructions before).1.1 =
      updates spec modulus count instructions before.1 := by
  induction count generalizing before with
  | zero => rfl
  | succ count ih =>
      change (rangeRecord spec modulus environment count (fun index => instructions index.succ)
        ((instructions 0).record spec modulus environment before).1).1.1 = _
      rw [ih, record_store]
      rfl

/-- Full actual execution of the original slots preserves arbitrary incoming quantum references. -/
lemma range_execute (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment)
    (count : Nat) (instructions : Fin count → RowInstruction ctx width length)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.forRange count (fun index =>
      (instructions index).circuit (model := model) spec modulus)).execute environment Reference
      state = state.mapClassical (fun entry =>
        let result := rangeRecord spec modulus environment count instructions (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord count (fun index => (instructions index).circuit spec modulus)
    environment (fun index => (instructions index).record spec modulus environment)
    (fun index => (instructions index).circuit_execute spec modulus environment) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.RowInstruction
