/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Framing

/-!
# Actual complete batch record including the true empty branch

An empty batch is the original identity circuit with its unique actual
path and unchanged Store/service state. Every nonempty batch uses exactly
the already proved initializer, forward traversal, paid XGCD and reverse
record. The conditional changes no instruction or execution contract.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : BatchFrame ctx width length)

/-- Actual record of the original conditional batch, including its literal identity branch. -/
def valueRecord (spec : ModulusSpec width) :
    (count : Nat) → (fits : count < length) → (environment : model.Environment) →
      Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (frame.circuit (model := model) spec count fits).Path
  | 0, _, _ => fun before => (before, ())
  | count + 1, fits, environment =>
      frame.nonemptyValueRecord (environment := environment) spec (count + 1) fits

/-- The original zero-row batch returns exactly its original real Store and service state. -/
lemma valueRecord_zero_state (spec : ModulusSpec width) (fits : 0 < length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.valueRecord spec 0 fits environment before).1 = before := rfl

/-- The nonempty record's returned state is exactly that of the already proved complete branch. -/
lemma valueRecord_nonempty_state (spec : ModulusSpec width) (count : Nat) (fits : count < length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (nonempty : count ≠ 0) :
    (frame.valueRecord spec count fits environment before).1 =
      (frame.nonemptyValueRecord (environment := environment) spec count fits before).1 := by
  cases count with
  | zero => contradiction
  | succ count => rfl

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The entire original conditional batch retains every incoming history and Reference block. -/
lemma circuit_execute (spec : ModulusSpec width) (count : Nat) (fits : count < length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.circuit (model := model) spec count fits).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.valueRecord spec count fits environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  cases count with
  | zero =>
      exact (Circuit.execute_id environment state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | succ count => exact frame.nonemptyCircuit_execute spec (count + 1) fits Reference state

/-- Both actual branches retain every structural caller read outside the five real batch outputs. -/
lemma valueRecord_read_other (spec : ModulusSpec width) (environment : model.Environment)
    (count : Nat) (fits : count < length) {shape : CShape} (observed : CInputRef ctx shape)
    (prefixFree : frame.prefixes.key ∉ observed.storageKeys)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (denominatorFree : frame.denominators.key ∉ observed.storageKeys)
    (inverseFree : frame.work.inverse.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.valueRecord spec count fits environment before).1.1.read observed =
      before.1.read observed := by
  by_cases empty : count = 0
  · subst count
    rw [frame.valueRecord_zero_state]
  · rw [frame.valueRecord_nonempty_state spec count fits environment before empty]
    exact frame.nonemptyValueRecord_read_other spec environment count fits observed
      prefixFree productFree denominatorFree inverseFree temporaryFree before

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
