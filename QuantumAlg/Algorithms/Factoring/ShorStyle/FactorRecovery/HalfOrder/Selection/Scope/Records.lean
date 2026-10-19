/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Store
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Initialization
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Separation

/-!
# Actual scoped half-factor records and original source result

The record retains the two literal constant-load paths and the selected real
GCD path. Its outer store is obtained by the actual six pushes and six pops.
The internal cell conditions are all discharged by this physical layout,
leaving only the original nontrivial-modulus source condition.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- Record the actual second constant load and following stored-value factor computation. -/
def modulusTailStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) : Store (context ctx N) ×
      (Circuit.seq (ConstantWord.circuit (model := model) (modulusRef ctx N) N)
        (NativeHalfFactor.code (model := model) (liftInput halfPower) (cells ctx N) (liftWrite
            output))).Path :=
  let loaded := modulusStep (model := model) store
  let selected := NativeHalfFactor.step (model := model) (liftInput halfPower) (cells ctx N)
    (liftWrite output) loaded.1
  (selected.1, (loaded.2, selected.2))

/-- The real first constant load precedes the same modulus-load and factor-selection records. -/
def bodyStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) : Store (context ctx N) × (body (model := model) halfPower
        output).Path :=
  let loaded := oneStep (model := model) store
  let selected := modulusTailStep (model := model) halfPower output loaded.1
  (selected.1, (loaded.2, selected.2))

/-- The actual lexical record releases all six real scratch entries after its result is written. -/
def step (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code (model := model) halfPower output).Path :=
  let selected := bodyStep (model := model) halfPower output (enter N store)
  (leave N selected.1, selected.2)

private lemma body_store (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) :
    (bodyStep (model := model) halfPower output store).1 =
      (NativeHalfFactor.step (model := model) (liftInput halfPower) (cells ctx N) (liftWrite output)
        (initialized (model := model) store)).1 := by
  dsimp only [bodyStep, modulusTailStep, initialized]

/-- The real initialized body has the original source result without an input separation premise. -/
lemma body_result (source : Input N)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) :
    (bodyStep (model := model) halfPower output store).1.read (.storage (liftWrite
        output).toCStorageRef) =
      encodeOutput (N := N)
        (factorFromHalfPowerValue N (store.read (liftInput halfPower)).toNat) := by
  have oneValue : ((initialized (model := model) store).read (cells ctx N).one).toNat = 1 :=
    initialized_one (model := model) store
  have modulusValue : ((initialized (model := model) store).read (cells ctx N).modulus).toNat = N :=
    initialized_modulus (model := model) source store
  have selected := NativeHalfFactor.result (model := model) source (liftInput halfPower) (cells
      ctx N)
    (liftWrite output) (initialized (model := model) store) (cells_separated ctx N halfPower)
        oneValue modulusValue
  refine (congrArg (fun final : Store (context ctx N) =>
    final.read (.storage (liftWrite output).toCStorageRef))
      (body_store (model := model) halfPower output store)).trans (selected.trans ?_)
  exact congrArg (fun value => encodeOutput (N := N) (factorFromHalfPowerValue N value.toNat))
    (initialized_read_original (model := model) halfPower store)

/-- Actual scope exit returns the source factor of the same original stored half-power. -/
lemma result (source : Input N)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (step (model := model) halfPower output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N) (factorFromHalfPowerValue N (store.read halfPower).toNat) :=
  (leave_read (.storage output.toCStorageRef)
    (bodyStep (model := model) halfPower output (enter N store)).1).trans
    ((body_result (model := model) source halfPower output (enter N store)).trans
      (congrArg (fun value => encodeOutput (N := N) (factorFromHalfPowerValue N value.toNat))
        (enter_read halfPower store)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
