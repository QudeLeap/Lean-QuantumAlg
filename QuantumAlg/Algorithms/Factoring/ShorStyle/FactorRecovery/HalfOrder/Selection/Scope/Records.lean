/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics
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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Record the actual second constant load and following stored-value factor computation. -/
def modulusTailStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) : Store (context ctx N) ×
      (Circuit.seq (ConstantWord.circuit (modulusRef ctx N) N)
        (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output))).Path :=
  let loaded := modulusStep store
  let selected := NativeHalfFactor.step (liftInput halfPower) (cells ctx N)
    (liftWrite output) loaded.1
  (selected.1, (loaded.2, selected.2))

/-- The real first constant load precedes the same modulus-load and factor-selection records. -/
def bodyStep (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) : Store (context ctx N) × (body halfPower output).Path :=
  let loaded := oneStep store
  let selected := modulusTailStep halfPower output loaded.1
  (selected.1, (loaded.2, selected.2))

/-- The actual lexical record releases all six real scratch entries after its result is written. -/
def step (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code halfPower output).Path :=
  let selected := bodyStep halfPower output (enter N store)
  (leave N selected.1, selected.2)

private theorem body_store (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) :
    (bodyStep halfPower output store).1 =
      (NativeHalfFactor.step (liftInput halfPower) (cells ctx N) (liftWrite output)
        (initialized store)).1 := by
  dsimp only [bodyStep, modulusTailStep, initialized]

/-- The real initialized body has the original source result without an input separation premise. -/
theorem body_result (source : Input N)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store (context ctx N)) :
    (bodyStep halfPower output store).1.read (.storage (liftWrite output).toCStorageRef) =
      encodeOutput (N := N)
        (factorFromHalfPowerValue N (store.read (liftInput halfPower)).toNat) := by
  have oneValue : ((initialized store).read (cells ctx N).one).toNat = 1 :=
    initialized_one store
  have modulusValue : ((initialized store).read (cells ctx N).modulus).toNat = N :=
    initialized_modulus source store
  have selected := NativeHalfFactor.result source (liftInput halfPower) (cells ctx N)
    (liftWrite output) (initialized store) (cells_separated ctx N halfPower) oneValue modulusValue
  refine (congrArg (fun final : Store (context ctx N) =>
    final.read (.storage (liftWrite output).toCStorageRef))
      (body_store halfPower output store)).trans (selected.trans ?_)
  exact congrArg (fun value => encodeOutput (N := N) (factorFromHalfPowerValue N value.toNat))
    (initialized_read_original halfPower store)

/-- Actual scope exit returns the source factor of the same original stored half-power. -/
theorem result (source : Input N)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (step halfPower output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N) (factorFromHalfPowerValue N (store.read halfPower).toNat) :=
  (leave_read (.storage output.toCStorageRef)
    (bodyStep halfPower output (enter N store)).1).trans
    ((body_result source halfPower output (enter N store)).trans
      (congrArg (fun value => encodeOutput (N := N) (factorFromHalfPowerValue N value.toNat))
        (enter_read halfPower store)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
