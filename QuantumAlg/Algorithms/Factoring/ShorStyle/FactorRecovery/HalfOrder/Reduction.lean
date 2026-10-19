/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Correctness
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Execution
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual half-order power followed by the scoped left-priority GCD suffix

The same two real circuits execute in sequence. Their actual path record
preserves complete quantum-reference blocks, and the result reads the power
cell that the first circuit actually wrote. Every half-factor comparison and
scratch condition is already discharged by its physical scope.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The real power and scoped factor paths, in their actual execution order. -/
def reduceStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (reduce (model := model) source cells output).Path :=
  let powered := NativeHalfPower.step (model := model) source (.storage cells.base.toCStorageRef)
    (orderRead cells) cells.halfPower store
  let factored := NativeHalfFactorScope.step (model := model) (halfRead cells) output powered.1
  (factored.1, (powered.2, factored.2))

/-- The single native execution has exactly the actual composed store and path record. -/
lemma reduce_execute (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (reduce (model := model) source cells output).execute environment Reference state =
      state.mapClassical (fun entry => ((reduceStep (model := model) source cells output entry.1).1,
        (entry.2.1, (entry.2.2, (reduceStep (model := model) source cells output entry.1).2)))) :=
            by
  unfold reduce
  rw [Circuit.execute_seq, NativeHalfFactorScope.code_execute, NativeHalfPower.code_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The true suffix returns the original selector of the same stored modular half-power. -/
lemma reduce_result (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (baseValue : ClassicalAlgorithms.Modular.Residue (modulusSpec source))
    (orderValue : ClassicalAlgorithms.Word (phaseBits N + 1))
    (baseRead : store.read (.storage cells.base.toCStorageRef) =
      .canonicalResidue baseValue.toWord)
    (orderValueRead : store.read (orderRead cells) = .unsignedWord orderValue) :
    (reduceStep (model := model) source cells output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N)
        (factorFromHalfPowerValue N (baseValue.val ^ (orderValue.val / 2) % N)) := by
  let powered := NativeHalfPower.step (model := model) source (.storage cells.base.toCStorageRef)
    (orderRead cells) cells.halfPower store
  exact (NativeHalfFactorScope.result (model := model) source (halfRead cells) output
      powered.1).trans
    (congrArg (fun value => encodeOutput (N := N) (factorFromHalfPowerValue N value))
      (NativeHalfPower.result_toNat source (.storage cells.base.toCStorageRef)
        (orderRead cells) cells.halfPower store baseValue orderValue baseRead orderValueRead))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
