/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics
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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The real power and scoped factor paths, in their actual execution order. -/
def reduceStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (reduce source cells output).Path :=
  let powered := NativeHalfPower.step source (.storage cells.base.toCStorageRef)
    (orderRead cells) cells.halfPower store
  let factored := NativeHalfFactorScope.step (halfRead cells) output powered.1
  (factored.1, (powered.2, factored.2))

/-- The single native execution has exactly the actual composed store and path record. -/
theorem reduce_execute (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (reduce source cells output).execute Reference state =
      state.mapClassical (fun entry => ((reduceStep source cells output entry.1).1,
        (entry.2, (reduceStep source cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (NativeHalfPower.code source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower)
    (NativeHalfFactorScope.code (halfRead cells) output)
    (NativeHalfPower.step source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower)
    (NativeHalfFactorScope.step (halfRead cells) output)
    (NativeHalfPower.code_execute source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower)
    (NativeHalfFactorScope.code_execute (halfRead cells) output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (reduce source cells output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((reduceStep source cells output entry.1).1,
          (entry.2, (reduceStep source cells output entry.1).2))))
    (Subsingleton.elim _ _)

/-- The true suffix returns the original selector of the same stored modular half-power. -/
theorem reduce_result (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (baseValue : ClassicalAlgorithms.Modular.Residue (modulusSpec source))
    (orderValue : ClassicalAlgorithms.Word (phaseBits N + 1))
    (baseRead : store.read (.storage cells.base.toCStorageRef) =
      .canonicalResidue baseValue.toWord)
    (orderValueRead : store.read (orderRead cells) = .unsignedWord orderValue) :
    (reduceStep source cells output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N)
        (factorFromHalfPowerValue N (baseValue.val ^ (orderValue.val / 2) % N)) := by
  let powered := NativeHalfPower.step source (.storage cells.base.toCStorageRef)
    (orderRead cells) cells.halfPower store
  exact (NativeHalfFactorScope.result source (halfRead cells) output powered.1).trans
    (congrArg (fun value => encodeOutput (N := N) (factorFromHalfPowerValue N value))
      (NativeHalfPower.result_toNat source (.storage cells.base.toCStorageRef)
        (orderRead cells) cells.halfPower store baseValue orderValue baseRead orderValueRead))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
