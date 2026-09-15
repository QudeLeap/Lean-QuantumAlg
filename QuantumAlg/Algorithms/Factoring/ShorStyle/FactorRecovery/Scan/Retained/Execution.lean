/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Context
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Scope.Store
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Scope.Execution
import all QuantumAlg.Core.Execution.Retained.Composition

/-!
# Actual native Shor recovery after the retained source batch

The real retained result allocation and the real complete scoped scan act on
the existing sampled store. Their precise finite record maps each complete
quantum-reference block without replacing its quantum state or its actual
classical history. The original source tuple cells remain the scan inputs.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual result allocation precedes the actual complete recovery scope record. -/
def recoveryStep {N : Nat} (source : Input N) (count : Nat)
    (store : Store (sampledContext N count)) :
    Store (post N count) × (recoveryStage source count).Path :=
  let actual := NativeFactorScan.Scope.step source (visitInputs N count) (resultRef N count)
    (store.pushRetained (resultKey N count) (outputShape N) (resultFresh N count))
  (actual.1, ((), actual.2))

/-- The same actual tail maps every full input block through its true store and path update. -/
theorem recoveryStage_execute {N : Nat} (source : Input N) (count : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (sampledContext N count) Reference History) :
    (recoveryStage source count).execute Reference state =
      state.mapClassical (fun entry => ((recoveryStep source count entry.1).1,
        (entry.2, (recoveryStep source count entry.1).2))) := by
  refine (Circuit.execute_retain_seq_mapClassical (sampledContext N count)
    (resultKey N count) (outputShape N) (resultFresh N count) (recoveryCode source count)
    (NativeFactorScan.Scope.step source (visitInputs N count) (resultRef N count))
    (NativeFactorScan.Scope.code_execute source (visitInputs N count) (resultRef N count))
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq
        (Store (post N count) × (History × (recoveryStage source count).Path)) =>
      @ExecutionState.mapClassical _ _ _ _
        (Register.prod (sampledContext N count).register Reference) decision state
        (fun entry => ((recoveryStep source count entry.1).1,
          (entry.2, (recoveryStep source count entry.1).2)))) (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
