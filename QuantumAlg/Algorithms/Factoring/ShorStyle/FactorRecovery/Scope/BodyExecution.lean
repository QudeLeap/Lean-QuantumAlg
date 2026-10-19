/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Records
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete CQ execution of the actual factor-scope body

The existing tail execution law is instantiated at the real seven-head
context. Its actual path dictionary is aligned explicitly; no inner store,
quantum block, reference state or runtime condition is reconstructed.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The genuine inner factor circuit has its complete store and path map on every CQ input. -/
lemma body_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (body (model := model) source parameter phase output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := bodyStep (model := model) source parameter phase output entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (NativeFactorTail.code_execute (model := model) source
    (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
