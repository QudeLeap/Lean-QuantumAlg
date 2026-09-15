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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The genuine inner factor circuit has its complete store and path map on every CQ input. -/
theorem body_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (body source parameter phase output).execute Reference state =
      state.mapClassical (fun entry => ((bodyStep source parameter phase output entry.1).1,
        (entry.2, (bodyStep source parameter phase output entry.1).2))) := by
  refine (NativeFactorTail.code_execute source (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store (context ctx N) ×
        (History × (body source parameter phase output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((bodyStep source parameter phase output entry.1).1,
          (entry.2, (bodyStep source parameter phase output entry.1).2))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
