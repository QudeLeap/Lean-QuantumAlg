/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Depth

/-!
# Actual event and depth bounds through the complete seven-cell factor scope

The genuine lexical allocations enter and release the seven cells around the
same stored-input factor tail. Their trace contains exactly the native events
and serial dependencies of that tail. Their simultaneous live capacities are
proved separately and are never represented as omitted classical operations.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- All actual order, power, GCD and output events survive placement under the real scope. -/
theorem code_pool_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source parameter phase output).Path) :
    (code (model := model) source parameter phase output).resourcePool path ≤
      NativeFactorTail.eventEnvelope model N :=
  NativeFactorTail.code_pool_le (model := model) source (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output) path

/-- Every actual serial dependency remains counted beneath the same real lexical allocations. -/
theorem code_unitDepth_le (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code (model := model) source parameter phase output).Path) :
    (code (model := model) source parameter phase output).depth (fun _ => 1) path ≤
      NativeFactorTail.depthBound N :=
  NativeFactorTail.code_unitDepth_le (model := model) source (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output) path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope
