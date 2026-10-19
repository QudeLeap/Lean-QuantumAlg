/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program

/-!
# Store projection of the actual scoped residue program

The projection exposes precisely the declared push, inner update and pop.
Subsequent read and frame laws can apply this equation without unfolding
the inner instruction path or the representation of a complete store.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open Execution

/-- The actual program's final store is the declared release of its actual inner store. -/
lemma samplerProgram_store_projection {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (store : Store ctx) :
    (step (model := model) N sample output store).1 =
      Layout.popStore (modulusBits N)
        (innerStep (model := model)
          N sample output (Layout.pushStore (modulusBits N) store)).1 := rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
