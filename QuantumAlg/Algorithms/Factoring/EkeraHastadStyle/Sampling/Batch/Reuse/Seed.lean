/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Endpoint
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant

/-!
# Fresh retained sampling preserves the same existing short-DLP bank

The actual uniform source and its complete parameter computation change
classical storage only. Every complete store-reference block retains its
already established bank seed. This supplies the internal induction step
between independent batches without another quantum preparation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- A fresh actual sampler preserves the existing bank in every complete store-reference block. -/
theorem nativeBatchReuse_sampler_seedBlocks {ctx : RuntimeCtx .quantum} {N : Nat}
    (input : Input N)
    (sameWires : ctx.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      ((ShorStyle.Canonical.Sampler.Retained.samplerNative_quantumWires ctx N).trans sameWires) N
      ((ShorStyle.Canonical.Sampler.Retained.circuit
        (model := RuntimeRound.model) ctx N).execute Reference state) :=
  ShorStyle.Canonical.Sampler.Retained.samplerRetained_seeded
    (model := RuntimeRound.model) input.samplerInput _ state seeded

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse
