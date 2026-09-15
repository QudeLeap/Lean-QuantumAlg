/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed

/-!
# Actual fresh sampling and sixteen more rounds on the same bank

One new source draw and its complete parameter computation precede sixteen
actual member/measurement/packing/reset/reload rounds. The caller supplies
the existing bank and measurement cells. The code preserves and restores
the internal complete-store seed invariant needed for subsequent batches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse

noncomputable section

open Execution ShortDLP.CompiledMAU

variable (base : RuntimeCtx .quantum) (N : Nat)
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- The stored new parameter selects sixteen complete rounds on the existing physical bank. -/
def rounds : Circuit (sampledContext base N) (context base N) :=
  RuntimeRepetition.code (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (sampledContext base N) (nativeBatchReuse_sampled_wires base N sameWires)
    (parameter base N) (cells base N originalCells) 16

/-- Fresh actual sampling feeds the same bank, with no quantum allocation in this continuation. -/
def code : Circuit base (context base N) :=
  .seq (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    (rounds base N sameWires originalCells)

/-- Complete output lists the original bank and cells plus all newly retained source results. -/
def run : AlgorithmRun base (context base N) (NativeBatch.resultShape N) where
  code := code base N sameWires originalCells
  output := Output.all (context base N)
    (.read (.product (finalSample base N)
      (.product (finalParameter base N) (finalResults base N))))

/-- Every surviving original and new entry appears in the actual output manifest. -/
theorem nativeBatchReuse_output_listing :
    (run base N sameWires originalCells).output.listing = (context base N).keys := rfl

/-- The complete actual continuation restores the same seed in every complete store block. -/
theorem nativeBatchReuse_code_seedBlocks (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatchReuse_context_wires base N sameWires) N
      ((code base N sameWires originalCells).execute Reference state) := by
  have sampled := nativeBatchReuse_sampler_seedBlocks input sameWires state seeded
  have repeated := RuntimeRepetition.shortDLP_runtimeRepetition_seedBlocks
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N)) 16
    (sampledContext base N) (nativeBatchReuse_sampled_wires base N sameWires)
    (parameter base N) (cells base N originalCells)
    ((ShorStyle.Canonical.Sampler.Retained.circuit base N).execute Reference state) sampled
  exact RuntimeRepetition.seq_seed (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    (rounds base N sameWires originalCells) (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (nativeBatchReuse_context_wires base N sameWires) state repeated

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse
