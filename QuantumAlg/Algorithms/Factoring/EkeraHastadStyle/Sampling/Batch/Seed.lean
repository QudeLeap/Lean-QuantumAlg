/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Preparation.Semantics
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.MeasurementCellsSeed

/-!
# The actual first shared-generator batch establishes and restores its bank seed

The real residue sampler runs before the single owned preparation. Actual
finite-cell allocation preserves that seed, and the actual sixteen-round
program reestablishes it in every complete final store-reference block.
The input may have arbitrary classical/reference correlations and mass.

This proof concerns the first internal allocation boundary. Subsequent
retries retain and reuse this same bank instead of preparing another one.
The statistical relation of the retained outcomes is proved separately from
this full-state restoration fact.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open ShortDLP.CompiledMAU
open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The actual sampler followed by one preparation establishes the complete seed blocks. -/
theorem nativeBatch_sampleAndPrepare_seedBlocks
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (RuntimeBank.shortDLP_runtimeBank_quantumWires (sampledContext base N)
        (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) N
      ((sampleAndPrepare base noQuantum N).execute Reference state) := by
  let sampler := ShorStyle.Canonical.Sampler.Retained.circuit base N
  let prepare := RuntimeBank.prepare (sampledContext base N)
    (nativeBatch_sampled_noQuantum base noQuantum N)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  exact RuntimeRepetition.seq_seed sampler prepare
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N _ state
    (RuntimeBank.shortDLP_runtimePrepare_seedBlocks (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N (sampler.execute Reference state))

/-- Actual initialization leaves the prepared seed beneath every real shared measurement cell. -/
theorem nativeBatch_initializeBank_seedBlocks
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatch_ready_wires base noQuantum N) N
      ((initializeBank base noQuantum N).execute Reference state) := by
  exact RuntimeRepetition.seq_seed (sampleAndPrepare base noQuantum N)
    (MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (nativeBatch_ready_wires base noQuantum N) state
    (RuntimeRound.shortDLP_runtimeMeasurementCells_seedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N _ 2 (measurementBits N)
      ((sampleAndPrepare base noQuantum N).execute Reference state)
      (nativeBatch_sampleAndPrepare_seedBlocks base noQuantum N state))

/-- The actual complete sixteen-round batch retains the exact source seed on its one bank. -/
theorem nativeBatch_complete_seedBlocks
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatch_context_wires base noQuantum N) N
      ((code base noQuantum N).execute Reference state) := by
  have initialized := nativeBatch_initializeBank_seedBlocks base noQuantum N state
  have repeated := RuntimeRepetition.shortDLP_runtimeRepetition_seedBlocks
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N)) 16
    (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
    (parameter base noQuantum N) (cells base noQuantum N)
    ((initializeBank base noQuantum N).execute Reference state) initialized
  exact RuntimeRepetition.seq_seed (initializeBank base noQuantum N) (rounds base noQuantum N)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (nativeBatch_context_wires base noQuantum N) state repeated

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
