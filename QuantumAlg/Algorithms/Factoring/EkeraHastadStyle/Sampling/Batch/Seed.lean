/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Preparation.Semantics
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.MeasurementCellsSeed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

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

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open ShortDLP.CompiledMAU
open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The actual sampler followed by one preparation establishes the complete seed blocks. -/
lemma nativeBatch_sampleAndPrepare_seedBlocks
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (RuntimeBank.shortDLP_runtimeBank_quantumWires (sampledContext base N)
        (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) N
      ((sampleAndPrepare base noQuantum N).execute environment Reference state) := by
  let sampler := ShorStyle.Canonical.Sampler.Retained.circuit
    (model := RuntimeRound.model) base N
  let prepare := RuntimeBank.prepare (operations := BitWord.model) (services := .empty)
    (sampledContext base N)
    (nativeBatch_sampled_noQuantum base noQuantum N)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  exact BasisSeeded.seq (environment := environment) sampler prepare
    ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (RuntimeBank.shortDLP_runtimeBank_quantumWires (sampledContext base N)
        (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N))).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state
    (RuntimeBank.shortDLP_runtimePrepare_seedBlocks (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N (sampler.execute
        environment Reference state))

/-- Actual initialization leaves the prepared seed beneath every real shared measurement cell. -/
lemma nativeBatch_initializeBank_seedBlocks
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatch_ready_wires base noQuantum N) N
      ((initializeBank base noQuantum N).execute environment Reference state) := by
  exact BasisSeeded.seq (environment := environment) (sampleAndPrepare base noQuantum N)
    (MeasurementCells.allocate (model := RuntimeRound.model)
      (bankContext base noQuantum N) 2 (measurementBits N))
    ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatch_ready_wires base noQuantum N)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state
    (RuntimeRound.shortDLP_runtimeMeasurementCells_seedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N _ 2 (measurementBits N)
      ((sampleAndPrepare base noQuantum N).execute environment Reference state)
      (nativeBatch_sampleAndPrepare_seedBlocks base noQuantum N state))

/-- The actual complete sixteen-round batch retains the exact source seed on its one bank. -/
lemma nativeBatch_complete_seedBlocks
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatch_context_wires base noQuantum N) N
      ((code base noQuantum N).execute environment Reference state) := by
  have initialized := nativeBatch_initializeBank_seedBlocks (environment := environment)
    base noQuantum N state
  have repeated := RuntimeRepetition.shortDLP_runtimeRepetition_seedBlocks (environment :=
    environment)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N)) 16
    (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
    (parameter base noQuantum N) (cells base noQuantum N)
    ((initializeBank base noQuantum N).execute environment Reference state) initialized
  exact BasisSeeded.seq (environment := environment)
    (initializeBank base noQuantum N) (rounds base noQuantum N)
    ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatch_context_wires base noQuantum N)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state repeated

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
