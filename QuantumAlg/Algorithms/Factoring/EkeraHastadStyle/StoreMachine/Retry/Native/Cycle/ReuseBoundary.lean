/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Boundary
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Seed

/-!
# Physical restart after every actual reused native batch

A positive actual repetition establishes its output seed from every incoming
state: its first round resets and reloads the bank, and the remaining rounds
preserve that seed. Fresh sampling and the actual classical recovery keep this
statement valid for the complete reused batch, with all service/history/path
records retained. No admission predicate is used in physical cleanup.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma positiveRepetition_seedBlocks {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ) (count : Nat)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks m ell width
      (RuntimeRepetition.shortDLP_runtimeRepetition_wires m ell width ctx sameWires
        (count + 1)) N
      ((RuntimeRepetition.code m ell width N generator target ctx sameWires parameter
        cells (count + 1)).execute environment Reference state) := by
  let next := RuntimeResults.next m ell width ctx
  let nextWires :=
    (RuntimeResults.shortDLP_runtimeResult_next_wires m ell width ctx).trans sameWires
  let nextParameter := parameter.underRetained ctx.canonicalFreshKey
    (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
  let nextCells := fun index => (cells index).underRetained ctx.canonicalFreshKey
    (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
  let retention := Circuit.retain (model := RuntimeRound.model) ctx ctx.canonicalFreshKey
    (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
  let round := RuntimeRound.code m ell width nextWires nextParameter N generator target
    nextCells (RuntimeResults.head m ell width ctx)
  let tail := RuntimeRepetition.code m ell width N generator target next nextWires
    nextParameter nextCells count
  let retained := retention.execute environment Reference state
  let rounded := round.execute environment Reference retained
  have roundSeed := RuntimeRound.shortDLP_runtimeRound_seedBlocks (environment := environment)
    m ell width nextWires
    nextParameter N generator target nextCells (RuntimeResults.head m ell width ctx) retained
  have tailSeed := RuntimeRepetition.shortDLP_runtimeRepetition_seedBlocks (environment :=
    environment)
    m ell width N generator target count next nextWires nextParameter nextCells
    rounded roundSeed
  have bodySeed := BasisSeeded.seq (environment := environment) round tail _ retained tailSeed
  exact BasisSeeded.seq (environment := environment) retention (.seq round tail) _ state bodySeed

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (cells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- Sixteen actual reused rounds establish the fixed seed even from an unseeded input. -/
lemma reuseSource_seedBlocks {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.nativeBatchReuse_context_wires base N sameWires) N
      ((NativeBatchReuse.code base N sameWires cells).execute environment Reference state) := by
  have repeated := positiveRepetition_seedBlocks (environment := environment)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N)) 15
    (NativeBatchReuse.sampledContext base N)
    (NativeBatchReuse.nativeBatchReuse_sampled_wires base N sameWires)
    (NativeBatchReuse.parameter base N) (NativeBatchReuse.cells base N cells)
    ((ShorStyle.Canonical.Sampler.Retained.circuit (model := RuntimeRound.model) base N).execute
      environment
      Reference state)
  exact BasisSeeded.seq (environment := environment)
    (ShorStyle.Canonical.Sampler.Retained.circuit (model := RuntimeRound.model) base N)
    (NativeBatchReuse.rounds base N sameWires cells)
    ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.nativeBatchReuse_context_wires base N sameWires)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state repeated

/-- Actual recovery retains unconditional seed support in every complete output block. -/
lemma reuseBatch_seedBlocks (specification : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuseRecovery.seedWires base sameWires) N
      ((NativeBatchReuseRecovery.code base sameWires cells specification).execute environment
        Reference state) := by
  have source := reuseSource_seedBlocks (environment := environment) base sameWires cells state
  exact BasisSeeded.seq (environment := environment) (NativeBatchReuse.code base N sameWires cells)
    (NativeBatchReuseRecovery.tail base specification)
    ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuseRecovery.seedWires base sameWires)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state
    (NativeBatchReuseRecovery.tail_seedBlocks base sameWires specification _ source)

/-- Every actual reused source path contains a measured reset of the nonempty bank. -/
lemma reuseSource_measured
    (path : (NativeBatchReuse.code base N sameWires cells).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := RuntimeRound.model) dimension ∈
      (NativeBatchReuse.code base N sameWires cells).eventTrace path := by
  unfold NativeBatchReuse.code at path ⊢
  have positive : 0 < shortLogBits N + 2 * tradeoffBits N + 2 * arithmeticBits N := by
    unfold shortLogBits
    omega
  obtain ⟨dimension, present⟩ := repetition_measured
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (NativeBatchReuse.sampledContext base N)
    (NativeBatchReuse.nativeBatchReuse_sampled_wires base N sameWires)
    (NativeBatchReuse.parameter base N) (NativeBatchReuse.cells base N cells) 15
    positive path.2
  exact ⟨dimension, List.mem_append.mpr (Or.inr present)⟩

/-- Actual classical recovery preserves the reset measurement in every complete trace. -/
lemma reuseBatch_measured (specification : Input N)
    (path : (NativeBatchReuseRecovery.code base sameWires cells specification).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := RuntimeRound.model) dimension ∈
      (NativeBatchReuseRecovery.code base sameWires cells specification).eventTrace path := by
  unfold NativeBatchReuseRecovery.code at path ⊢
  obtain ⟨dimension, present⟩ := reuseSource_measured base sameWires cells path.1
  exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩

attribute [local irreducible] NativeBatchReuseRecovery.code

/-- A complete actual reused batch is physically restartable for every input and record. -/
lemma reuseBatch_restartCleanup (specification : Input N)
    (noBorrowed : base.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (environment := environment)
      (NativeBatchReuseRecovery.code base sameWires cells specification) where
  measured := reuseBatch_measured base sameWires cells specification
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment)
      (model := RuntimeRound.model) (pre := base)
      (post := NativeBatchReuseRecovery.context base N)
      (NativeBatchReuseRecovery.code base sameWires cells specification)
      noBorrowed Reference (History := History) state
  reinitialized := by
    let seed := (RuntimePlacement.basisEquiv
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuseRecovery.seedWires base sameWires)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    refine ⟨(NativeBatchReuseRecovery.context base N).quantumLayout.restrictSelectedBasis
      (NativeBatchReuseRecovery.context base N).borrowedSelectionᶜ seed, ?_⟩
    intro Reference History _ state label
    exact RuntimeRound.selectedSeed_promise seed _
      (reuseBatch_seedBlocks base sameWires cells specification state) label
      (NativeBatchReuseRecovery.context base N).borrowedSelectionᶜ

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles
