/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Cleanup
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Restart

/-!
# Actual physical boundary after the first recovered native batch

The first batch prepares its bank internally and executes sixteen complete
measured rounds. The actual classical recovery retains the full seed support.
Consequently its complete output meets physical restart for every incoming
state and every execution record. The independently certified batch protocol
and actual continuation admission remain separate obligations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma repetition_measured {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat) (positive : 0 < m + 2 * ell + 2 * width)
    (path : (RuntimeRepetition.code m ell width N generator target ctx sameWires
      parameter cells (count + 1)).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := RuntimeRound.model) dimension ∈
      (RuntimeRepetition.code m ell width N generator target ctx sameWires
        parameter cells (count + 1)).eventTrace path := by
  let nextWires :=
    (RuntimeResults.shortDLP_runtimeResult_next_wires m ell width ctx).trans sameWires
  let nextParameter := parameter.underRetained ctx.canonicalFreshKey
    (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
  let nextCells := fun index => (cells index).underRetained ctx.canonicalFreshKey
    (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
  simp only [RuntimeRepetition.code] at path ⊢
  obtain ⟨dimension, present⟩ := RuntimeRound.shortDLP_runtimeRound_measured
    m ell width nextWires nextParameter N generator target nextCells
    (RuntimeResults.head m ell width ctx) positive path.2.1
  exact ⟨dimension, List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl present)))⟩

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every first source batch path includes a real bank measurement. -/
lemma firstSource_measured (N : Nat)
    (path : (NativeBatch.code base noQuantum N).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := RuntimeRound.model) dimension ∈
      (NativeBatch.code base noQuantum N).eventTrace path := by
  unfold NativeBatch.code at path ⊢
  have positive : 0 < shortLogBits N + 2 * tradeoffBits N + 2 * arithmeticBits N := by
    unfold shortLogBits
    omega
  obtain ⟨dimension, present⟩ := repetition_measured
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (NativeBatch.readyContext base noQuantum N)
    (NativeBatch.nativeBatch_ready_wires base noQuantum N)
    (NativeBatch.parameter base noQuantum N) (NativeBatch.cells base noQuantum N) 15
    positive path.2
  exact ⟨dimension, List.mem_append.mpr (Or.inr present)⟩

/-- Classical recovery does not remove any actual source measurement from the batch trace. -/
lemma firstBatch_measured (specification : Input N)
    (path : (NativeBatchRecovery.code base noQuantum specification).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := RuntimeRound.model) dimension ∈
      (NativeBatchRecovery.code base noQuantum specification).eventTrace path := by
  unfold NativeBatchRecovery.code at path ⊢
  obtain ⟨dimension, present⟩ := firstSource_measured base noQuantum N path.1
  exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩

attribute [local irreducible] NativeBatchRecovery.code

/-- The first recovered batch is physically restartable for every caller state and path. -/
lemma firstBatch_restartCleanup (specification : Input N) :
    Circuit.RestartCleanup (environment := environment) (model := RuntimeRound.model) (pre := base)
      (post := NativeBatchRecovery.context base noQuantum N)
      (NativeBatchRecovery.code base noQuantum specification) where
  measured := firstBatch_measured base noQuantum specification
  restores := by
    intro Reference History _ state
    have none : base.borrowedQuantumWires = [] := by
      have included := base.borrowedQuantumWires_sublist
      rw [noQuantum] at included
      exact List.sublist_nil.mp included
    exact Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment)
      (model := RuntimeRound.model) (pre := base)
      (post := NativeBatchRecovery.context base noQuantum N)
      (NativeBatchRecovery.code base noQuantum specification)
      none Reference (History := History) state
  reinitialized := by
    let seed := (RuntimePlacement.basisEquiv
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchRecovery.seedWires base noQuantum N)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    refine ⟨(NativeBatchRecovery.context base noQuantum N).quantumLayout.restrictSelectedBasis
      (NativeBatchRecovery.context base noQuantum N).borrowedSelectionᶜ seed, ?_⟩
    intro Reference History _ state label
    exact RuntimeRound.selectedSeed_promise seed _
      (NativeBatchRecovery.code_seedBlocks base noQuantum specification state) label
      (NativeBatchRecovery.context base noQuantum N).borrowedSelectionᶜ

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles
