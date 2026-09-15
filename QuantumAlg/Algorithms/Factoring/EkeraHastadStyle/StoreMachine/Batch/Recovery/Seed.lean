/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Record
import all QuantumAlg.Core.Execution.Borrowed

/-!
# The first recovered batch leaves its owned bank seeded in every actual store

Actual sampling, the sole owned preparation and sixteen rounds establish
complete store-reference seed blocks. The proved classical recovery record
preserves those blocks through its real retained output and full workspace
allocation. This internal fact supplies the next batch without a caller
initialization premise. The physical borrowed-wire list is empty because
all incoming quantum storage was absent and the new bank was owned.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

noncomputable section

open Execution ShortDLP.CompiledMAU

attribute [local irreducible] NativeBatch.context NativeBatch.code

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The completed recovery context still uses exactly the originally prepared ordered bank. -/
theorem seedWires (N : Nat) :
    (context base noQuantum N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (context_quantumWires base noQuantum N).trans
    (NativeBatch.nativeBatch_context_wires base noQuantum N)

/-- Actual classical allocation and recovery preserve every complete source seed block. -/
theorem tail_seedBlocks (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (NativeBatch.context base noQuantum N) Reference History)
    (seeded : RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatch.nativeBatch_context_wires base noQuantum N) N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (seedWires base noQuantum N) N
      ((tail base noQuantum input).execute Reference state) :=
  RuntimeRound.shortDLP_runtimeRetainedRecord_seedBlocks
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (NativeBatch.nativeBatch_context_wires base noQuantum N)
    (tail base noQuantum input) (step base noQuantum input)
    (tail_execute base noQuantum input) state seeded

/-- The actual first recovered batch establishes the seed without an incoming seed premise. -/
theorem code_seedBlocks (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (seedWires base noQuantum N) N ((code base noQuantum input).execute Reference state) := by
  have source := NativeBatch.nativeBatch_complete_seedBlocks base noQuantum N state
  exact RuntimeRepetition.seq_seed (NativeBatch.code base noQuantum N) (tail base noQuantum input)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N (seedWires base noQuantum N) state
    (tail_seedBlocks base noQuantum input _ source)

/-- The first owned bank contributes no borrowed quantum wire to the subsequent retry context. -/
theorem context_noBorrowedQuantum (N : Nat) :
    (context base noQuantum N).borrowedQuantumWires = [] := by
  have empty : base.borrowedQuantumWires = [] := by
    have subset := base.borrowedQuantumWires_sublist
    rw [noQuantum] at subset
    exact List.sublist_nil.mp subset
  exact (RuntimeCtx.borrowedQuantumWires_addRetained (NativeBatch.context base noQuantum N)
    (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh).trans
      ((NativeBatch.code base noQuantum N).borrowedQuantumWires_preserved.trans empty)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
