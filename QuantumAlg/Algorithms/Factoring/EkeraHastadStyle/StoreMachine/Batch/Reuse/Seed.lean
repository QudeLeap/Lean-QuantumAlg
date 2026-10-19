/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Program
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Record
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# The actual subsequent recovered batch preserves every complete seed block

Fresh sampling and sixteen more rounds use the already allocated bank.
Their actual complete store-reference seed invariant then crosses the real
classical recovery record. The invariant includes every earlier result,
new sample and retained factor; no quantum marginal is used to infer a
stronger conditional state promise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

attribute [local irreducible] NativeBatchReuse.context NativeBatchReuse.code

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

include sameWires in
/-- The subsequent recovery preserves the actual physical wire correspondence of the same bank. -/
lemma seedWires :
    (context base N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (context_base_wires base N).trans sameWires

/-- The actual complete recovery tail preserves the seed separately in every final store. -/
lemma tail_seedBlocks (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (NativeBatchReuse.context base N) Reference
      (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.nativeBatchReuse_context_wires base N sameWires) N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (seedWires base sameWires) N ((tail base input).execute environment Reference state) :=
  RuntimeRound.shortDLP_runtimeRetainedRecord_seedBlocks
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (NativeBatchReuse.nativeBatchReuse_context_wires base N sameWires)
    (tail base input) (step base input) (tail_execute base input) state seeded

/-- One more actual sampled-and-recovered batch preserves the internal complete seed invariant. -/
lemma code_seedBlocks (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      sameWires N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (seedWires base sameWires) N
      ((code base sameWires originalCells input).execute environment Reference state) := by
  have source := NativeBatchReuse.nativeBatchReuse_code_seedBlocks (environment := environment)
    base N sameWires originalCells
    input state seeded
  exact BasisSeeded.seq (environment := environment)
    (NativeBatchReuse.code base N sameWires originalCells)
    (tail base input)
    ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (seedWires base sameWires)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state
    (tail_seedBlocks base sameWires input _ source)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
