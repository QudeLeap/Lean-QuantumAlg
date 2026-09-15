/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Program
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Record

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

open Execution ShortDLP.CompiledMAU

attribute [local irreducible] NativeBatchReuse.context NativeBatchReuse.code

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

include sameWires in
/-- The subsequent recovery preserves the actual physical wire correspondence of the same bank. -/
theorem seedWires :
    (context base N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (context_base_wires base N).trans sameWires

/-- The actual complete recovery tail preserves the seed separately in every final store. -/
theorem tail_seedBlocks (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (NativeBatchReuse.context base N) Reference History)
    (seeded : RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.nativeBatchReuse_context_wires base N sameWires) N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (seedWires base sameWires) N ((tail base input).execute Reference state) :=
  RuntimeRound.shortDLP_runtimeRetainedRecord_seedBlocks
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (NativeBatchReuse.nativeBatchReuse_context_wires base N sameWires)
    (tail base input) (step base input) (tail_execute base input) state seeded

/-- One more actual sampled-and-recovered batch preserves the internal complete seed invariant. -/
theorem code_seedBlocks (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (seeded : RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      sameWires N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (seedWires base sameWires) N
      ((code base sameWires originalCells input).execute Reference state) := by
  have source := NativeBatchReuse.nativeBatchReuse_code_seedBlocks base N sameWires originalCells
    input state seeded
  exact RuntimeRepetition.seq_seed (NativeBatchReuse.code base N sameWires originalCells)
    (tail base input) (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (seedWires base sameWires) state (tail_seedBlocks base sameWires input _ source)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
