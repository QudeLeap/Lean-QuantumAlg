/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Retention
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# The actual repeated circuit preserves its complete store-reference seed

Induction follows the actual retain, round and recursive sequence. Every
positive round establishes the seed through its actual reset/reload; the
empty repetition retains the incoming seed. History reassociation preserves
the complete store blocks. The same result applies in particular to the
source's sixteen rounds on one existing bank.

This internal state theorem does not assert statistical independence by
itself. The separate source-fiber theorem supplies the conditional measured
weights while preserving actual stored parameters and previous outcomes.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Arbitrarily many actual rounds retain the same seed in each complete final store block. -/
theorem shortDLP_runtimeRepetition_seedBlocks {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ) :
    ∀ (count : Nat) (ctx : RuntimeCtx .quantum)
      (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
      (parameter : CInputRef ctx shape)
      (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
      {Reference : Register} {History : Type} [Fintype History]
      (state : State ctx Reference (RuntimeRound.model.HiddenState × History)),
      RuntimeRound.HasSeedBlocks m ell width sameWires N state →
        RuntimeRound.HasSeedBlocks m ell width
          (shortDLP_runtimeRepetition_wires m ell width ctx sameWires count) N
          ((code m ell width N generator target ctx sameWires parameter cells count).execute
            Reference state) := by
  intro count
  induction count with
  | zero =>
      intro ctx sameWires parameter cells Reference History _ state seeded
      exact BasisSeeded.mapHistory _ state.skip
        (BasisSeeded.mapHistory _ state seeded (fun record => (record, ())))
        (fun record => (record.1.1, (record.1.2, record.2)))
  | succ count induction =>
      intro ctx sameWires parameter cells Reference History _ state _seeded
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
      let tail := code m ell width N generator target next nextWires nextParameter nextCells count
      let retained := retention.execute Reference state
      let rounded := round.execute Reference retained
      have roundSeed := RuntimeRound.shortDLP_runtimeRound_seedBlocks m ell width nextWires
        nextParameter N generator target nextCells (RuntimeResults.head m ell width ctx) retained
      have tailSeed := induction next nextWires nextParameter nextCells rounded roundSeed
      have bodySeed := BasisSeeded.seq round tail _ retained tailSeed
      exact BasisSeeded.seq retention (.seq round tail) _ state bodySeed

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition
