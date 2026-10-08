/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results

/-!
# Actual repeated short-DLP rounds on one existing bank

The sampled parameter and finite measurement cells already exist. Each round
retains one distinct packed-result cell, reads that same parameter, runs the
actual compiled member, measures and packs its outcome, then resets and reloads
the existing bank. The parameter and shared measurement cells are lifted
structurally underneath the result cell for the next round.

There is no quantum preparation in this repetition. Its caller allocates the
owned bank once after sampling. The complete final Output includes every live
bank and classical entry, with the chronological vector as its result read.
Statistical independence is a separate obligation of the actual reset and
full-state semantics; it is not assumed by this construction.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition

noncomputable section

/-- An actual retain followed by a complete reusable-bank round, repeated in source order. -/
def code {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ) :
    (ctx : RuntimeCtx .quantum) →
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires) →
    CInputRef ctx shape →
    (Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2)) →
    (count : Nat) → Circuit RuntimeRound.model ctx (RuntimeResults.context m ell width ctx count)
  | ctx, _, _, _, 0 => .id (model := RuntimeRound.model) ctx
  | ctx, sameWires, parameter, cells, count + 1 =>
      let nextContext := RuntimeResults.next m ell width ctx
      let nextWires :=
        (RuntimeResults.shortDLP_runtimeResult_next_wires m ell width ctx).trans sameWires
      let nextParameter := parameter.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      let nextCells := fun index => (cells index).underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      .seq (.retain (model := RuntimeRound.model)
        ctx ctx.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
        ctx.canonicalFreshKey_fresh)
        (.seq (RuntimeRound.code m ell width nextWires nextParameter N generator target
          nextCells (RuntimeResults.head m ell width ctx))
          (code m ell width N generator target nextContext nextWires nextParameter
            nextCells count))

/-- Full final output reads all distinct stored outcomes in their original round order. -/
def run {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat) :
    AlgorithmRun RuntimeRound.model ctx (RuntimeResults.context m ell width ctx count)
      (.fixedVector count (.bits (RuntimeRound.resultBits m ell width))) where
  code := code m ell width N generator target ctx sameWires parameter cells count
  output := Output.all (RuntimeResults.context m ell width ctx count)
    (.read (RuntimeResults.input m ell width ctx count))

/-- The zero-round boundary is the real identity circuit on the original context. -/
theorem shortDLP_runtimeRepetition_zero {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2)) :
    code m ell width N generator target ctx sameWires parameter cells 0 =
      .id (model := RuntimeRound.model) ctx := rfl

/-- Repetition leaves the exact same ordered physical bank in the complete output. -/
theorem shortDLP_runtimeRepetition_wires (m ell width : Nat)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires) (count : Nat) :
    (RuntimeResults.context m ell width ctx count).quantumWires =
      (runtimeLayout m ell width).wires :=
  (RuntimeResults.shortDLP_runtimeResults_wires m ell width ctx count).trans sameWires

/-- Every actual live result, parameter, finite cell and quantum bank entry is listed. -/
theorem shortDLP_runtimeRepetition_output_listing {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat) :
    (run m ell width N generator target ctx sameWires parameter cells count).output.listing =
      (RuntimeResults.context m ell width ctx count).keys := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition
