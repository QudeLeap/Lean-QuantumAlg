/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Input.WideBasis.Layout

/-!
# Actual wide sample decoding and source-basis initialization

The actual two-sample decoder feeds the actual native basis loader through
the same chronological execution store. The original wide cells and source
sample convention are retained, with no separate classical execution runtime.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Both actual stored samples feed the actual initialized native wide source basis. -/
def decodeBasisInto (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (BatchMachine.decodePairInto refs.pair)
    (LatticeBasis.loadBasisInto (m := shortLogBits N) (ell := tradeoffBits N) refs.pair refs.raw)

/-- Actual chronological decoder/basis store and the complete original execution paths. -/
def decodeBasisStep (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (decodeBasisInto refs).Path :=
  let decoded := BatchMachine.decodePairStep refs.pair store
  let loaded := LatticeBasis.basisStep (shortLogBits N) (tradeoffBits N)
    refs.pair refs.raw decoded.1
  (loaded.1, (decoded.2, loaded.2))

/-- Actual wide initialization preserves original history and quantum-reference correlations. -/
lemma decodeBasisInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decodeBasisInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := decodeBasisStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (BatchMachine.decodePairInto refs.pair)
    (LatticeBasis.loadBasisInto (m := shortLogBits N) (ell := tradeoffBits N) refs.pair refs.raw)
    (fun before =>
      let actual := BatchMachine.decodePairStep (model := model) refs.pair before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeBasis.basisStep (model := model)
        (shortLogBits N) (tradeoffBits N) refs.pair refs.raw before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      BatchMachine.decodePairInto_execute refs.pair reference current)
    (fun reference _history _ current =>
      LatticeBasis.loadBasisInto_execute
        (shortLogBits N) (tradeoffBits N) refs.pair refs.raw reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix
