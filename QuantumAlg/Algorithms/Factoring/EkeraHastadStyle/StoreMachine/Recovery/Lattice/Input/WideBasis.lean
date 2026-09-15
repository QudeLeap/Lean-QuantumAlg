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

/-- Both actual stored samples feed the actual initialized native wide source basis. -/
def decodeBasisInto (refs : Refs ctx N) : Circuit ctx ctx :=
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
theorem decodeBasisInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (decodeBasisInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((decodeBasisStep refs entry.1).1, (entry.2, (decodeBasisStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (BatchMachine.decodePairInto refs.pair)
    (LatticeBasis.loadBasisInto (m := shortLogBits N) (ell := tradeoffBits N) refs.pair refs.raw)
    (BatchMachine.decodePairStep refs.pair)
    (LatticeBasis.basisStep (shortLogBits N) (tradeoffBits N) refs.pair refs.raw)
    (BatchMachine.decodePairInto_execute refs.pair)
    (LatticeBasis.loadBasisInto_execute (shortLogBits N) (tradeoffBits N) refs.pair refs.raw)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix
