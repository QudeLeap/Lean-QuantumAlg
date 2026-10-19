/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Retaining real round results preserves the actual seed blocks

A retained result cell changes only classical storage. Its actual push keeps
the whole previous store injectively, and history reassociation keeps every
complete store-reference block. These facts transport the internal seed
invariant through the actual constructors used between repeated rounds.

No new state transformation is introduced. In particular, all earlier
results and the actual sampled parameter remain in the retained store.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Reorganizing actual histories preserves the internal invariant on every complete store. -/
lemma shortDLP_runtimeSeedBlocks_mapHistory (N : Nat)
    {Reference : Register} {History Later : Type} [Fintype History] [Fintype Later]
    (state : State ctx Reference History) (seeded : HasSeedBlocks m ell width sameWires N state)
    (update : History → Later) :
    HasSeedBlocks m ell width sameWires N (state.mapHistory update) :=
  BasisSeeded.mapHistory _ state seeded update

/-- An actual retained classical cell keeps the same source seed and all old store correlations. -/
lemma shortDLP_runtimeSeedBlocks_retain (N : Nat)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state) :
    HasSeedBlocks m ell width
      ((RuntimeCtx.quantumWires_addRetained ctx key shape fresh).trans sameWires) N
      ((Circuit.retain (model := model) ctx key shape fresh).execute environment Reference state) :=
  BasisSeeded.retain (environment := environment) (model := model)
    ((RuntimePlacement.basisEquiv m ell width sameWires).symm
      (CompiledMAU.reloadLabel m ell width N)) state seeded key shape fresh

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
