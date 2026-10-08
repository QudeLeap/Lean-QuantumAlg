/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Core.Execution.Basis.Seeded.Record

/-!
# Actual retained records preserve complete short-DLP seed blocks

The retained context has the same physical quantum basis. Applying the
complete deterministic store-record theorem therefore preserves the exact
short-DLP reload label in every final store-reference block. The argument
is generic in the existing context and the actual retained continuation.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

/-- A real retained continuation preserves the source seed in every complete store block. -/
theorem shortDLP_runtimeRetainedRecord_seedBlocks {ctx : RuntimeCtx .quantum}
    (m ell width N : Nat)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    {key : StorageKey} {shape : CShape} {fresh : key ∉ ctx.keys}
    (code : Circuit model ctx (ctx.addRetained key shape fresh))
    (step : Store ctx × model.HiddenState →
      (Store (ctx.addRetained key shape fresh) × model.HiddenState) × code.Path)
    (record : Circuit.RetainedRecord code step)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state) :
    HasSeedBlocks m ell width
      ((RuntimeCtx.quantumWires_addRetained ctx key shape fresh).trans sameWires) N
      (code.execute Reference state) :=
  BasisSeeded.retainedRecord code step record
    ((RuntimePlacement.basisEquiv m ell width sameWires).symm
      (CompiledMAU.reloadLabel m ell width N)) state seeded

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
