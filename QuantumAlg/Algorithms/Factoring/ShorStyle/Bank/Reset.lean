/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Seed
import all QuantumAlg.Primitives.ZReset.Reload

/-!
# Complete Shor store-reference blocks after actual bank reuse

The actual reset and shared X reload restore the bank's exact source seed.
Every complete classical store retains its entire reference block. In
particular, the stored residue sample, parameter and measured phase keep
their correlations while the same owned quantum systems become ready for
the next round. No independence assumption is imposed on the incoming state.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Actual reset and reload establish the seed and retain every complete store-reference block. -/
theorem resetReload_store_entry {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((resetReload N sameWires).execute Reference state)
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      NormalizedVector.ket (R := ctx.register)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) left *
        (∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)) *
        star (NormalizedVector.ket (R := ctx.register)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) right) :=
  ZReset.Reload.zResetReload_store_entry (NativePlacement.qubits N sameWires)
    (NativePlacement.reloadProgram N sameWires) (NativePlacement.reload_physicalIdx N sameWires)
    ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N))
    (NativePlacement.reload_apply_zero N sameWires) state original left right leftRef rightRef

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
