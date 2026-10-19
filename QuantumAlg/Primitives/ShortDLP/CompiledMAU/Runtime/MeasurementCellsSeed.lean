/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Actual shared measurement-cell allocation retains the prepared bank seed

The existing allocator consists only of real retained finite cells. Its
prefix induction preserves every complete store-reference seed block using
the actual retention and history-reassociation laws. The quantum bank is
unchanged, including when no measurement cell is allocated.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

/-- Allocating actual finite measurement cells preserves every complete prepared seed block. -/
lemma shortDLP_runtimeMeasurementCells_seedBlocks {ctx : RuntimeCtx .quantum}
    (m ell width N : Nat)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (dimension : ℕ+) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state) :
    HasSeedBlocks m ell width
      ((MeasurementCells.context_quantumWires ctx dimension count).trans sameWires) N
      ((MeasurementCells.allocate (model := model) ctx dimension count).execute environment
        Reference state) := by
  have corresponding :
      (RuntimePlacement.basisEquiv m ell width
        ((MeasurementCells.context_quantumWires ctx dimension count).trans sameWires)).symm
          (CompiledMAU.reloadLabel m ell width N) =
        MeasurementCells.basisEquiv ctx dimension count
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N)) := by
    induction count with
    | zero => rfl
    | succ count induction => exact induction
  change BasisSeeded.Holds _ _
  rw [corresponding]
  exact MeasurementCells.allocate_seeded (environment := environment)
    (model := model) ctx dimension count
    ((RuntimePlacement.basisEquiv m ell width sameWires).symm
      (CompiledMAU.reloadLabel m ell width N)) state seeded

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
