/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Actual shared measurement-cell allocation retains the prepared bank seed

The existing allocator consists only of real retained finite cells. Its
prefix induction preserves every complete store-reference seed block using
the actual retention and history-reassociation laws. The quantum bank is
unchanged, including when no measurement cell is allocated.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

/-- Allocating actual finite measurement cells preserves every complete prepared seed block. -/
theorem shortDLP_runtimeMeasurementCells_seedBlocks {ctx : RuntimeCtx .quantum}
    (m ell width N : Nat)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (dimension : ℕ+) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seeded : HasSeedBlocks m ell width sameWires N state) :
    HasSeedBlocks m ell width
      ((MeasurementCells.context_quantumWires ctx dimension count).trans sameWires) N
      ((MeasurementCells.allocate ctx dimension count).execute Reference state) := by
  induction count with
  | zero =>
      exact shortDLP_runtimeSeedBlocks_mapHistory m ell width sameWires N state seeded
        (fun history => (history, ()))
  | succ count induction =>
      let allocationPrefix := MeasurementCells.allocate ctx dimension count
      let middle := MeasurementCells.context ctx dimension count
      let middleWires :=
        (MeasurementCells.context_quantumWires ctx dimension count).trans sameWires
      let retain := Circuit.retain middle middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh
      have retained := shortDLP_runtimeSeedBlocks_retain m ell width middleWires N
        middle.canonicalFreshKey (.finite dimension) middle.canonicalFreshKey_fresh
        (allocationPrefix.execute Reference state) induction
      exact RuntimeRepetition.seq_seed allocationPrefix retain m ell width N
        ((MeasurementCells.context_quantumWires ctx dimension (count + 1)).trans sameWires)
        state retained

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
