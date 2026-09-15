/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration.Seed

/-!
# The same actual Shor bank remains seeded through every finite batch

The initial seed is supplied by the one actual preparation. Each real round
resets and reloads that bank before the next round executes. The invariant
holds separately in every complete final store block, with all reference
coordinates retained, including the empty finite batch.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch

noncomputable section

open Execution

/-- All finite actual repetitions retain the seed in the identical physical bank coordinates. -/
theorem code_seeded (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N ((quantumWires ctx N count).trans sameWires)).symm
        (NativeQuantum.seedLabel N))
      ((code ctx N sameWires count).execute Reference state) := by
  induction count generalizing ctx History with
  | zero =>
      exact BasisSeeded.mapHistory _ state seeded (fun history => (history, ()))
  | succ count induction =>
      exact BasisSeeded.seq (NativeIteration.code ctx N sameWires)
        (code (NativeIteration.context ctx N) N
          ((NativeIteration.quantumWires ctx N).trans sameWires) count) _ state
        (induction (NativeIteration.context ctx N)
          ((NativeIteration.quantumWires ctx N).trans sameWires)
          ((NativeIteration.code ctx N sameWires).execute Reference state)
          (NativeIteration.code_seeded N sameWires state))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch
