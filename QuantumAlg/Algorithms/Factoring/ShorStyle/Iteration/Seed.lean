/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage.Seed

/-!
# Every actual sampled Shor iteration returns the same bank seed

The actual sampler, retained measurement storage, selected quantum member,
measurement, packing and full-bank reset/reload use a single sequential
execution. Its complete final store retains the bank seed jointly with all
earlier classical values and the reference. No second quantum preparation is
needed when continuing to the next actual iteration.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration

noncomputable section

open Execution

/-- A complete actual iteration establishes the seed on its unchanged physical bank. -/
theorem code_seeded {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N ((quantumWires ctx N).trans sameWires)).symm
        (NativeQuantum.seedLabel N))
      ((code ctx N sameWires).execute Reference state) :=
  BasisSeeded.seq (Sampler.Retained.circuit ctx N)
    (NativeStorage.round (sampledContext ctx N) N
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)) _ state
    (NativeStorage.round_seeded (sampledContext ctx N) N
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)
      ((Sampler.Retained.circuit ctx N).execute Reference state))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration
