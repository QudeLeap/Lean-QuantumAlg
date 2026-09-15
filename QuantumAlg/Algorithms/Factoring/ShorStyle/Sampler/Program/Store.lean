/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Frame

/-!
# Complete store result of actual residue preparation

The source parameter and the unchanged reads of every other caller cell
identify the entire final store. This mathematical write is independent of
the loader, proposal scan, Euclidean loop and chosen decision path that
implement it. Every initialized internal cell has already been released.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual scoped program changes precisely its complete parameter cell. -/
theorem samplerProgram_store (input : Input N)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N))
    (sampled : store.read sample = .bits (PackedSample.storedBits value)) :
    (step N sample output store).1 = store.write output (parameterValue input value) := by
  apply Store.store_eq_write_of_read_frame
  · exact samplerProgram_read input sample output store value sampled
  · intro shape other separate
    exact samplerProgram_read_other N sample output (.storage other)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separate) store

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
