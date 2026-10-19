/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Frame

/-!
# Complete retained values of the native RSA sampler

Each actual random outcome fills the real sample cell and selects the real
scoped program path. That path leaves the sample intact and writes precisely
the original source parameter, including its early-factor flag and payload.
No premise initializes or separates caller-provided scratch storage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind}

/-- The parameter's later allocation gives it a different actual key from the sample. -/
lemma samplerRetained_parameter_key_ne_sample (ctx : RuntimeCtx kind) (N : Nat) :
    (parameterRef ctx N).key ≠ (sampleRef ctx N).key := by
  intro same
  apply (sampleContext ctx N).canonicalFreshKey_fresh
  change (sampleContext ctx N).canonicalFreshKey ∈ ctx.canonicalFreshKey :: ctx.keys
  exact List.mem_cons.mpr (Or.inl same)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The actual store and complete body path selected by one genuine random outcome. -/
def outcomeStep (ctx : RuntimeCtx model.kind) (N : Nat) (store : Store (context ctx N))
    (value : Fin (2 ^ residueSamplingBits N)) :
      Store (context ctx N) × (body (model := model) ctx N).Path :=
  let sampled := store.write (sampleRef ctx N) (.bits (PackedSample.storedBits value))
  let prepared := Program.step (model := model) N (FirstAccepted.cellRead (sampleRef ctx N))
    (parameterRef ctx N) sampled
  (prepared.1, ((PackedSample.drawPathEquiv (model := model) N (sampleRef ctx N)).symm value,
    prepared.2))

/-- The real source sample remains readable after the full scoped parameter computation. -/
lemma samplerRetained_outcome_sample (store : Store (context ctx N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    (outcomeStep (model := model) ctx N store value).1.read
      (FirstAccepted.cellRead (sampleRef ctx N)) =
      .bits (PackedSample.storedBits value) := by
  have separate : (parameterRef ctx N).key ∉
      (FirstAccepted.cellRead (sampleRef ctx N)).storageKeys := by
    simpa only [FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton] using
      samplerRetained_parameter_key_ne_sample ctx N
  exact (Program.samplerProgram_read_other (model := model)
    N (FirstAccepted.cellRead (sampleRef ctx N))
    (parameterRef ctx N) (FirstAccepted.cellRead (sampleRef ctx N)) separate
    (store.write (sampleRef ctx N) (.bits (PackedSample.storedBits value)))).trans
      (Store.read_write_same store (sampleRef ctx N) _)

/-- Every actually sampled outcome yields exactly the source's complete unit/factor parameter. -/
lemma samplerRetained_outcome_parameter (input : Input N) (store : Store (context ctx N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    (outcomeStep (model := model) ctx N store value).1.read
      (FirstAccepted.cellRead (parameterRef ctx N)) =
      parameterValue input value :=
  Program.samplerProgram_read (model := model) input (FirstAccepted.cellRead (sampleRef ctx N))
    (parameterRef ctx N) (store.write (sampleRef ctx N) (.bits (PackedSample.storedBits value)))
    value (Store.read_write_same store (sampleRef ctx N) _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
