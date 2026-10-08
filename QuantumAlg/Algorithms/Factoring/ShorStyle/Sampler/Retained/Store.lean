/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Store

/-!
# Independent full-store output of retained residue sampling

For each finite uniform source integer, the mathematical output stores its
bits and the source's complete unit/factor parameter in the two real retained
cells. Every original caller value is preserved. The actual native program
is proved to produce this whole store, including arbitrary initial values
and its complete independently specified early-factor result.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Independent mathematical store update of the two actual retained outputs. -/
def outputStore (input : Input N) (store : Store (context ctx N))
    (value : Fin (2 ^ residueSamplingBits N)) : Store (context ctx N) :=
  (store.write (sampleRef ctx N) (.bits (PackedSample.storedBits value))).write
    (parameterRef ctx N) (parameterValue input value)

/-- Complete mathematical result store, including both allocated cells and every caller entry. -/
def resultStore (input : Input N) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) : Store (context ctx N) :=
  outputStore input (pushStore N store) value

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual sampled path produces exactly the independent complete store update. -/
theorem samplerRetained_outcome_store (input : Input N) (store : Store (context ctx N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    (outcomeStep (model := model) ctx N store value).1 = outputStore input store value :=
  Program.samplerProgram_store (model := model) input (FirstAccepted.cellRead (sampleRef ctx N))
    (parameterRef ctx N) (store.write (sampleRef ctx N) (.bits (PackedSample.storedBits value)))
    value (Store.read_write_same store (sampleRef ctx N) _)

/-- The actual allocations and native sampled path have the prescribed complete store result. -/
theorem samplerRetained_result_store (input : Input N) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    (outcomeStep (model := model) ctx N (pushStore N store) value).1 =
      resultStore input store value :=
  samplerRetained_outcome_store (model := model) input (pushStore N store) value

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
