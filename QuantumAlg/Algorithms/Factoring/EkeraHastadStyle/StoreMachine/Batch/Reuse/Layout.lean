/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Retained recovery output beside the existing native batch bank

One fresh optional-factor cell extends the actual native batch context. Every
source read remains structural in that same live context; no bank or sampled
parameter is reconstructed for the classical recovery tail.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (N : Nat)

/-- The sole new retained key follows all entries of the actual completed native batch. -/
def resultKey : StorageKey := (NativeBatchReuse.context base N).canonicalFreshKey

/-- The actual live bank and all source cells remain beside one fresh optional-factor cell. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum :=
  (NativeBatchReuse.context base N).addRetained (resultKey base N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh

/-- The caller-visible result is a real writable retained cell. -/
def resultRef : CWriteRef (context base N) (LatticeBatchRecoveryOutput.OutputShape N) :=
  .retainedHead (NativeBatchReuse.context base N) (resultKey base N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh

/-- Every old structural input remains a reference to the same actual storage. -/
def liftInput {shape : CShape}
    (input : CInputRef (NativeBatchReuse.context base N) shape) :
    CInputRef (context base N) shape :=
  input.underRetained (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh

/-- An earlier caller operand remains structural through the new batch and its recovery output. -/
def callerInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base N) shape :=
  liftInput base N (NativeBatchReuse.callerInput base N input)

/-- The sampled residue remains in its original retained source cell. -/
def sourceSample : CInputRef (context base N) (.bits (residueSamplingBits N)) :=
  liftInput base N (NativeBatchReuse.finalSample base N)

/-- Recovery reads the original complete shared parameter. -/
def sourceParameter : CInputRef (context base N) (ParameterShape N) :=
  liftInput base N (NativeBatchReuse.finalParameter base N)

/-- All sixteen chronological source outcomes remain in their original retained cells. -/
def sourceResults :
    CInputRef (context base N) (.fixedVector 16 (.bits (measurementBits N))) :=
  liftInput base N (NativeBatchReuse.finalResults base N)

/-- Original terminal reads used by the pure fixed-batch specification. -/
def sourceTerminals : LatticePairRecoveryBatch.Terminals
    (NativeBatchReuse.context base N) N :=
  fun index => .vectorGet (NativeBatchReuse.finalResults base N) index

/-- The actual classical machine reads those same terminals underneath the retained output. -/
def terminals : LatticePairRecoveryBatch.Terminals (context base N) N :=
  fun index => liftInput base N (sourceTerminals base N index)

/-- Fresh result storage cannot overlap any structural source read. -/
theorem result_avoids_input {shape : CShape}
    (input : CInputRef (NativeBatchReuse.context base N) shape) :
    (resultRef base N).key ∉ (liftInput base N input).storageKeys :=
  input.fresh_not_mem_storageKeys_underRetained (resultKey base N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh

/-- Retaining the result preserves the identical actual bank and wire identities. -/
theorem context_quantumWires :
    (context base N).quantumWires =
      (NativeBatchReuse.context base N).quantumWires :=
  RuntimeCtx.quantumWires_addRetained (NativeBatchReuse.context base N)
    (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatchReuse.context base N).canonicalFreshKey_fresh

/-- The continuation retains precisely the caller's original ordered quantum wires. -/
theorem context_base_wires : (context base N).quantumWires = base.quantumWires :=
  (context_quantumWires base N).trans
    ((ShortDLP.CompiledMAU.RuntimeResults.shortDLP_runtimeResults_wires
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.sampledContext base N) 16).trans
        (ShorStyle.Canonical.Sampler.Retained.samplerNative_quantumWires base N))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
