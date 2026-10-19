/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Retained recovery output beside the original native batch bank

One fresh optional-factor cell extends the actual native batch context. Every
source read remains structural in that same live context; no bank or sampled
parameter is reconstructed for the classical recovery tail.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The sole new retained key follows all entries of the actual completed native batch. -/
def resultKey : StorageKey := (NativeBatch.context base noQuantum N).canonicalFreshKey

/-- The actual live bank and all source cells remain beside one fresh optional-factor cell. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum :=
  (NativeBatch.context base noQuantum N).addRetained (resultKey base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

/-- The caller-visible result is a real writable retained cell. -/
def resultRef : CWriteRef (context base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N) :=
  .retainedHead (NativeBatch.context base noQuantum N) (resultKey base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

/-- Every old structural input remains a reference to the same actual storage. -/
def liftInput {shape : CShape}
    (input : CInputRef (NativeBatch.context base noQuantum N) shape) :
    CInputRef (context base noQuantum N) shape :=
  input.underRetained (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

/-- The sampled residue remains in its original retained source cell. -/
def sourceSample : CInputRef (context base noQuantum N) (.bits (residueSamplingBits N)) :=
  liftInput base noQuantum N (NativeBatch.finalSample base noQuantum N)

/-- Recovery reads the original complete shared parameter. -/
def sourceParameter : CInputRef (context base noQuantum N) (ParameterShape N) :=
  liftInput base noQuantum N (NativeBatch.finalParameter base noQuantum N)

/-- All sixteen chronological source outcomes remain in their original retained cells. -/
def sourceResults :
    CInputRef (context base noQuantum N) (.fixedVector 16 (.bits (measurementBits N))) :=
  liftInput base noQuantum N (NativeBatch.finalResults base noQuantum N)

/-- Original terminal reads used by the pure fixed-batch specification. -/
def sourceTerminals : LatticePairRecoveryBatch.Terminals
    (NativeBatch.context base noQuantum N) N :=
  fun index => .vectorGet (NativeBatch.finalResults base noQuantum N) index

/-- The actual classical machine reads those same terminals underneath the retained output. -/
def terminals : LatticePairRecoveryBatch.Terminals (context base noQuantum N) N :=
  fun index => liftInput base noQuantum N (sourceTerminals base noQuantum N index)

/-- Fresh result storage cannot overlap any structural source read. -/
lemma result_avoids_input {shape : CShape}
    (input : CInputRef (NativeBatch.context base noQuantum N) shape) :
    (resultRef base noQuantum N).key ∉ (liftInput base noQuantum N input).storageKeys :=
  input.fresh_not_mem_storageKeys_underRetained (resultKey base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

/-- Retaining the result preserves the identical actual bank and wire identities. -/
lemma context_quantumWires :
    (context base noQuantum N).quantumWires =
      (NativeBatch.context base noQuantum N).quantumWires :=
  RuntimeCtx.quantumWires_addRetained (NativeBatch.context base noQuantum N)
    (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
    (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
