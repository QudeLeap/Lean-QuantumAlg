/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Layout
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation

/-!
# One retained first-success result beside the actual batch chain

The completed chain keeps every original bank, source and factor cell. A
single fresh optional-word cell stores the selected result; all chronological
factor reads are lifted structurally through that real retained allocation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection

open Execution

noncomputable section

variable (source : RuntimeCtx .quantum) (N : Nat)

/-- The selected result receives the next actual fresh storage key. -/
def resultKey : StorageKey := source.canonicalFreshKey

/-- The complete source context survives beside one real retained optional factor. -/
@[implicit_reducible]
def context : RuntimeCtx .quantum :=
  source.addRetained (resultKey source) (LatticeBatchRecoveryOutput.OutputShape N)
    source.canonicalFreshKey_fresh

/-- The selected result is stored in the actual retained head cell. -/
def resultRef : CWriteRef (context source N) (LatticeBatchRecoveryOutput.OutputShape N) :=
  .retainedHead source (resultKey source) (LatticeBatchRecoveryOutput.OutputShape N)
    source.canonicalFreshKey_fresh

/-- Every source operand crosses the new result without changing its storage identity. -/
def liftInput {shape : CShape} (input : CInputRef source shape) :
    CInputRef (context source N) shape :=
  input.underRetained (resultKey source) (LatticeBatchRecoveryOutput.OutputShape N)
    source.canonicalFreshKey_fresh

/-- Fresh selected-result storage lies outside every original structural read. -/
theorem result_avoids_input {shape : CShape} (input : CInputRef source shape) :
    (resultRef source N).key ∉ (liftInput source N input).storageKeys :=
  input.fresh_not_mem_storageKeys_underRetained (resultKey source)
    (LatticeBatchRecoveryOutput.OutputShape N) source.canonicalFreshKey_fresh

/-- Selection keeps the identical ordered quantum-wire identities. -/
theorem context_quantumWires : (context source N).quantumWires = source.quantumWires :=
  RuntimeCtx.quantumWires_addRetained source (resultKey source)
    (LatticeBatchRecoveryOutput.OutputShape N) source.canonicalFreshKey_fresh

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection
