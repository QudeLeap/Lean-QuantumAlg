/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Space

/-!
# Exact complete storage retained by the first recovered batch

The first batch allocates one quantum bank and its original measurement-cell
family. Its two source cells, sixteen outcomes and optional factor have the
same retained capacity as a later batch. Lexical recovery and reset scratch
do not appear in the final context; their live peaks remain charged by the
independent complete-code resource theorems.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

noncomputable section

open Execution ShortDLP.CompiledMAU

attribute [local irreducible] NativeBatch.context RuntimeResults.context

/-- The sole allocated quantum bank and the original writable measurement-cell family. -/
def bankSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofQuantumLayout
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
      measurementBits N • SpacePool.ofShape (.finite 2)

/-- Exactly the first bank, its measurement cells and the complete retained batch data. -/
def retainedSpace (N : Nat) : SpacePool .quantum :=
  bankSpace N + NativeBatchReuseRecovery.retainedSpace N

/-- The first complete recovery leaves precisely its permanent resident capacity. -/
lemma firstRecovery_context_resident (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) :
    (context base noQuantum N).residentSpace = base.residentSpace + retainedSpace N := by
  have retained : (context base noQuantum N).residentSpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatch.context base noQuantum N).residentSpace :=
    RuntimeCtx.residentSpace_addRetained (NativeBatch.context base noQuantum N)
      (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh
  have results := RuntimeResults.shortDLP_runtimeResults_resident
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatch.readyContext base noQuantum N) 16
  rw [retained, NativeBatch.context, results, NativeBatch.nativeBatch_ready_residentSpace]
  change SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
    (16 • SpacePool.ofShape (.bits (measurementBits N)) +
      (measurementBits N • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
            (base.residentSpace +
              ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))))) = _
  unfold retainedSpace bankSpace NativeBatchReuseRecovery.retainedSpace
  ac_rfl

/-- The same actual retained keys keep their complete owned auxiliary capacity. -/
lemma firstRecovery_context_auxiliary (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) :
    (context base noQuantum N).auxiliarySpace = base.auxiliarySpace + retainedSpace N := by
  have retained : (context base noQuantum N).auxiliarySpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatch.context base noQuantum N).auxiliarySpace :=
    RuntimeCtx.auxiliarySpace_addRetained (NativeBatch.context base noQuantum N)
      (resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh
  have results := RuntimeResults.shortDLP_runtimeResults_auxiliary
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatch.readyContext base noQuantum N) 16
  rw [retained, NativeBatch.context, results, NativeBatch.nativeBatch_ready_auxiliarySpace]
  change SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
    (16 • SpacePool.ofShape (.bits (measurementBits N)) +
      (measurementBits N • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
            (base.auxiliarySpace +
              ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))))) = _
  unfold retainedSpace bankSpace NativeBatchReuseRecovery.retainedSpace
  ac_rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
