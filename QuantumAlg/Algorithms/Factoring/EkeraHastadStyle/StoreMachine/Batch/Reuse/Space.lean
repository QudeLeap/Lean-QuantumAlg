/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Resources

/-!
# Exact retained capacity of a complete later batch

Each later batch retains two source cells, sixteen outcome cells and one
optional-factor cell. Their capacity is distinct from the temporary sampler,
reset and recovery workspace. Every additional retained bit is classical;
the same ordered quantum bank remains available for the next batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

noncomputable section

open Execution ShortDLP.CompiledMAU

-- Use the compiled result-context equations without expanding sixteen retained layouts.
attribute [local irreducible] NativeBatchReuse.context RuntimeResults.context

/-- Exact persistent capacity of the two source cells, sixteen outcomes and one factor. -/
def retainedSpace (N : Nat) : SpacePool .quantum :=
  ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N) +
    16 • SpacePool.ofShape (.bits (measurementBits N)) +
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N)

/-- Independent binary capacity of precisely the permanently retained classical cells. -/
def retainedBits (N : Nat) : Nat := 19 * modulusBits N + 16 * measurementBits N + 2

/-- The permanent allowance is exactly the displayed classical-bit formula. -/
theorem retainedSpace_bits (N : Nat) :
    retainedSpace N = SpacePool.ofShape (.bits (retainedBits N)) := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [retainedSpace, retainedBits, ShorStyle.Canonical.Sampler.Retained.resultSpace,
      LatticeBatchRecoveryOutput.OutputShape, SpacePool.ofShape]
  omega

/-- No retained batch result allocates any quantum system of any dimension. -/
theorem retainedSpace_quantum (N : Nat) (dimension : ℕ+) :
    retainedSpace N (.quantumSystems dimension) = 0 := by
  rw [retainedSpace_bits]
  rfl

/-- The exact complete output resident capacity contains only the actual retained additions. -/
theorem reuseRecovery_context_resident (base : RuntimeCtx .quantum) (N : Nat) :
    (context base N).residentSpace = base.residentSpace + retainedSpace N := by
  have results := RuntimeResults.shortDLP_runtimeResults_resident
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchReuse.sampledContext base N) 16
  have sample := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_resident base N
  have retained : (context base N).residentSpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatchReuse.context base N).residentSpace :=
    RuntimeCtx.residentSpace_addRetained (NativeBatchReuse.context base N)
      (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatchReuse.context base N).canonicalFreshKey_fresh
  rw [retained, NativeBatchReuse.context, results,
    NativeBatchReuse.sampledContext, sample]
  change SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
    (16 • SpacePool.ofShape (.bits (measurementBits N)) +
      (base.residentSpace +
        ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))) = _
  unfold retainedSpace
  ac_rfl

/-- Retained cells remain owned auxiliaries with exactly the same classical capacity. -/
theorem reuseRecovery_context_auxiliary (base : RuntimeCtx .quantum) (N : Nat) :
    (context base N).auxiliarySpace = base.auxiliarySpace + retainedSpace N := by
  have results := RuntimeResults.shortDLP_runtimeResults_auxiliary
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchReuse.sampledContext base N) 16
  have sample := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_auxiliary base N
  have retained : (context base N).auxiliarySpace =
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
        (NativeBatchReuse.context base N).auxiliarySpace :=
    RuntimeCtx.auxiliarySpace_addRetained (NativeBatchReuse.context base N)
      (resultKey base N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatchReuse.context base N).canonicalFreshKey_fresh
  rw [retained, NativeBatchReuse.context, results,
    NativeBatchReuse.sampledContext, sample]
  change SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N) +
    (16 • SpacePool.ofShape (.bits (measurementBits N)) +
      (base.auxiliarySpace +
        ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))) = _
  unfold retainedSpace
  ac_rfl

/-- Repeated execution retains classical capacity without increasing its quantum bank. -/
theorem reuseRecovery_context_quantum (base : RuntimeCtx .quantum) (N : Nat) (dimension : ℕ+) :
    (context base N).residentSpace (.quantumSystems dimension) =
      base.residentSpace (.quantumSystems dimension) := by
  rw [reuseRecovery_context_resident]
  change base.residentSpace (.quantumSystems dimension) +
    retainedSpace N (.quantumSystems dimension) = _
  rw [retainedSpace_quantum, Nat.add_zero]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery
