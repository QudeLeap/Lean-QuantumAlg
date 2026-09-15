/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Reuse.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Space

/-!
# Actual resource bounds for a later batch on the original bank

The complete source sampler and sixteen measured rounds contribute their
native coordinates and serial dependencies. All new storage is classical:
source preparation work, two retained source results, sixteen retained
outcomes and the real reset scratch bit. The original bank and measurement
cells remain in the caller's resident and auxiliary pools.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- Independent native allowance for one complete later sampled batch. -/
def nativeEnvelope (N : Nat) : ResourcePool .quantum :=
  ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N +
    16 • RuntimeRound.eventEnvelope (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- Independent serial bound retains the source-to-round dependency and all round resets. -/
def unitDepthBound (N : Nat) : Nat :=
  44 * modulusBits N + 161 +
    16 * RuntimeRound.unitDepthBound (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- All extra capacity is explicitly classical; the caller already owns the quantum bank. -/
def additionalSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.bits (27 * modulusBits N + 16 * measurementBits N + 16))

private theorem samplerSpaceBound (width measured : Nat) (original : SpacePool .quantum) :
    original + ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum width ≤
      original + SpacePool.ofShape (.bits (27 * width + 16 * measured + 16)) := by
  intro axis
  cases axis <;>
    simp [ShorStyle.Canonical.Sampler.Retained.additionalSpace, SpacePool.ofShape]
  omega

private theorem continuationSpaceBound (width measured : Nat) (original : SpacePool .quantum) :
    SpacePool.ofShape (.finite 2) + 16 • SpacePool.ofShape (.bits measured) +
        (original + ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum width) ≤
      original + SpacePool.ofShape (.bits (27 * width + 16 * measured + 16)) := by
  have bitSize : Nat.clog 2 2 = 1 := by decide
  intro axis
  cases axis <;>
    simp [ShorStyle.Canonical.Sampler.Retained.resultSpace, SpacePool.ofShape, bitSize]
  omega

variable (base : RuntimeCtx .quantum) (N : Nat)
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- The actual later-batch path obeys every independent native coordinate allowance. -/
theorem nativeBatchReuse_resourcePool_le (path : (code base N sameWires originalCells).Path) :
    (code base N sameWires originalCells).resourcePool path ≤ nativeEnvelope N := by
  change ResourcePool.ofList
    ((ShorStyle.Canonical.Sampler.Retained.circuit base N).eventTrace path.1 ++
      (rounds base N sameWires originalCells).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le base N path.1)
    (RuntimeRepetition.shortDLP_runtimeRepetition_resourcePool_le
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
      (parameterUnit (N := N)) (parameterTarget (N := N))
      (sampledContext base N) (nativeBatchReuse_sampled_wires base N sameWires)
      (parameter base N) (cells base N originalCells) 16 path.2)

/-- One source draw precedes the serial depth of all sixteen complete measured rounds. -/
theorem nativeBatchReuse_unitDepth_le (path : (code base N sameWires originalCells).Path) :
    (code base N sameWires originalCells).depth (fun _ => 1) path ≤ unitDepthBound N :=
  Nat.add_le_add
    (ShorStyle.Canonical.Sampler.Retained.samplerRetained_unit_depth_le base N path.1)
    (RuntimeRepetition.shortDLP_runtimeRepetition_unitDepth_le
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
      (parameterUnit (N := N)) (parameterTarget (N := N))
      (sampledContext base N) (nativeBatchReuse_sampled_wires base N sameWires)
      (parameter base N) (cells base N originalCells) 16 path.2)

/-- Resident space includes the same original bank and all newly live classical storage. -/
theorem nativeBatchReuse_resident_le (path : (code base N sameWires originalCells).Path) :
    (code base N sameWires originalCells).peakResidentSpace path ≤
      base.residentSpace + additionalSpace N := by
  refine (Circuit.peakResidentSpace_seq
    (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    (rounds base N sameWires originalCells) path).le.trans ?_
  apply SpacePool.max_le
  · exact (ShorStyle.Canonical.Sampler.Retained.samplerRetained_resident_le
      base N path.1).trans (samplerSpaceBound (modulusBits N) (measurementBits N) _)
  · have repeated := RuntimeRepetition.shortDLP_runtimeRepetition_resident_le
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
      (parameterUnit (N := N)) (parameterTarget (N := N))
      (sampledContext base N) (nativeBatchReuse_sampled_wires base N sameWires)
      (parameter base N) (cells base N originalCells) 16 path.2
    have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_resident base N
    exact (repeated.trans_eq (congrArg
      (fun frame : SpacePool .quantum => SpacePool.ofShape (.finite 2) +
        16 • SpacePool.ofShape (.bits (measurementBits N)) + frame) sampled)).trans
      (continuationSpaceBound (modulusBits N) (measurementBits N) _)

/-- Auxiliary space counts the same bank, retained results and real reset scratch cell. -/
theorem nativeBatchReuse_auxiliary_le (path : (code base N sameWires originalCells).Path) :
    (code base N sameWires originalCells).peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N := by
  refine (Circuit.peakAuxiliarySpace_seq
    (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    (rounds base N sameWires originalCells) path).le.trans ?_
  apply SpacePool.max_le
  · exact (ShorStyle.Canonical.Sampler.Retained.samplerRetained_auxiliary_le
      base N path.1).trans (samplerSpaceBound (modulusBits N) (measurementBits N) _)
  · have repeated := RuntimeRepetition.shortDLP_runtimeRepetition_auxiliary_le
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
      (parameterUnit (N := N)) (parameterTarget (N := N))
      (sampledContext base N) (nativeBatchReuse_sampled_wires base N sameWires)
      (parameter base N) (cells base N originalCells) 16 path.2
    have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_auxiliary base N
    exact (repeated.trans_eq (congrArg
      (fun frame : SpacePool .quantum => SpacePool.ofShape (.finite 2) +
        16 • SpacePool.ofShape (.bits (measurementBits N)) + frame) sampled)).trans
      (continuationSpaceBound (modulusBits N) (measurementBits N) _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse
