/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Actual Shor iteration capacity with sampler, results and reset scratch

An iteration retains the original sample, full parameter and both forms of
the phase result: `22m+1` classical bits in all. The native sampler's actual
workspace allowance `27m+15` also bounds the subsequent readout and reset.
Every quantum coordinate is unchanged throughout the actual path; on the
specified bank this is exactly `4m` qubits and no other dimensions. These
per-iteration facts include all live scratch and support later finite retry
accounting without allocating another quantum bank.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration

noncomputable section

variable (ctx : RuntimeCtx .quantum) (N : Nat)

/-- Exact classical capacity of all retained source and measured results of one iteration. -/
theorem context_resident :
    (context ctx N).residentSpace =
      ctx.residentSpace + SpacePool.ofShape (.bits (22 * modulusBits N + 1)) := by
  rw [context, NativeStorage.context_resident]
  change (Sampler.Retained.context ctx N).residentSpace + NativeStorage.resultSpace N = _
  rw [Sampler.Retained.samplerRetained_context_resident]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp [Sampler.Retained.resultSpace, NativeStorage.resultSpace,
    phaseBits, SpacePool.ofShape]; omega

theorem context_auxiliary :
    (context ctx N).auxiliarySpace =
      ctx.auxiliarySpace + SpacePool.ofShape (.bits (22 * modulusBits N + 1)) := by
  rw [context, NativeStorage.context_auxiliary]
  change (Sampler.Retained.context ctx N).auxiliarySpace + NativeStorage.resultSpace N = _
  rw [Sampler.Retained.samplerRetained_context_auxiliary]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp [Sampler.Retained.resultSpace, NativeStorage.resultSpace,
    phaseBits, SpacePool.ofShape]; omega

private theorem round_resident_budget :
    (sampledContext ctx N).residentSpace + NativeStorage.additionalSpace N ≤
      ctx.residentSpace + Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  change (Sampler.Retained.context ctx N).residentSpace + NativeStorage.additionalSpace N ≤ _
  rw [Sampler.Retained.samplerRetained_context_resident]
  intro axis
  cases axis <;> simp [Sampler.Retained.resultSpace, Sampler.Retained.additionalSpace,
    NativeStorage.additionalSpace, phaseBits, SpacePool.ofShape]; omega

private theorem round_auxiliary_budget :
    (sampledContext ctx N).auxiliarySpace + NativeStorage.additionalSpace N ≤
      ctx.auxiliarySpace + Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  change (Sampler.Retained.context ctx N).auxiliarySpace + NativeStorage.additionalSpace N ≤ _
  rw [Sampler.Retained.samplerRetained_context_auxiliary]
  intro axis
  cases axis <;> simp [Sampler.Retained.resultSpace, Sampler.Retained.additionalSpace,
    NativeStorage.additionalSpace, phaseBits, SpacePool.ofShape]; omega

/-- The same actual sampler and quantum path fit the explicit additional resident allowance. -/
theorem resident_le (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (path : (code ctx N sameWires).Path) :
    (code ctx N sameWires).peakResidentSpace path ≤
      ctx.residentSpace + Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq (Sampler.Retained.circuit ctx N)
    (NativeStorage.round (sampledContext ctx N) N
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)) path).le.trans ?_
  exact SpacePool.max_le (Sampler.Retained.samplerRetained_resident_le ctx N path.1)
    ((NativeStorage.resident_le (sampledContext ctx N) N _ _ path.2).trans
      (round_resident_budget ctx N))

/-- The actual auxiliary peak also includes all sampler work, retained results and reset scratch. -/
theorem auxiliary_le (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (path : (code ctx N sameWires).Path) :
    (code ctx N sameWires).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq (Sampler.Retained.circuit ctx N)
    (NativeStorage.round (sampledContext ctx N) N
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)) path).le.trans ?_
  exact SpacePool.max_le (Sampler.Retained.samplerRetained_auxiliary_le ctx N path.1)
    ((NativeStorage.auxiliary_le (sampledContext ctx N) N _ _ path.2).trans
      (round_auxiliary_budget ctx N))

private theorem initial_visited
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (path : (code ctx N sameWires).Path) :
    ctx ∈ (code ctx N sameWires).visitedContexts path := by
  change ctx ∈ ((([ctx, Sampler.Retained.sampleContext ctx N] ++
    [Sampler.Retained.sampleContext ctx N, Sampler.Retained.context ctx N]) ++
      (Sampler.Retained.body ctx N).visitedContexts path.1.2) ++ _)
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (.head _)))

/-- No actual iteration stage increases or decreases any live quantum capacity coordinate. -/
theorem quantum_peak_eq
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (path : (code ctx N sameWires).Path) (dimension : ℕ+) :
    (code ctx N sameWires).peakResidentSpace path (.quantumSystems dimension) =
      ctx.residentSpace (.quantumSystems dimension) := by
  apply Nat.le_antisymm
  · have bounded := resident_le ctx N sameWires path (.quantumSystems dimension)
    simpa only [Sampler.Retained.additionalSpace, SpacePool.ofShape, Pi.add_apply,
      Nat.add_zero] using bounded
  · exact Circuit.residentSpace_le_peak_of_visited (code ctx N sameWires) path ctx
      (initial_visited ctx N sameWires path) (.quantumSystems dimension)

/-- The supplied actual bank, including its multiplier auxiliary,
has exactly four words of qubits. -/
theorem quantum_peak_dimension
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (path : (code ctx N sameWires).Path) (dimension : ℕ+) :
    (code ctx N sameWires).peakResidentSpace path (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then 4 * modulusBits N else 0 := by
  rw [quantum_peak_eq, RuntimeCtx.residentSpace_quantumSystems,
    layout_dimensionCount_eq_count_wires, RuntimeCtx.quantumLayout_wires, sameWires,
    ← layout_dimensionCount_eq_count_wires, NativeQuantum.runtimeLayout_dimensionCount]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration
