/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Space
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Retained Shor phase capacity and actual quantum-round scratch

The packed phase word and its finite measurement cells occupy exactly twice
the phase width. The real reset adds one temporary classical bit. All bounds
come from the actual retain sequence and quantum round and preserve every
incoming dimension-indexed quantum coordinate.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage

noncomputable section

open Execution

variable (ctx : RuntimeCtx .quantum) (N : Nat)

private theorem binaryCapacity : Nat.clog 2 2 = 1 := by decide

/-- Independent capacity of the retained packed and individual phase results. -/
def resultSpace : SpacePool .quantum := SpacePool.ofShape (.bits (2 * phaseBits N))

/-- Independent allowance also includes the actual temporary reset cell. -/
def additionalSpace : SpacePool .quantum := SpacePool.ofShape (.bits (2 * phaseBits N + 1))

theorem context_resident :
    (context ctx N).residentSpace = ctx.residentSpace + resultSpace N := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [context, MeasurementCells.context_residentSpace, resultContext,
      resultSpace, SpacePool.ofShape, binaryCapacity]; omega

theorem context_auxiliary :
    (context ctx N).auxiliarySpace = ctx.auxiliarySpace + resultSpace N := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [context, MeasurementCells.context_auxiliarySpace, resultContext,
      resultSpace, SpacePool.ofShape, binaryCapacity]; omega

private theorem allocation_resident_le (path : (allocate ctx N).Path) :
    (allocate ctx N).peakResidentSpace path ≤ (context ctx N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (Circuit.retain ctx ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (MeasurementCells.allocate (resultContext ctx N) 2 (phaseBits N)) path).le.trans ?_
  apply SpacePool.max_le
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rcases List.mem_cons.mp present with same | same
    · subst frame
      rw [context_resident]
      exact fun _ => Nat.le_add_right _ _
    · have sameFrame := List.mem_singleton.mp same
      subst frame
      exact MeasurementCells.context_residentSpace_mono (resultContext ctx N) 2 (Nat.zero_le _)
  · exact MeasurementCells.allocate_peakResidentSpace (resultContext ctx N) 2 (phaseBits N) path.2

private theorem allocation_auxiliary_le (path : (allocate ctx N).Path) :
    (allocate ctx N).peakAuxiliarySpace path ≤ (context ctx N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Circuit.retain ctx ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (MeasurementCells.allocate (resultContext ctx N) 2 (phaseBits N)) path).le.trans ?_
  apply SpacePool.max_le
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rcases List.mem_cons.mp present with same | same
    · subst frame
      rw [context_auxiliary]
      exact fun _ => Nat.le_add_right _ _
    · have sameFrame := List.mem_singleton.mp same
      subst frame
      exact MeasurementCells.context_auxiliarySpace_mono (resultContext ctx N) 2 (Nat.zero_le _)
  · exact MeasurementCells.allocate_peakAuxiliarySpace (resultContext ctx N) 2 (phaseBits N) path.2

private theorem resident_budget :
    SpacePool.ofShape (.finite 2) + (context ctx N).residentSpace =
      ctx.residentSpace + additionalSpace N := by
  rw [context_resident]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp [resultSpace, additionalSpace, SpacePool.ofShape, binaryCapacity]; omega

private theorem auxiliary_budget :
    SpacePool.ofShape (.finite 2) + (context ctx N).auxiliarySpace =
      ctx.auxiliarySpace + additionalSpace N := by
  rw [context_auxiliary]
  apply SpacePool.ext
  intro axis
  cases axis <;> simp [resultSpace, additionalSpace, SpacePool.ofShape, binaryCapacity]; omega

/-- Actual allocation and the complete reset/reload round fit the explicit resident allowance. -/
theorem resident_le (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (round ctx N sameWires parameter).Path) :
    (round ctx N sameWires parameter).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace N := by
  refine (Circuit.peakResidentSpace_seq (allocate ctx N)
    (NativeRound.code N ((quantumWires ctx N).trans sameWires)
      (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N)) path).le.trans ?_
  rw [← resident_budget]
  exact SpacePool.max_le
    ((allocation_resident_le ctx N path.1).trans (fun _ => Nat.le_add_left _ _))
    (NativeRound.resident_le N _ _ _ _ path.2)

/-- The same visited contexts bound auxiliary space without changing incoming storage roles. -/
theorem auxiliary_le (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (round ctx N sameWires parameter).Path) :
    (round ctx N sameWires parameter).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace N := by
  refine (Circuit.peakAuxiliarySpace_seq (allocate ctx N)
    (NativeRound.code N ((quantumWires ctx N).trans sameWires)
      (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N)) path).le.trans ?_
  rw [← auxiliary_budget]
  exact SpacePool.max_le
    ((allocation_auxiliary_le ctx N path.1).trans (fun _ => Nat.le_add_left _ _))
    (NativeRound.auxiliary_le N _ _ _ _ path.2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage
