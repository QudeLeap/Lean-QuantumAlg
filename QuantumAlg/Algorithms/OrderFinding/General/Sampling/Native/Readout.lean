/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.General.Input
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Store

/-!
# The original canonical residue under source-sample allocations

The base used by recovery remains the caller's borrowed input cell. Fresh
qubits, a packed result and measured-bit cells only extend the structural
reference; their allocation never reconstructs the base value.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling

noncomputable section

open QuantumAlg.Execution

/-- The source register attached to the original borrowed classical input. -/
public abbrev prepared (t width : Nat) : RuntimeCtx .quantum :=
  Sampling.Native.Framed.preparedContext (pre width) (pre_quantumWires width) t width

/-- The original base beneath the newly owned quantum-register marker. -/
public def preparedBase (t width : Nat) :
    CStorageRef (prepared t width) (.canonicalResidue width) where
  key := baseKey
  role := .borrowedInput
  slot := .there .here

/-- Recovery can read the actual borrowed base beside the stored phase word. -/
public def baseRef (t width : Nat) :
    CInputRef (post t width) (.canonicalResidue width) :=
  MeasurementCells.liftInput 2
    ((CInputRef.storage (preparedBase t width)).underRetained
      (prepared t width).canonicalFreshKey (.bits t)
      (prepared t width).canonicalFreshKey_fresh) t

/-- The new source-register wires are disjoint from the classical-only input. -/
public theorem sourcePreparationDisjoint (t width : Nat) :
    List.Disjoint (Sampling.Native.runtimeLayout t width).identities
      (pre width).physicalIdx := by
  rw [RuntimeCtx.physicalIdx, pre_quantumWires width]
  exact List.disjoint_nil_right _

/-- Fresh quantum preparation keeps the original stored residue unchanged. -/
theorem preparedBase_read (t width : Nat) (store : Store (pre width)) :
    (store.pushOwnedLayout (pre width).canonicalFreshKey
      (Sampling.Native.runtimeLayout t width)
      (pre width).canonicalFreshKey_fresh (sourcePreparationDisjoint t width)).read
        (.storage (preparedBase t width)) = store.read (baseSourceRef width) := rfl

/-- Output allocation preserves the same canonical residue in the same cell. -/
theorem baseRef_read_allocated (t width : Nat)
    (store : Store (prepared t width)) :
    (MeasurementCells.pushStore 2 t
      (store.pushRetained (prepared t width).canonicalFreshKey (.bits t)
        (prepared t width).canonicalFreshKey_fresh)).read (baseRef t width) =
      store.read (.storage (preparedBase t width)) := by
  rw [baseRef, MeasurementCells.read_pushStore_liftInput,
    Store.read_pushRetained_underRetained]

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling
