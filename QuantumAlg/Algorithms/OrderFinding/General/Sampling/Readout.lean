/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Sampling
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Store

/-!
# Read the original borrowed base after actual source sampling allocations

The modular base is an operand at the original borrowed storage identity.
The quantum-presence marker, packed result and individual Z-result cells
only extend the context. Structural references cross those extensions without
copying the base or introducing an uncharged conversion.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling

noncomputable section

open QuantumAlg.Execution

private abbrev prepared (t width : Nat) : RuntimeCtx .quantum :=
  Sampling.Framed.preparedContext (pre width) (pre_quantumWires width) t width

/-- The original base cell underneath the actual owned-register presence marker. -/
def preparedBase (t width : Nat) : CStorageRef (prepared t width) (.canonicalResidue width) where
  key := baseKey
  role := .borrowedInput
  slot := .there .here

/-- The actual borrowed base read by native recovery alongside the real packed sample. -/
def baseRef (t width : Nat) : CInputRef (post t width) (.canonicalResidue width) :=
  MeasurementCells.liftInput 2
    ((CInputRef.storage (preparedBase t width)).underRetained
      (prepared t width).canonicalFreshKey (.bits t)
      (prepared t width).canonicalFreshKey_fresh) t

/-- The owned-register preparation preserves the original actual operand value. -/
theorem preparedBase_read (t width : Nat) (store : Store (pre width)) :
    (store.pushOwnedLayout (pre width).canonicalFreshKey (Sampling.runtimeLayout t width)
      (pre width).canonicalFreshKey_fresh
      (Sampling.Framed.preparationDisjoint (pre width) (pre_quantumWires width) t width)).read
        (.storage (preparedBase t width)) = store.read (baseSourceRef width) := rfl

/-- The same packed-output and measurement-cell allocations keep reading the original base. -/
theorem baseRef_read_allocated (t width : Nat) (store : Store (prepared t width)) :
    (MeasurementCells.pushStore 2 t
      (store.pushRetained (prepared t width).canonicalFreshKey (.bits t)
        (prepared t width).canonicalFreshKey_fresh)).read (baseRef t width) =
      store.read (.storage (preparedBase t width)) := by
  rw [baseRef, MeasurementCells.read_pushStore_liftInput,
    Store.read_pushRetained_underRetained]

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling
