/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Readout
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Store

/-!
# The original base inside the complete borrowed observation

The sampler's borrowed classical interface contains exactly the original
canonical-residue cell. Its structural read remains the first component
under the actual owned-register marker, packed result, and every individual
measurement cell. The proofs concern arbitrary existing stores, including
stores with noninitial measurement values.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling

noncomputable section

open QuantumAlg.Execution

private abbrev resultFrame (t width : Nat) : RuntimeCtx .quantum :=
  Sampling.Framed.resultContext (pre width) (pre_quantumWires width) t width

private def resultBase (t width : Nat) :
    CInputRef (resultFrame t width) (.canonicalResidue width) :=
  (CInputRef.storage (preparedBase t width)).underRetained
    (prepared t width).canonicalFreshKey (.bits t)
    (prepared t width).canonicalFreshKey_fresh

private def measuredBase (t width : Nat) : (count : Nat) →
    CStorageRef (MeasurementCells.context (resultFrame t width) 2 count) (.canonicalResidue width)
  | 0 => (preparedBase t width).underRetained
      (prepared t width).canonicalFreshKey (.bits t)
      (prepared t width).canonicalFreshKey_fresh
  | count + 1 => (measuredBase t width count).underRetained
      (MeasurementCells.context (resultFrame t width) 2 count).canonicalFreshKey (.finite 2)
      (MeasurementCells.context (resultFrame t width) 2 count).canonicalFreshKey_fresh

private theorem measuredBase_input (t width count : Nat) :
    MeasurementCells.liftInput 2 (resultBase t width) count =
      .storage (measuredBase t width count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [MeasurementCells.liftInput, ih]
      rfl

private theorem measuredBorrowedShape (t width count : Nat) :
    (MeasurementCells.context (resultFrame t width) 2 count).borrowedClassicalShape =
      .product (.canonicalResidue width) .unit := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

private theorem measuredBorrowedRead (t width count : Nat)
    (store : Store (MeasurementCells.context (resultFrame t width) 2 count)) :
    Equiv.cast (congrArg CShape.Value (measuredBorrowedShape t width count))
        store.readBorrowedClassical =
      .product (store.read (MeasurementCells.liftInput 2 (resultBase t width) count)) .unit := by
  rw [measuredBase_input]
  induction count with
  | zero => rfl
  | succ count ih =>
      let earlier : Store (MeasurementCells.context (resultFrame t width) 2 count) :=
        ⟨store.cells.2⟩
      exact ih earlier

/-- The initial complete borrowed observation reads precisely the original base. -/
theorem input_borrowedRead (width : Nat) (store : Store (pre width)) :
    store.readBorrowedClassical = .product (store.read (baseSourceRef width)) .unit := rfl

/-- The same original base is the sole value in the transported final borrowed observation. -/
theorem sampling_borrowedRead {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    (store : Store (post t width)) :
    (code A).borrowedClassicalValueTransport store.readBorrowedClassical =
      .product (store.read (baseRef t width)) .unit :=
  measuredBorrowedRead t width t store

/-- Equality of the actual borrowed interface entails equality of the actual original-base read. -/
theorem base_read_of_borrowed_eq {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    (final : Store (post t width)) (initial : Store (pre width))
    (same : (code A).borrowedClassicalValueTransport final.readBorrowedClassical =
      initial.readBorrowedClassical) :
    final.read (baseRef t width) = initial.read (baseSourceRef width) := by
  rw [sampling_borrowedRead, input_borrowedRead] at same
  exact congrArg CShape.Value.first same

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling
