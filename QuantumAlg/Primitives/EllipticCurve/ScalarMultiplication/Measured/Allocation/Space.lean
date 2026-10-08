/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Resources
import all QuantumAlg.Core.Execution.Trace.Preparation
import all QuantumAlg.Core.Execution.Context.Union.Preparation.Resources

/-!
# Exact live space of the allocating measured scalar cascade

Initialization reaches the complete final bank monotonically through actual
preparations and retained-cell allocation. The body then retains that same bank.
Both actual peaks include the two input words, all supplied exponents, internal
selector, shared arithmetic work and every retained measurement-result cell.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredUncompute MAU.Inversion.SharedEEA

private theorem auxiliary_resident (modulus count : Nat)
    (path : (prepareAuxiliary modulus count).Path) :
    (prepareAuxiliary modulus count).peakResidentSpace path =
      ((InversePreparation.after modulus.size).disjointUnion
        (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)).residentSpace := by
  exact ContextUnion.prepareFramed_peakResidentSpace
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint modulus.size count)
    (InPlacePreparation.loadProgram modulus) path

private theorem auxiliary_auxiliary (modulus count : Nat)
    (path : (prepareAuxiliary modulus count).Path) :
    (prepareAuxiliary modulus count).peakAuxiliarySpace path =
      ((InversePreparation.after modulus.size).disjointUnion
        (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)).auxiliarySpace := by
  exact ContextUnion.prepareFramed_peakAuxiliarySpace
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint modulus.size count)
    (InPlacePreparation.loadProgram modulus) path

private theorem cells_resident (width count : Nat) (path : (allocateCells width count).Path) :
    (allocateCells width count).peakResidentSpace path =
      (withCells width count).residentSpace :=
  (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ path).trans
    (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm

private theorem cells_auxiliary (width count : Nat) (path : (allocateCells width count).Path) :
    (allocateCells width count).peakAuxiliarySpace path =
      (withCells width count).auxiliarySpace :=
  (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ path).trans
    (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm

private theorem selector_resident (width count : Nat) (path : (prepareSelector width count).Path) :
    (prepareSelector width count).peakResidentSpace path = (after width count).residentSpace :=
  Circuit.prepare_peakResidentSpace _ _ _ _ _ _

private theorem selector_auxiliary (width count : Nat) (path : (prepareSelector width count).Path) :
    (prepareSelector width count).peakAuxiliarySpace path = (after width count).auxiliarySpace :=
  Circuit.prepare_peakAuxiliarySpace _ _ _ _ _ _

private theorem auxiliary_le_cells_resident (width count : Nat) :
    ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)).residentSpace ≤
        (withCells width count).residentSpace := by
  rw [RuntimeCtx.residentSpace_disjointUnion, withCells,
    RuntimeCtx.residentSpace_disjointUnion, NumeratorMeasurement.context]
  exact fun axis => Nat.add_le_add_right
    (MeasurementCells.context_residentSpace_mono (InversePreparation.after width) 2
      (Nat.zero_le width) axis) _

private theorem auxiliary_le_cells_auxiliary (width count : Nat) :
    ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)).auxiliarySpace ≤
        (withCells width count).auxiliarySpace := by
  rw [RuntimeCtx.auxiliarySpace_disjointUnion, withCells,
    RuntimeCtx.auxiliarySpace_disjointUnion, NumeratorMeasurement.context]
  exact fun axis => Nat.add_le_add_right
    (MeasurementCells.context_auxiliarySpace_mono (InversePreparation.after width) 2
      (Nat.zero_le width) axis) _

private theorem cells_le_after_resident (width count : Nat) :
    (withCells width count).residentSpace ≤ (after width count).residentSpace := by
  change (withCells width count).residentSpace ≤
    SpacePool.ofQuantumLayout (indexedLayout width count) +
      (withCells width count).residentSpace
  exact fun axis => Nat.le_add_left _ _

private theorem cells_le_after_auxiliary (width count : Nat) :
    (withCells width count).auxiliarySpace ≤ (after width count).auxiliarySpace := by
  change (withCells width count).auxiliarySpace ≤
    SpacePool.ofQuantumLayout (indexedLayout width count) +
      (withCells width count).auxiliarySpace
  exact fun axis => Nat.le_add_left _ _

/-- The actually allocated final context has the independent complete resident capacity. -/
theorem after_resident (width count : Nat) :
    (after width count).residentSpace = readySpace width count :=
  (ContextPermutation.resident_space (body_entries width count)).symm.trans
    (readyContext_resident_exact width count)

/-- The actually allocated final context retains the original fixed auxiliary roles. -/
theorem after_auxiliary (width count : Nat) :
    (after width count).auxiliarySpace = readySpace width count :=
  (ContextPermutation.auxiliary_space (body_entries width count)).symm.trans
    (readyContext_auxiliary_exact width count)

/-- Actual initialization reaches the complete final resident peak without another live bank. -/
theorem initialize_resident (modulus count : Nat) (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).peakResidentSpace path = readySpace modulus.size count := by
  refine (Circuit.peakResidentSpace_seq (prepareAuxiliary modulus count)
    (.seq (allocateCells modulus.size count) (prepareSelector modulus.size count)) path).trans ?_
  have inner := Circuit.peakResidentSpace_seq (allocateCells modulus.size count)
    (prepareSelector modulus.size count) path.2
  rw [inner, auxiliary_resident, cells_resident, selector_resident,
    SpacePool.max_eq_right (cells_le_after_resident modulus.size count),
    SpacePool.max_eq_right ((auxiliary_le_cells_resident modulus.size count).trans
      (cells_le_after_resident modulus.size count)), after_resident]

/-- The initialization auxiliary peak is derived from those same actual visited contexts. -/
theorem initialize_auxiliary (modulus count : Nat) (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).peakAuxiliarySpace path = readySpace modulus.size count := by
  refine (Circuit.peakAuxiliarySpace_seq (prepareAuxiliary modulus count)
    (.seq (allocateCells modulus.size count) (prepareSelector modulus.size count)) path).trans ?_
  have inner := Circuit.peakAuxiliarySpace_seq (allocateCells modulus.size count)
    (prepareSelector modulus.size count) path.2
  rw [inner, auxiliary_auxiliary, cells_auxiliary, selector_auxiliary,
    SpacePool.max_eq_right (cells_le_after_auxiliary modulus.size count),
    SpacePool.max_eq_right ((auxiliary_le_cells_auxiliary modulus.size count).trans
      (cells_le_after_auxiliary modulus.size count)), after_auxiliary]

/-- The complete allocating circuit attains the independently prescribed resident space. -/
theorem circuit_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (circuit E points order).Path) :
    (circuit E points order).peakResidentSpace path = readySpace p.size count := by
  refine (Circuit.peakResidentSpace_seq (initializeWork p count)
    (placedCascade E points order) path).trans ?_
  rw [initialize_resident, placedCascade_resident]
  exact SpacePool.max_eq_right le_rfl

/-- The whole actual allocating circuit has the same proved fixed-role auxiliary peak. -/
theorem circuit_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (circuit E points order).Path) :
    (circuit E points order).peakAuxiliarySpace path = readySpace p.size count := by
  refine (Circuit.peakAuxiliarySpace_seq (initializeWork p count)
    (placedCascade E points order) path).trans ?_
  rw [initialize_auxiliary, placedCascade_auxiliary]
  exact SpacePool.max_eq_right le_rfl

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
