/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Resources
import all QuantumAlg.Core.Execution.Trace.Preparation
import all QuantumAlg.Core.Execution.Context.Union.Preparation.Resources

/-!
# Exact live space of the allocating measured point-addition circuit

Initialization reaches the complete final bank monotonically through actual
preparations and retained-cell allocation. The body then retains that same bank.
Both actual peaks include the two input words, supplied control, internal
selector, shared arithmetic work and every retained measurement-result cell.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution MeasuredUncompute MAU.Inversion.SharedEEA

private lemma auxiliary_resident (modulus : Nat) (path : (prepareAuxiliary modulus).Path) :
    (prepareAuxiliary modulus).peakResidentSpace path =
      ((InversePreparation.after modulus.size).disjointUnion
        (InPlaceControlled.controlContext modulus.size)
        (auxiliary_disjoint_control modulus.size)).residentSpace := by
  exact ContextUnion.prepareFramed_peakResidentSpace
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint_control modulus.size)
    (InPlacePreparation.loadProgram modulus) path

private lemma auxiliary_auxiliary (modulus : Nat) (path : (prepareAuxiliary modulus).Path) :
    (prepareAuxiliary modulus).peakAuxiliarySpace path =
      ((InversePreparation.after modulus.size).disjointUnion
        (InPlaceControlled.controlContext modulus.size)
        (auxiliary_disjoint_control modulus.size)).auxiliarySpace := by
  exact ContextUnion.prepareFramed_peakAuxiliarySpace
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint_control modulus.size)
    (InPlacePreparation.loadProgram modulus) path

private lemma cells_resident (width : Nat) (path : (allocateCells width).Path) :
    (allocateCells width).peakResidentSpace path =
      (InPlaceControlled.context width).residentSpace :=
  (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ path).trans
    (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm

private lemma cells_auxiliary (width : Nat) (path : (allocateCells width).Path) :
    (allocateCells width).peakAuxiliarySpace path =
      (InPlaceControlled.context width).auxiliarySpace :=
  (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ path).trans
    (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm

private lemma selector_resident (width : Nat) (path : (prepareSelector width).Path) :
    (prepareSelector width).peakResidentSpace path = (after width).residentSpace :=
  Circuit.prepare_peakResidentSpace _ _ _ _ _ _

private lemma selector_auxiliary (width : Nat) (path : (prepareSelector width).Path) :
    (prepareSelector width).peakAuxiliarySpace path = (after width).auxiliarySpace :=
  Circuit.prepare_peakAuxiliarySpace _ _ _ _ _ _

private lemma auxiliary_le_cells_resident (width : Nat) :
    ((InversePreparation.after width).disjointUnion (InPlaceControlled.controlContext width)
      (auxiliary_disjoint_control width)).residentSpace ≤
        (InPlaceControlled.context width).residentSpace := by
  rw [RuntimeCtx.residentSpace_disjointUnion, InPlaceControlled.context,
    RuntimeCtx.residentSpace_disjointUnion]
  exact fun axis => Nat.add_le_add_right
    (MeasurementCells.context_residentSpace_mono (InversePreparation.after width) 2
      (Nat.zero_le width) axis) _

private lemma auxiliary_le_cells_auxiliary (width : Nat) :
    ((InversePreparation.after width).disjointUnion (InPlaceControlled.controlContext width)
      (auxiliary_disjoint_control width)).auxiliarySpace ≤
        (InPlaceControlled.context width).auxiliarySpace := by
  rw [RuntimeCtx.auxiliarySpace_disjointUnion, InPlaceControlled.context,
    RuntimeCtx.auxiliarySpace_disjointUnion]
  exact fun axis => Nat.add_le_add_right
    (MeasurementCells.context_auxiliarySpace_mono (InversePreparation.after width) 2
      (Nat.zero_le width) axis) _

private lemma cells_le_after_resident (width : Nat) :
    (InPlaceControlled.context width).residentSpace ≤ (after width).residentSpace := by
  change (InPlaceControlled.context width).residentSpace ≤
    SpacePool.ofQuantumLayout (selectorLayout width) +
      (InPlaceControlled.context width).residentSpace
  exact fun axis => Nat.le_add_left _ _

private lemma cells_le_after_auxiliary (width : Nat) :
    (InPlaceControlled.context width).auxiliarySpace ≤ (after width).auxiliarySpace := by
  change (InPlaceControlled.context width).auxiliarySpace ≤
    SpacePool.ofQuantumLayout (selectorLayout width) +
      (InPlaceControlled.context width).auxiliarySpace
  exact fun axis => Nat.le_add_left _ _

/-- The actually allocated final context has the independent complete resident capacity. -/
lemma after_resident (width : Nat) : (after width).residentSpace = space width :=
  (ContextPermutation.resident_space (body_entries width)).symm.trans (context_resident width)

/-- The actually allocated final context retains the original fixed auxiliary roles. -/
lemma after_auxiliary (width : Nat) : (after width).auxiliarySpace = space width :=
  (ContextPermutation.auxiliary_space (body_entries width)).symm.trans (context_auxiliary width)

/-- Actual initialization reaches the complete final resident peak without another live bank. -/
lemma initialize_resident (modulus : Nat) (path : (initializeWork modulus).Path) :
    (initializeWork modulus).peakResidentSpace path = space modulus.size := by
  refine (Circuit.peakResidentSpace_seq (prepareAuxiliary modulus)
    (.seq (allocateCells modulus.size) (prepareSelector modulus.size)) path).trans ?_
  have inner := Circuit.peakResidentSpace_seq (allocateCells modulus.size)
    (prepareSelector modulus.size) path.2
  rw [inner, auxiliary_resident, cells_resident, selector_resident,
    SpacePool.max_eq_right (cells_le_after_resident modulus.size),
    SpacePool.max_eq_right ((auxiliary_le_cells_resident modulus.size).trans
      (cells_le_after_resident modulus.size)), after_resident]

/-- The initialization auxiliary peak is derived from those same actual visited contexts. -/
lemma initialize_auxiliary (modulus : Nat) (path : (initializeWork modulus).Path) :
    (initializeWork modulus).peakAuxiliarySpace path = space modulus.size := by
  refine (Circuit.peakAuxiliarySpace_seq (prepareAuxiliary modulus)
    (.seq (allocateCells modulus.size) (prepareSelector modulus.size)) path).trans ?_
  have inner := Circuit.peakAuxiliarySpace_seq (allocateCells modulus.size)
    (prepareSelector modulus.size) path.2
  rw [inner, auxiliary_auxiliary, cells_auxiliary, selector_auxiliary,
    SpacePool.max_eq_right (cells_le_after_auxiliary modulus.size),
    SpacePool.max_eq_right ((auxiliary_le_cells_auxiliary modulus.size).trans
      (cells_le_after_auxiliary modulus.size)), after_auxiliary]

/-- The complete allocating circuit attains the independently prescribed resident space. -/
lemma circuit_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).peakResidentSpace path = space p.size := by
  refine (Circuit.peakResidentSpace_seq (initializeWork p) (placedBody E Q) path).trans ?_
  rw [initialize_resident, placedBody_resident]
  exact SpacePool.max_eq_right le_rfl

/-- The whole actual allocating circuit has the same proved fixed-role auxiliary peak. -/
lemma circuit_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).peakAuxiliarySpace path = space p.size := by
  refine (Circuit.peakAuxiliarySpace_seq (initializeWork p) (placedBody E Q) path).trans ?_
  rw [initialize_auxiliary, placedBody_auxiliary]
  exact SpacePool.max_eq_right le_rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
