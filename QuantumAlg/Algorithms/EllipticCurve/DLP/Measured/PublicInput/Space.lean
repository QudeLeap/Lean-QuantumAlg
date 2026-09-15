/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Run.Space
import all QuantumAlg.Core.Execution.Trace.Preparation

/-!
# Exact live space of the exponent run with both original public inputs

The complete original arithmetic and terminal contexts are reached by their
actual preparations and retained allocations. Both borrowed public point
values remain resident throughout. They contribute their original point
shapes to resident input space and introduce no auxiliary ownership role.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private theorem cells_resident : ∀ path : (allocateCells E exponentWidth).Path,
    (allocateCells E exponentWidth).peakResidentSpace path =
      (withCells E exponentWidth).residentSpace := by
  apply allocateCells_property E exponentWidth
    (fun _ post code => ∀ path, code.peakResidentSpace path = post.residentSpace)
  intro resident separate path
  exact (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ path).trans
    (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm

private theorem cells_auxiliary : ∀ path : (allocateCells E exponentWidth).Path,
    (allocateCells E exponentWidth).peakAuxiliarySpace path =
      (withCells E exponentWidth).auxiliarySpace := by
  apply allocateCells_property E exponentWidth
    (fun _ post code => ∀ path, code.peakAuxiliarySpace path = post.auxiliarySpace)
  intro resident separate path
  exact (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ path).trans
    (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm

private theorem initialization_resident (path : (initializeWork E exponentWidth).Path) :
    (initializeWork E exponentWidth).peakResidentSpace path =
      (after E exponentWidth).residentSpace := by
  have prepared : (prepareAuxiliary E exponentWidth).peakResidentSpace path.1 =
      (withAuxiliary E exponentWidth).residentSpace :=
    Circuit.prepare_peakResidentSpace _ _ _ _ _ _ _
  have selected : (prepareSelector E exponentWidth).peakResidentSpace path.2.2 =
      (after E exponentWidth).residentSpace :=
    Circuit.prepare_peakResidentSpace _ _ _ _ _ _ _
  have firstBound := (Circuit.input_residentSpace_le_peak
    (allocateCells E exponentWidth) path.2.1).trans_eq (cells_resident E exponentWidth path.2.1)
  have lastBound := (Circuit.input_residentSpace_le_peak
    (prepareSelector E exponentWidth) path.2.2).trans_eq selected
  have inner := (Circuit.peakResidentSpace_seq (allocateCells E exponentWidth)
    (prepareSelector E exponentWidth) path.2).trans
      ((congrArg₂ SpacePool.max (cells_resident E exponentWidth path.2.1) selected).trans
        (SpacePool.max_eq_right lastBound))
  exact (Circuit.peakResidentSpace_seq (prepareAuxiliary E exponentWidth)
    ((allocateCells E exponentWidth).seq (prepareSelector E exponentWidth)) path).trans
      ((congrArg₂ SpacePool.max prepared inner).trans
        (SpacePool.max_eq_right (firstBound.trans lastBound)))

private theorem initialization_auxiliary (path : (initializeWork E exponentWidth).Path) :
    (initializeWork E exponentWidth).peakAuxiliarySpace path =
      (after E exponentWidth).auxiliarySpace := by
  have prepared : (prepareAuxiliary E exponentWidth).peakAuxiliarySpace path.1 =
      (withAuxiliary E exponentWidth).auxiliarySpace :=
    Circuit.prepare_peakAuxiliarySpace _ _ _ _ _ _ _
  have selected : (prepareSelector E exponentWidth).peakAuxiliarySpace path.2.2 =
      (after E exponentWidth).auxiliarySpace :=
    Circuit.prepare_peakAuxiliarySpace _ _ _ _ _ _ _
  have firstBound := (Circuit.input_auxiliarySpace_le_peak
    (allocateCells E exponentWidth) path.2.1).trans_eq (cells_auxiliary E exponentWidth path.2.1)
  have lastBound := (Circuit.input_auxiliarySpace_le_peak
    (prepareSelector E exponentWidth) path.2.2).trans_eq selected
  have inner := (Circuit.peakAuxiliarySpace_seq (allocateCells E exponentWidth)
    (prepareSelector E exponentWidth) path.2).trans
      ((congrArg₂ SpacePool.max (cells_auxiliary E exponentWidth path.2.1) selected).trans
        (SpacePool.max_eq_right lastBound))
  exact (Circuit.peakAuxiliarySpace_seq (prepareAuxiliary E exponentWidth)
    ((allocateCells E exponentWidth).seq (prepareSelector E exponentWidth)) path).trans
      ((congrArg₂ SpacePool.max prepared inner).trans
        (SpacePool.max_eq_right (firstBound.trans lastBound)))

variable [Fact p.Prime]

private theorem prefix_resident (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).peakResidentSpace path =
      (after E (orderWidth problem)).residentSpace := by
  let width := orderWidth problem
  let prepared := frameLocal (beforeExponentPreparation p problem) trivial
    (frame E width) (before_disjoint E width)
  let scalar := frameLocal
    (Encoding.placedConvertedCascade E points (List.finRange (2 * width))
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))
    (Encoding.placedConvertedCascade_isLocal E points (List.finRange (2 * width))
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))
    (frame E width) (after_disjoint E width)
  let readout := frameLocal (afterExponentReadout p problem) trivial
    (frame E width) (after_disjoint E width)
  have firstBound := (Circuit.input_residentSpace_le_peak (initializeWork E width)
    path.1.2.1).trans_eq (initialization_resident E width path.1.2.1)
  have first : prepared.peakResidentSpace path.1.1 = (before E width).residentSpace :=
    (frameLocal_peakResidentSpace _ _ _ _ _).trans
      (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm
  have middle : scalar.peakResidentSpace path.1.2.2 = (after E width).residentSpace :=
    (frameLocal_peakResidentSpace _ _ _ _ _).trans
      (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm
  have last : readout.peakResidentSpace path.2 = (after E width).residentSpace :=
    (frameLocal_peakResidentSpace _ _ _ _ _).trans
      (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm
  have scalarPeak := (Circuit.peakResidentSpace_seq (initializeWork E width) scalar
    path.1.2).trans
      ((congrArg₂ SpacePool.max (initialization_resident E width path.1.2.1) middle).trans
        (SpacePool.max_eq_right le_rfl))
  have earlier := (Circuit.peakResidentSpace_seq prepared
    ((initializeWork E width).seq scalar) path.1).trans
      ((congrArg₂ SpacePool.max first scalarPeak).trans (SpacePool.max_eq_right firstBound))
  exact (Circuit.peakResidentSpace_seq
    (prepared.seq ((initializeWork E width).seq scalar)) readout path).trans
      ((congrArg₂ SpacePool.max earlier last).trans (SpacePool.max_eq_right le_rfl))

private theorem prefix_auxiliary (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).peakAuxiliarySpace path =
      (after E (orderWidth problem)).auxiliarySpace := by
  let width := orderWidth problem
  let prepared := frameLocal (beforeExponentPreparation p problem) trivial
    (frame E width) (before_disjoint E width)
  let scalar := frameLocal
    (Encoding.placedConvertedCascade E points (List.finRange (2 * width))
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))
    (Encoding.placedConvertedCascade_isLocal E points (List.finRange (2 * width))
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))
    (frame E width) (after_disjoint E width)
  let readout := frameLocal (afterExponentReadout p problem) trivial
    (frame E width) (after_disjoint E width)
  have firstBound := (Circuit.input_auxiliarySpace_le_peak (initializeWork E width)
    path.1.2.1).trans_eq (initialization_auxiliary E width path.1.2.1)
  have first : prepared.peakAuxiliarySpace path.1.1 = (before E width).auxiliarySpace :=
    (frameLocal_peakAuxiliarySpace _ _ _ _ _).trans
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm
  have middle : scalar.peakAuxiliarySpace path.1.2.2 = (after E width).auxiliarySpace :=
    (frameLocal_peakAuxiliarySpace _ _ _ _ _).trans
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm
  have last : readout.peakAuxiliarySpace path.2 = (after E width).auxiliarySpace :=
    (frameLocal_peakAuxiliarySpace _ _ _ _ _).trans
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm
  have scalarPeak := (Circuit.peakAuxiliarySpace_seq (initializeWork E width) scalar
    path.1.2).trans
      ((congrArg₂ SpacePool.max (initialization_auxiliary E width path.1.2.1) middle).trans
        (SpacePool.max_eq_right le_rfl))
  have earlier := (Circuit.peakAuxiliarySpace_seq prepared
    ((initializeWork E width).seq scalar) path.1).trans
      ((congrArg₂ SpacePool.max first scalarPeak).trans (SpacePool.max_eq_right firstBound))
  exact (Circuit.peakAuxiliarySpace_seq
    (prepared.seq ((initializeWork E width).seq scalar)) readout path).trans
      ((congrArg₂ SpacePool.max earlier last).trans (SpacePool.max_eq_right le_rfl))

/-- The real resident peak adds exactly both original borrowed point values to the old peak. -/
theorem exponentRun_resident (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.peakResidentSpace path =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) +
          2 • SpacePool.ofShape (Canonical.Runtime.Context.PointShape E) := by
  have finalSpace : (terminal E (orderWidth problem)).residentSpace =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) +
          2 • SpacePool.ofShape (Canonical.Runtime.Context.PointShape E) := by
    rw [terminal, RuntimeCtx.residentSpace_disjointUnion,
      exponentMeasurementContext_resident, Allocation.after_resident, frame_resident]
  have cells : (allocateTerminal E (orderWidth problem)).peakResidentSpace path.1.2 =
      (terminal E (orderWidth problem)).residentSpace :=
    (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ _).trans
      (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm
  have measured : (measurements E (orderWidth problem)).peakResidentSpace path.2 =
      (terminal E (orderWidth problem)).residentSpace :=
    (frameLocal_peakResidentSpace _ _ _ _ _).trans
      (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm
  have bounded := (Circuit.input_residentSpace_le_peak
    (allocateTerminal E (orderWidth problem)) path.1.2).trans_eq cells
  have earlier := (Circuit.peakResidentSpace_seq
    (preMeasurement E fieldTail odd problem points) (allocateTerminal E (orderWidth problem))
    path.1).trans
      ((congrArg₂ SpacePool.max (prefix_resident E fieldTail odd problem points path.1.1)
        cells).trans (SpacePool.max_eq_right bounded))
  exact (Circuit.peakResidentSpace_seq
    ((preMeasurement E fieldTail odd problem points).seq
      (allocateTerminal E (orderWidth problem))) (measurements E (orderWidth problem)) path).trans
        (((congrArg₂ SpacePool.max earlier measured).trans
          (SpacePool.max_eq_right le_rfl)).trans finalSpace)

/-- Borrowed public inputs add no auxiliary role to the complete original retained workspace. -/
theorem exponentRun_auxiliary (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.peakAuxiliarySpace path =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) := by
  have finalSpace : (terminal E (orderWidth problem)).auxiliarySpace =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) := by
    rw [terminal, RuntimeCtx.auxiliarySpace_disjointUnion,
      exponentMeasurementContext_auxiliary, Allocation.after_auxiliary, frame_auxiliary, add_zero]
  have cells : (allocateTerminal E (orderWidth problem)).peakAuxiliarySpace path.1.2 =
      (terminal E (orderWidth problem)).auxiliarySpace :=
    (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ _).trans
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm
  have measured : (measurements E (orderWidth problem)).peakAuxiliarySpace path.2 =
      (terminal E (orderWidth problem)).auxiliarySpace :=
    (frameLocal_peakAuxiliarySpace _ _ _ _ _).trans
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm
  have bounded := (Circuit.input_auxiliarySpace_le_peak
    (allocateTerminal E (orderWidth problem)) path.1.2).trans_eq cells
  have earlier := (Circuit.peakAuxiliarySpace_seq
    (preMeasurement E fieldTail odd problem points) (allocateTerminal E (orderWidth problem))
    path.1).trans
      ((congrArg₂ SpacePool.max (prefix_auxiliary E fieldTail odd problem points path.1.1)
        cells).trans (SpacePool.max_eq_right bounded))
  exact (Circuit.peakAuxiliarySpace_seq
    ((preMeasurement E fieldTail odd problem points).seq
      (allocateTerminal E (orderWidth problem))) (measurements E (orderWidth problem)) path).trans
        (((congrArg₂ SpacePool.max earlier measured).trans
          (SpacePool.max_eq_right le_rfl)).trans finalSpace)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
