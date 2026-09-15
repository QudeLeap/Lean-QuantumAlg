/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Run
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Program.Space
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Complete actual exponent-run peak space

The original preparation, measured scalar execution, and inverse QFT reach
the established complete scalar space. Actual terminal allocation retains
one additional finite-two classical cell per exponent bit. All subsequent
measurements use that complete final context. Its full resident and auxiliary
space is both an upper bound and an actually visited boundary of every run.

The equalities retain all native dimension coordinates. Finite result cells
contribute classical bits; they do not add quantum systems or replace the
already retained intermediate arithmetic measurement results.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP

private theorem exponentMeasurements_resident_le (modulus exponentWidth : Nat)
    (path : (exponentMeasurements modulus exponentWidth).Path) :
    (exponentMeasurements modulus exponentWidth).peakResidentSpace path ≤
      (exponentMeasurementContext modulus exponentWidth).residentSpace := by
  change (Circuit.measurementSequence (QubitReadouts.readouts
    (exponentMeasurementWires modulus exponentWidth)
    (exponentMeasurementWires_qubits modulus exponentWidth)
    (exponentMeasurementCells modulus exponentWidth))).Path at path
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  change frame ∈ (Circuit.measurementSequence (QubitReadouts.readouts
    (exponentMeasurementWires modulus exponentWidth)
    (exponentMeasurementWires_qubits modulus exponentWidth)
    (exponentMeasurementCells modulus exponentWidth))).visitedContexts path at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  exact (congrArg RuntimeCtx.residentSpace (List.eq_of_mem_replicate present)).le

private theorem exponentMeasurements_auxiliary_le (modulus exponentWidth : Nat)
    (path : (exponentMeasurements modulus exponentWidth).Path) :
    (exponentMeasurements modulus exponentWidth).peakAuxiliarySpace path ≤
      (exponentMeasurementContext modulus exponentWidth).auxiliarySpace := by
  change (Circuit.measurementSequence (QubitReadouts.readouts
    (exponentMeasurementWires modulus exponentWidth)
    (exponentMeasurementWires_qubits modulus exponentWidth)
    (exponentMeasurementCells modulus exponentWidth))).Path at path
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  change frame ∈ (Circuit.measurementSequence (QubitReadouts.readouts
    (exponentMeasurementWires modulus exponentWidth)
    (exponentMeasurementWires_qubits modulus exponentWidth)
    (exponentMeasurementCells modulus exponentWidth))).visitedContexts path at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  exact (congrArg RuntimeCtx.auxiliarySpace (List.eq_of_mem_replicate present)).le

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Actual resident peak includes every original system and every retained terminal result cell. -/
theorem exponentRun_resident (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.peakResidentSpace path =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) := by
  have finalSpace := exponentMeasurementContext_resident p (orderWidth problem)
  rw [after_resident] at finalSpace
  rw [← finalSpace]
  refine le_antisymm ?_ (Circuit.output_residentSpace_le_peak _ path)
  change ((preMeasurement E fieldTail odd problem points).Path ×
    (exponentMeasurementAllocate p (orderWidth problem)).Path) ×
      (exponentMeasurements p (orderWidth problem)).Path at path
  change (((preMeasurement E fieldTail odd problem points).seq
    (exponentMeasurementAllocate p (orderWidth problem))).seq
      (exponentMeasurements p (orderWidth problem))).peakResidentSpace path ≤ _
  rw [Circuit.peakResidentSpace_seq, Circuit.peakResidentSpace_seq, preMeasurement_resident]
  refine SpacePool.max_le (SpacePool.max_le ?_ ?_) ?_
  · rw [← after_resident]
    exact MeasurementCells.context_residentSpace_mono _ 2 (Nat.zero_le (2 * orderWidth problem))
  · exact MeasurementCells.allocate_peakResidentSpace _ 2 (2 * orderWidth problem) path.1.2
  · exact exponentMeasurements_resident_le p (orderWidth problem) path.2

/-- Actual auxiliary peak charges the same terminal cells in their retained classical roles. -/
theorem exponentRun_auxiliary (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.peakAuxiliarySpace path =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) := by
  have finalSpace := exponentMeasurementContext_auxiliary p (orderWidth problem)
  rw [after_auxiliary] at finalSpace
  rw [← finalSpace]
  refine le_antisymm ?_ (Circuit.output_auxiliarySpace_le_peak _ path)
  change ((preMeasurement E fieldTail odd problem points).Path ×
    (exponentMeasurementAllocate p (orderWidth problem)).Path) ×
      (exponentMeasurements p (orderWidth problem)).Path at path
  change (((preMeasurement E fieldTail odd problem points).seq
    (exponentMeasurementAllocate p (orderWidth problem))).seq
      (exponentMeasurements p (orderWidth problem))).peakAuxiliarySpace path ≤ _
  rw [Circuit.peakAuxiliarySpace_seq, Circuit.peakAuxiliarySpace_seq, preMeasurement_auxiliary]
  refine SpacePool.max_le (SpacePool.max_le ?_ ?_) ?_
  · rw [← after_auxiliary]
    exact MeasurementCells.context_auxiliarySpace_mono _ 2 (Nat.zero_le (2 * orderWidth problem))
  · exact MeasurementCells.allocate_peakAuxiliarySpace _ 2 (2 * orderWidth problem) path.1.2
  · exact exponentMeasurements_auxiliary_le p (orderWidth problem) path.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
