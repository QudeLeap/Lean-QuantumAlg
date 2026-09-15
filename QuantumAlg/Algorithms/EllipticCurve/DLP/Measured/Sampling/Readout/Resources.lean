/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Resources
import all QuantumAlg.Core.Execution.Local.Cells.Resources
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Native resources of original sampling with existing terminal storage

Actual path equivalences preserve both the original quantum prefix and the
terminal Z instructions beside all existing finite cells and public points.
The budget includes original exponent preparation, four real conversions,
every measured point call, inverse QFT, and one Z event per exponent wire.
Arbitrary native durations retain the exact scalar execution path. Resident
and auxiliary peaks use the complete unchanged terminal context, including
all arithmetic, selector and measurement storage and both public point inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP ConcreteCircuitAccess GenericPointAddition.InPlace

private theorem cells_pool {ctx : RuntimeCtx .quantum} (code : Circuit ctx ctx)
    (supported : code.IsLocal) (dimension : ℕ+) (count : Nat)
    (path : (Circuit.underMeasurementCells code supported dimension count).Path) :
    (Circuit.underMeasurementCells code supported dimension count).resourcePool path =
      code.resourcePool
        ((Circuit.underMeasurementCellsPathEquiv code supported dimension count).symm path) := by
  simpa only [Equiv.apply_symm_apply] using
    Circuit.underMeasurementCells_resourcePool code supported dimension count
      ((Circuit.underMeasurementCellsPathEquiv code supported dimension count).symm path)

private theorem cells_depth {ctx : RuntimeCtx .quantum} (code : Circuit ctx ctx)
    (supported : code.IsLocal) (dimension : ℕ+) (count : Nat)
    (duration : Resource.Event .quantum → Nat)
    (path : (Circuit.underMeasurementCells code supported dimension count).Path) :
    (Circuit.underMeasurementCells code supported dimension count).depth duration path =
      code.depth duration
        ((Circuit.underMeasurementCellsPathEquiv code supported dimension count).symm path) := by
  simpa only [Equiv.apply_symm_apply] using
    Circuit.underMeasurementCells_depth code supported dimension count duration
      ((Circuit.underMeasurementCellsPathEquiv code supported dimension count).symm path)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E)

private def samplingReadoutOriginalPath
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingPrefix E fieldTail odd problem points).Path :=
  (Circuit.underMeasurementCellsPathEquiv (samplingPrefix E fieldTail odd problem points)
    (samplingPrefix_isLocal E fieldTail odd problem points) 2 (2 * orderWidth problem)).symm
    ((frameLocalPathEquiv _ (Circuit.underMeasurementCells_isLocal
      (samplingPrefix E fieldTail odd problem points)
      (samplingPrefix_isLocal E fieldTail odd problem points) 2 (2 * orderWidth problem))
      (PublicInput.frame E (orderWidth problem))
      (PublicInput.terminal_disjoint E (orderWidth problem))).symm path.1)

/-- The actual complete round charges every original quantum stage and every terminal Z event. -/
theorem samplingReadout_budget
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingReadout E fieldTail odd problem points).resourcePool path ≤
      (exponentPreparationCircuit problem).eventCost +
        (ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
          ResourcePool.scale (2 * orderWidth problem) (MeasuredPointAddition.events p.size)) +
        (exponentReadoutCircuit problem).eventCost +
        (2 * orderWidth problem) • ResourcePool.singleton (Circuit.zEvent 2) := by
  let source := samplingPrefix E fieldTail odd problem points
  let supported := samplingPrefix_isLocal E fieldTail odd problem points
  let cells := Circuit.underMeasurementCells source supported 2 (2 * orderWidth problem)
  let cellsLocal := Circuit.underMeasurementCells_isLocal source supported 2
    (2 * orderWidth problem)
  let framed := frameLocal cells cellsLocal (PublicInput.frame E (orderWidth problem))
    (PublicInput.terminal_disjoint E (orderWidth problem))
  change ResourcePool.ofList (framed.eventTrace path.1 ++
    (PublicInput.measurements E (orderWidth problem)).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  have first := (PublicInput.framed_pool cells cellsLocal
    (PublicInput.frame E (orderWidth problem))
    (PublicInput.terminal_disjoint E (orderWidth problem)) path.1).trans
      (cells_pool source supported 2 (2 * orderWidth problem) _)
  have last := (PublicInput.framed_pool (exponentMeasurements p (orderWidth problem))
    (Circuit.measurementSequence_isLocal _) (PublicInput.frame E (orderWidth problem))
    (PublicInput.terminal_disjoint E (orderWidth problem)) path.2).trans
      (QubitReadouts.measurement_resources (exponentMeasurementWires p (orderWidth problem))
        (exponentMeasurementWires_qubits p (orderWidth problem))
        (exponentMeasurementCells p (orderWidth problem)) _)
  exact add_le_add (first.le.trans (samplingPrefix_budget E fieldTail odd problem points _)) last.le

/-- Native durations preserve the same scalar path, followed by all actual sequential readouts. -/
theorem samplingReadout_duration (duration : Resource.Event .quantum → Nat)
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingReadout E fieldTail odd problem points).depth duration path =
      (exponentPreparationCircuit problem).evaluatedEventDepth duration +
        (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
          (Semantics.radixUnit p fieldTail.succ odd)).depth duration
            (samplingReadoutOriginalPath E fieldTail odd problem points path).1.2 +
        (exponentReadoutCircuit problem).evaluatedEventDepth duration +
        (2 * orderWidth problem) * duration (Circuit.zEvent 2) := by
  let source := samplingPrefix E fieldTail odd problem points
  let supported := samplingPrefix_isLocal E fieldTail odd problem points
  let cells := Circuit.underMeasurementCells source supported 2 (2 * orderWidth problem)
  let cellsLocal := Circuit.underMeasurementCells_isLocal source supported 2
    (2 * orderWidth problem)
  let framed := frameLocal cells cellsLocal (PublicInput.frame E (orderWidth problem))
    (PublicInput.terminal_disjoint E (orderWidth problem))
  change framed.depth duration path.1 +
    (PublicInput.measurements E (orderWidth problem)).depth duration path.2 = _
  have first := (PublicInput.framed_depth cells cellsLocal
    (PublicInput.frame E (orderWidth problem))
    (PublicInput.terminal_disjoint E (orderWidth problem)) duration path.1).trans
      ((cells_depth source supported 2 (2 * orderWidth problem) duration _).trans
        (samplingPrefix_duration E fieldTail odd problem points duration _))
  have last := (PublicInput.framed_depth (exponentMeasurements p (orderWidth problem))
    (Circuit.measurementSequence_isLocal _) (PublicInput.frame E (orderWidth problem))
    (PublicInput.terminal_disjoint E (orderWidth problem)) duration path.2).trans
      (PublicInput.measurement_duration p (orderWidth problem) duration _)
  exact congrArg₂ Nat.add first last

/-- Unit durations retain the original four-conversion and per-point depth allowance. -/
theorem samplingReadout_depth
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingReadout E fieldTail odd problem points).depth (fun _ => 1) path ≤
      (exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
        (4 * MAU.Multiplication.Gidney.eventBound p.size +
          (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size) +
        (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) +
        2 * orderWidth problem := by
  rw [samplingReadout_duration, Nat.mul_one]
  have scalar := Encoding.placedConvertedCascade_depth E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)
    (samplingReadoutOriginalPath E fieldTail odd problem points path).1.2
  rw [List.length_finRange] at scalar
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left scalar _) _) _

/-- The exact resident peak is the same complete terminal context on every actual path. -/
theorem samplingReadout_resident
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingReadout E fieldTail odd problem points).peakResidentSpace path =
      (PublicInput.terminal E (orderWidth problem)).residentSpace := by
  apply le_antisymm
  · exact Circuit.peakResidentSpace_le_of_visited _ path _ (by
      intro visited present
      exact (congrArg RuntimeCtx.residentSpace
        (samplingReadout_visited E fieldTail odd problem points path visited present)).le)
  · exact Circuit.input_residentSpace_le_peak _ path

/-- The exact auxiliary peak retains every original arithmetic and measurement-cell role. -/
theorem samplingReadout_auxiliary
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingReadout E fieldTail odd problem points).peakAuxiliarySpace path =
      (PublicInput.terminal E (orderWidth problem)).auxiliarySpace := by
  apply le_antisymm
  · exact Circuit.peakAuxiliarySpace_le_of_visited _ path _ (by
      intro visited present
      exact (congrArg RuntimeCtx.auxiliarySpace
        (samplingReadout_visited E fieldTail odd problem points path visited present)).le)
  · exact Circuit.input_auxiliarySpace_le_peak _ path

/-- All terminal result cells and both original public point values remain explicitly charged. -/
theorem samplingReadout_resident_exact
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingReadout E fieldTail odd problem points).peakResidentSpace path =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) +
          2 • SpacePool.ofShape (Canonical.Runtime.Context.PointShape E) := by
  rw [samplingReadout_resident, PublicInput.terminal, RuntimeCtx.residentSpace_disjointUnion,
    exponentMeasurementContext_resident, Allocation.after_resident, PublicInput.frame_resident]

/-- Public borrowed values add no auxiliary ownership to the unchanged retained workspace. -/
theorem samplingReadout_auxiliary_exact
    (path : (samplingReadout E fieldTail odd problem points).Path) :
    (samplingReadout E fieldTail odd problem points).peakAuxiliarySpace path =
      (2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) := by
  rw [samplingReadout_auxiliary, PublicInput.terminal, RuntimeCtx.auxiliarySpace_disjointUnion,
    exponentMeasurementContext_auxiliary, Allocation.after_auxiliary,
    PublicInput.frame_auxiliary, add_zero]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
