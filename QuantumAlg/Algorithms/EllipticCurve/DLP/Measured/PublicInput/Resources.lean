/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Framing

/-!
# Actual exponent resources with the original public inputs resident

The original preparations, converted measured cascade, inverse QFT and final
measurements retain their native event budgets. Reassociating the context of
the original retained cells emits no event. Every bound is derived from the
actual framed instructions and their own paths, without a caller cost witness.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open MAU.Inversion.SharedEEA FiniteCyclicDLP ConcreteCircuitAccess GenericPointAddition.InPlace

private theorem inputTransport_property {pre next post : RuntimeCtx .quantum}
    (same : pre = next) (code : Circuit next post)
    (property : ∀ pre post, Circuit pre post → Prop) (holds : property next post code) :
    property pre post (Eq.mpr (congrArg (fun ctx => Circuit ctx post) same) code) := by
  cases same
  exact holds

private theorem outputTransport_property {pre post next : RuntimeCtx .quantum}
    (same : post = next) (code : Circuit pre next)
    (property : ∀ pre post, Circuit pre post → Prop) (holds : property pre next code) :
    property pre post (Eq.mpr (congrArg (fun ctx => Circuit pre ctx) same) code) := by
  cases same
  exact holds

private theorem framed_pool {pre post : RuntimeCtx .quantum} (code : Circuit pre post)
    (supported : code.IsLocal) (resident : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint pre resident)
    (path : (frameLocal code supported resident separate).Path) :
    (frameLocal code supported resident separate).resourcePool path =
      code.resourcePool ((frameLocalPathEquiv code supported resident separate).symm path) := by
  obtain ⟨original, rfl⟩ := (frameLocalPathEquiv code supported resident separate).surjective path
  rw [Equiv.symm_apply_apply]
  exact frameLocal_resourcePool code supported resident separate original

private theorem framed_depth {pre post : RuntimeCtx .quantum} (code : Circuit pre post)
    (supported : code.IsLocal) (resident : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint pre resident)
    (duration : Resource.Event .quantum → Nat)
    (path : (frameLocal code supported resident separate).Path) :
    (frameLocal code supported resident separate).depth duration path =
      code.depth duration ((frameLocalPathEquiv code supported resident separate).symm path) := by
  obtain ⟨original, rfl⟩ := (frameLocalPathEquiv code supported resident separate).surjective path
  rw [Equiv.symm_apply_apply]
  exact frameLocal_depth code supported resident separate duration original

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private theorem allocateCells_property
    (property : ∀ pre post : RuntimeCtx .quantum, Circuit pre post → Prop)
    (holds : ∀ (resident : RuntimeCtx .quantum)
      (separate : RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context p.size) resident),
      property _ _
        (MeasurementCells.allocateFramed (InversePreparation.after p.size) resident 2 p.size
          separate)) :
    property (withAuxiliary E exponentWidth) (withCells E exponentWidth)
      (allocateCells E exponentWidth) := by
  let expandedFrame := (Allocation.exponents p.size (2 * exponentWidth)).disjointUnion
    (frame E exponentWidth) (exponents_disjoint E exponentWidth)
  let complete := union_right_separate
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (numerator_disjoint E exponentWidth) (exponents_disjoint E exponentWidth)
  let original := MeasurementCells.original_disjoint (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  have first := union_assoc (InversePreparation.after p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))
    (auxiliary_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) original
  have last := union_assoc (NumeratorMeasurement.context p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) complete
  exact inputTransport_property first _ property
    (outputTransport_property last _ property (holds expandedFrame complete))

/-- Reassociating the original arithmetic cell allocator adds no native operation. -/
theorem allocateCells_eventTrace : ∀ path : (allocateCells E exponentWidth).Path,
    (allocateCells E exponentWidth).eventTrace path = [] := by
  apply allocateCells_property E exponentWidth
    (fun _ _ code => ∀ path, code.eventTrace path = [])
  intro resident separate
  exact MeasurementCells.allocateFramed_eventTrace _ resident _ _ separate

/-- Every original retain has zero event duration, for any supplied duration assignment. -/
theorem allocateCells_depth (duration : Resource.Event .quantum → Nat) :
    ∀ path : (allocateCells E exponentWidth).Path,
      (allocateCells E exponentWidth).depth duration path = 0 := by
  apply allocateCells_property E exponentWidth
    (fun _ _ code => ∀ path, code.depth duration path = 0)
  intro resident separate
  exact MeasurementCells.allocateFramed_depth _ resident _ _ separate duration

/-- Both original fixed preparations occur in their actual chronological positions. -/
theorem initializeWork_eventTrace (path : (initializeWork E exponentWidth).Path) :
    (initializeWork E exponentWidth).eventTrace path =
      [(InPlacePreparation.preparation p).event,
        (BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))).event] := by
  change [(InPlacePreparation.preparation p).event] ++
    ((allocateCells E exponentWidth).eventTrace path.2.1 ++
      [(BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))).event]) = _
  rw [allocateCells_eventTrace]
  rfl

/-- The original two charged preparations determine the exact initialization duration. -/
theorem initializeWork_depth (duration : Resource.Event .quantum → Nat)
    (path : (initializeWork E exponentWidth).Path) :
    (initializeWork E exponentWidth).depth duration path =
      duration (InPlacePreparation.preparation p).event +
        duration (BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))).event := by
  change duration (InPlacePreparation.preparation p).event +
    ((allocateCells E exponentWidth).depth duration path.2.1 +
      duration (BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth))).event) = _
  rw [allocateCells_depth, Nat.zero_add]

variable [Fact p.Prime]

/-- The complete framed prefix retains the original independent native event allowance. -/
theorem preMeasurement_budget (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).resourcePool path ≤
      (exponentPreparationCircuit problem).eventCost +
        Encoding.convertedEventBudget p (2 * orderWidth problem) (2 * orderWidth problem) +
          (exponentReadoutCircuit problem).eventCost := by
  let width := orderWidth problem
  let scalar := Encoding.placedConvertedCascade E points (List.finRange (2 * width))
    (Semantics.radixUnit p fieldTail.succ odd)
  let supported := Encoding.placedConvertedCascade_isLocal E points
    (List.finRange (2 * width)) (Semantics.radixUnit p fieldTail.succ odd)
  change ResourcePool.ofList
    (((frameLocal (beforeExponentPreparation p problem) trivial
        (frame E width) (before_disjoint E width)).eventTrace path.1.1 ++
      ((initializeWork E width).eventTrace path.1.2.1 ++
        (frameLocal scalar supported (frame E width) (after_disjoint E width)).eventTrace
          path.1.2.2)) ++
      (frameLocal (afterExponentReadout p problem) trivial
        (frame E width) (after_disjoint E width)).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  have initialized := congrArg ResourcePool.ofList
    (initializeWork_eventTrace E width path.1.2.1)
  have prepared := (framed_pool (beforeExponentPreparation p problem) trivial
    (frame E width) (before_disjoint E width) path.1.1).trans
      (beforeExponentCircuit_cost p width (exponentPreparationCircuit problem)
        (exponentPreparationCircuit_physical_idx problem) _)
  have readout := (framed_pool (afterExponentReadout p problem) trivial
    (frame E width) (after_disjoint E width) path.2).trans
      (afterExponentCircuit_cost p width (exponentReadoutCircuit problem)
        (exponentReadoutCircuit_physical_idx problem) _)
  have scalarBound := (framed_pool scalar supported (frame E width)
    (after_disjoint E width) path.1.2.2).le.trans
      (Encoding.placedConvertedCascade_budget E points (List.finRange (2 * width))
        (Semantics.radixUnit p fieldTail.succ odd) _)
  rw [List.length_finRange] at scalarBound
  exact ResourcePool.add_mono (ResourcePool.add_mono prepared.le
    (ResourcePool.add_mono initialized.le scalarBound)) readout.le

/-- The full actual exponent run charges every final Z in addition to the original prefix. -/
theorem exponentRun_budget (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.resourcePool path ≤
      (exponentPreparationCircuit problem).eventCost +
        Encoding.convertedEventBudget p (2 * orderWidth problem) (2 * orderWidth problem) +
          (exponentReadoutCircuit problem).eventCost +
            (2 * orderWidth problem) • ResourcePool.singleton (Circuit.zEvent 2) := by
  change ResourcePool.ofList
    (((preMeasurement E fieldTail odd problem points).eventTrace path.1.1 ++
      (allocateTerminal E (orderWidth problem)).eventTrace path.1.2) ++
      (measurements E (orderWidth problem)).eventTrace path.2) ≤ _
  have noEvents : (allocateTerminal E (orderWidth problem)).eventTrace path.1.2 = [] :=
    MeasurementCells.allocateFramed_eventTrace _ _ _ _ _ _
  rw [noEvents, List.append_nil, ResourcePool.ofList_append]
  have measured := (framed_pool (exponentMeasurements p (orderWidth problem))
    (Circuit.measurementSequence_isLocal _) (frame E (orderWidth problem))
    (terminal_disjoint E (orderWidth problem)) path.2).trans
      (QubitReadouts.measurement_resources _ _ _ _)
  exact ResourcePool.add_mono
    (preMeasurement_budget E fieldTail odd problem points path.1.1) measured.le

private def scalarOriginalPath (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd)).Path :=
  (frameLocalPathEquiv _ (Encoding.placedConvertedCascade_isLocal E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd))
    (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))).symm path.1.2.2

/-- Arbitrary native durations retain the original exponent programs and exact scalar path. -/
theorem preMeasurement_duration (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (duration : Resource.Event .quantum → Nat)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).depth duration path =
      (exponentPreparationCircuit problem).evaluatedEventDepth duration +
        (duration (InPlacePreparation.preparation p).event +
          duration (BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).event +
          (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
            (Semantics.radixUnit p fieldTail.succ odd)).depth duration
              (scalarOriginalPath E fieldTail odd problem points path)) +
        (exponentReadoutCircuit problem).evaluatedEventDepth duration := by
  let width := orderWidth problem
  let scalar := Encoding.placedConvertedCascade E points (List.finRange (2 * width))
    (Semantics.radixUnit p fieldTail.succ odd)
  let supported := Encoding.placedConvertedCascade_isLocal E points
    (List.finRange (2 * width)) (Semantics.radixUnit p fieldTail.succ odd)
  change (frameLocal (beforeExponentPreparation p problem) trivial
      (frame E width) (before_disjoint E width)).depth duration path.1.1 +
    ((initializeWork E width).depth duration path.1.2.1 +
      (frameLocal scalar supported (frame E width) (after_disjoint E width)).depth duration
        path.1.2.2) +
    (frameLocal (afterExponentReadout p problem) trivial
      (frame E width) (after_disjoint E width)).depth duration path.2 = _
  have prepared := (framed_depth (beforeExponentPreparation p problem) trivial
    (frame E width) (before_disjoint E width) duration path.1.1).trans
      (beforeExponentCircuit_depth p width (exponentPreparationCircuit problem)
        (exponentPreparationCircuit_physical_idx problem) duration _)
  have readout := (framed_depth (afterExponentReadout p problem) trivial
    (frame E width) (after_disjoint E width) duration path.2).trans
      (afterExponentCircuit_depth p width (exponentReadoutCircuit problem)
        (exponentReadoutCircuit_physical_idx problem) duration _)
  exact congrArg₂ Nat.add (congrArg₂ Nat.add prepared
    (congrArg₂ Nat.add (initializeWork_depth E width duration path.1.2.1)
      (framed_depth scalar supported (frame E width) (after_disjoint E width) duration
        path.1.2.2))) readout

/-- Unit duration preserves the original complete serial prefix bound. -/
theorem preMeasurement_depth (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).depth (fun _ => 1) path ≤
      (exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
        (2 + (4 * MAU.Multiplication.Gidney.eventBound p.size +
          (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size)) +
        (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) := by
  rw [preMeasurement_duration]
  have scalarBound := Encoding.placedConvertedCascade_depth E points
      (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)
      (scalarOriginalPath E fieldTail odd problem points path)
  rw [List.length_finRange] at scalarBound
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.add_le_add_left scalarBound 2) _) _

private theorem measurement_duration (modulus width : Nat)
    (duration : Resource.Event .quantum → Nat)
    (path : (exponentMeasurements modulus width).Path) :
    (exponentMeasurements modulus width).depth duration path =
      (2 * width) * duration (Circuit.zEvent 2) := by
  have actual := Circuit.measurementSequence_depth (QubitReadouts.readouts
    (exponentMeasurementWires modulus width) (exponentMeasurementWires_qubits modulus width)
    (exponentMeasurementCells modulus width)) duration path
  refine actual.trans ?_
  simp only [QubitReadouts.readouts, List.map_ofFn, QubitReadouts.readout, Function.comp_def,
    exponentMeasurementWires_qubits, List.ofFn_const, List.sum_replicate, smul_eq_mul]

/-- Full actual duration contains both preparations, the original scalar path and every final Z. -/
theorem exponentRun_duration (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (duration : Resource.Event .quantum → Nat)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.depth duration path =
      (exponentPreparationCircuit problem).evaluatedEventDepth duration +
        (duration (InPlacePreparation.preparation p).event +
          duration (BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).event +
          (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
            (Semantics.radixUnit p fieldTail.succ odd)).depth duration
              (scalarOriginalPath E fieldTail odd problem points path.1.1)) +
        (exponentReadoutCircuit problem).evaluatedEventDepth duration +
        (2 * orderWidth problem) * duration (Circuit.zEvent 2) := by
  change ((preMeasurement E fieldTail odd problem points).depth duration path.1.1 +
    (allocateTerminal E (orderWidth problem)).depth duration path.1.2) +
    (measurements E (orderWidth problem)).depth duration path.2 = _
  have noDepth : (allocateTerminal E (orderWidth problem)).depth duration path.1.2 = 0 :=
    MeasurementCells.allocateFramed_depth _ _ _ _ _ _ _
  have measured := (framed_depth (exponentMeasurements p (orderWidth problem))
    (Circuit.measurementSequence_isLocal _) (frame E (orderWidth problem))
    (terminal_disjoint E (orderWidth problem)) duration path.2).trans
      (measurement_duration p (orderWidth problem) duration _)
  rw [noDepth, Nat.add_zero]
  exact congrArg₂ Nat.add
    (preMeasurement_duration E fieldTail odd problem points duration path.1.1) measured

/-- The complete actual framed execution retains the original serial unit-duration bound. -/
theorem exponentRun_depth (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (exponentRun E fieldTail odd problem points).code.Path) :
    (exponentRun E fieldTail odd problem points).code.depth (fun _ => 1) path ≤
      (exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
        (2 + (4 * MAU.Multiplication.Gidney.eventBound p.size +
          (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size)) +
        (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) +
          2 * orderWidth problem := by
  have prefixBound := preMeasurement_depth E fieldTail odd problem points path.1.1
  rw [preMeasurement_duration] at prefixBound
  rw [exponentRun_duration, Nat.mul_one]
  exact Nat.add_le_add_right prefixBound _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
