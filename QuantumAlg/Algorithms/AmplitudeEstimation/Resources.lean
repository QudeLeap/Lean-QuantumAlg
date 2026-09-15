/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Specification
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Counts
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Components.Oracle.Common
import all QuantumAlg.Components.Oracle.ZeroReflection
import Mathlib.Data.List.OfFn

/-!
# Exact complete amplitude-estimation events and depth

Every actual path charges one all-zero preparation, the source-correct
unitary, each retained-cell Z write, and the final packing opcode. The
complete trace is compared with explicit independent event and depth formulas.
Ordinary U and U-dagger queries remain separate native coordinates.

-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

private theorem preparation_value (t n : Nat) (index : Fin (t + (Elementary.helperWidth t n + n))) :
    ((inputPreparation t n).value index).val = 0 := by
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ (t + (Elementary.helperWidth t n + n)))).val.testBit index.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

theorem inputPreparation_event (t n : Nat) :
    (inputPreparation t n).event = basisPreparationEvent t n := by
  have dimensions : (runtimeLayout t n).dimensions.map PNat.val =
      List.replicate (t + (Elementary.helperWidth t n + n)) 2 := by
    change (List.ofFn (fun _ : Fin (t + (Elementary.helperWidth t n + n)) => (2 : ℕ+))).map
      PNat.val = _
    rw [List.map_ofFn]
    exact List.ofFn_const (t + (Elementary.helperWidth t n + n)) 2
  have values : List.ofFn (fun index => ((inputPreparation t n).value index).val) =
      List.replicate (t + (Elementary.helperWidth t n + n)) 0 := by
    simp only [preparation_value, List.ofFn_const]
  change Resource.Event.preparation
    { family := "builtin", name := "computational-basis",
      parameters := (t + (Elementary.helperWidth t n + n)) ::
        ((runtimeLayout t n).dimensions.map PNat.val ++
          List.ofFn (fun index => ((inputPreparation t n).value index).val)) } = _
  rw [dimensions, values]
  rfl

private theorem program_pool {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    ResourcePool.ofList (nativeProgram E t).eventTrace = Elementary.unitaryEventPool t n := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProgram,
    UnitaryCircuit.reindex_eventCost, Elementary.program_eventCost]

private theorem measurement_pool (t n : Nat)
    (path : (Circuit.measurementSequence (readouts t n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (readouts t n)).eventTrace path) =
      t • ResourcePool.singleton (Circuit.zEvent 2) := by
  change (Circuit.measurementSequence (readouts t n)).resourcePool path = _
  rw [Circuit.measurementSequence_qubit_resourcePool (readouts t n) (readouts_qubits t n),
    readouts_length]

private theorem packing_trace (t n : Nat) :
    (packing t n).eventTrace =
      [.classicalOperation (.nominalEncoding (.packFiniteBits t))] :=
  ClassicalOp.eventTrace_packFiniteBits t _ _ _

private theorem allocation_trace (t n : Nat) (path : (allocationCode t n).Path) :
    (allocationCode t n).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (resultContext t n) 2 t path.2

/-- Every actual path has exactly the independent complete native event pool. -/
theorem code_events {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (code E t).Path) :
    (code E t).resourcePool path = eventBudget t n := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    preparationCode, allocation_trace, Circuit.eventTrace,
    List.append_nil, ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero, inputPreparation_event, program_pool,
    measurement_pool, packing_trace]
  rfl

private theorem program_depth {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    (nativeProgram E t).evaluatedEventDepth (fun _ => 1) = Elementary.unitaryDepth t n :=
  Elementary.program_unitDepth t E.source.preparation E.source.good

/-- Exact unit-event depth includes preparation, each sequential Z write and final packing. -/
theorem code_depth {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (path : (code E t).Path) :
    (code E t).depth (fun _ => 1) path = depthBudget t n := by
  change (1 + ((nativeProgram E t).evaluatedEventDepth (fun _ => 1) +
    (0 + (MeasurementCells.allocate (resultContext t n) 2 t).depth
      (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (readouts t n)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  unfold depthBudget
  omega

/-- The complete hybrid execution contains exactly the unitary's actual elementary gates. -/
theorem code_gateCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((code E t).resourcePool path) =
        Elementary.unitaryGateCount t n := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight ((code E t).resourcePool path) = _
  have actual : ResourcePool.weightedCount weight (Elementary.unitaryEventPool t n) =
      Elementary.unitaryGateCount t n := by
    rw [← Elementary.program_eventCost t E.source.preparation E.source.good]
    refine Eq.trans ?_ (Elementary.program_gateCount t E.source.preparation E.source.good)
    apply congrArg (fun assignment : Resource.Event .quantum → Nat =>
      ResourcePool.weightedCount assignment
        (Elementary.program t E.source.preparation E.source.good).eventCost)
    funext event
    cases event <;> rfl
  rw [code_events]
  simp only [eventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton]
  rw [actual]
  dsimp only [weight, basisPreparationEvent]
  omega

/-- Preparation, Z measurements and packing add no quantum-subroutine calls. -/
theorem code_quantumSubroutineCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label) ((code E t).resourcePool path) =
      ResourcePool.count (.quantumSubroutine label)
        (Elementary.program t E.source.preparation E.source.good).eventCost := by
  rw [code_events, Elementary.program_eventCost]
  simp [eventBudget, basisPreparationEvent]

/-- Exact ordinary preparation queries include the initial U before the power ladder. -/
theorem code_preparationCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (AmplitudeAmplificationSource.preparationEvent n)
      ((code E t).resourcePool path) = (2 ^ t - 1) + 1 :=
  (code_quantumSubroutineCount E t path
    (AmplitudeAmplificationSource.preparationLabel n).quantum).trans
      (Elementary.program_preparationCount t E.source.preparation E.source.good)

/-- Every controlled ladder call contains one ordinary inverse-preparation query. -/
theorem code_inversePreparationCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count (AmplitudeAmplificationSource.inversePreparationEvent n)
      ((code E t).resourcePool path) = 2 ^ t - 1 :=
  (code_quantumSubroutineCount E t path
    (AmplitudeAmplificationSource.inversePreparationLabel n).quantum).trans
      (Elementary.program_inversePreparationCount t E.source.preparation E.source.good)

/-- Every controlled ladder call contains the source's controlled good-state reflection. -/
theorem code_controlledGoodReflectionCount {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (path : (code E t).Path) :
    ResourcePool.count
      ((AmplitudeAmplificationSource.goodReflectionEvent n).controlForDimension 2)
      ((code E t).resourcePool path) = 2 ^ t - 1 :=
  (code_quantumSubroutineCount E t path
    ((AmplitudeAmplificationSource.goodReflectionLabel n).quantum.controlForDimension 2)).trans
      (Elementary.program_controlledGoodReflectionCount t
        E.source.preparation E.source.good)

end

end QuantumAlg.AmplitudeEstimation
