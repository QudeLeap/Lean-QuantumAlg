/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.QuantumSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Initialization
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Scalar
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Primitives.ZReset.Bank

/-!
# Unit event bounds for complete original ECDLP computations

This auxiliary weight counts each quantum gate, query, zero preparation and
measurement as one event while excluding classical work. It preserves the
original weighted-depth inequalities. Algorithm quantum computation time uses
`Resource.Event.quantumDuration`, whose measurement and zero-preparation
weights are zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section
open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native
variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Unit event weight for the original quantum-event accounting inequalities. -/
@[expose] public def quantumEventUnitWeight {model : ExecutionModel} : Resource.Event model → Nat
  | .classicalOperation _ | .classicalQuery _ => 0
  | .gate _ | .oracle _ | .preparation _ | .measurement _ => 1

/-- Classical computation contributes zero to this event observation. -/
@[simp] public lemma ecdlpQuantum_eventUnitWeight_classicalOperation {model : ExecutionModel}
    (coordinate : model.ClassicalCoordinate) :
    quantumEventUnitWeight (.classicalOperation coordinate : Resource.Event model) = 0 := rfl

/-- Classical queries contribute zero to this event observation. -/
@[simp] public lemma ecdlpQuantum_eventUnitWeight_classicalQuery {model : ExecutionModel}
    (coordinate : model.ClassicalOracleCoordinate) :
    quantumEventUnitWeight (.classicalQuery coordinate : Resource.Event model) = 0 := rfl

/-- Every actual native gate contributes one counted event. -/
@[simp] public lemma ecdlpQuantum_eventUnitWeight_gate {model : ExecutionModel}
    (coordinate : model.GateCoordinate) :
    quantumEventUnitWeight (.gate coordinate : Resource.Event model) = 1 := rfl

/-- Every granted quantum query contributes one counted event. -/
@[simp] public lemma ecdlpQuantum_eventUnitWeight_oracle {model : ExecutionModel}
    (coordinate : model.OracleCoordinate) :
    quantumEventUnitWeight (.oracle coordinate : Resource.Event model) = 1 := rfl

/-- Each preparation is one event in this auxiliary accounting weight. -/
@[simp] public lemma ecdlpQuantum_eventUnitWeight_preparation {model : ExecutionModel}
    (dimension : model.SystemDimension) :
    quantumEventUnitWeight (.preparation dimension : Resource.Event model) = 1 := rfl

/-- Each measurement is one event in this auxiliary accounting weight. -/
@[simp] public lemma ecdlpQuantum_eventUnitWeight_measurement {model : ExecutionModel}
    (dimension : model.SystemDimension) :
    quantumEventUnitWeight (.measurement dimension : Resource.Event model) = 1 := rfl

private lemma quantumEventUnitWeight_le_unit {model : ExecutionModel}
    (event : Resource.Event model) :
    quantumEventUnitWeight event ≤ 1 := by cases event <;> simp [quantumEventUnitWeight]

/-- One real reused round, including both resets and every terminal exponent readout. -/
def quantumEventRoundDepthBound (fieldWidth sampleWidth : Nat) : Nat :=
  4 * Scalar.qubits fieldWidth sampleWidth + 13 * sampleWidth +
    5 * Nat.choose sampleWidth 2 + 3 * (sampleWidth / 2) + 3

private lemma reset_quantum_event_unit_depth {allowAllocation : Bool}
    (I : ECDLPInstance E)
    (path : (Sampling.Reuse.reset (allowAllocation := allowAllocation) I).Path) :
    (Sampling.Reuse.reset (allowAllocation := allowAllocation) I).depth
      quantumEventUnitWeight path ≤ 2 * Scalar.qubits (fieldWidth E) (scalarWidth I) := by
  have unit := ZReset.Bank.zResetBank_unitDepth_le (allowAllocation := allowAllocation)
    (services := .empty)
    (oracles := model I) (operations := BitWord.model)
    (Sampling.Reuse.ecdlpReuse_qubits I) (Sampling.Reuse.scratch I) path
  have dimensions : (Sampling.Reuse.context I).systemCount = Layout.totalQubits I := by
    change (Sampling.post I).systemCount = Layout.totalQubits I
    simpa only [Fintype.card_fin] using Fintype.card_congr (Sampling.wireEquiv I).symm
  rw [dimensions, original_qubits_scalar] at unit
  exact (DepthExpr.depthEval_mono quantumEventUnitWeight_le_unit _).trans unit

private lemma native_quantum_event_unit_depth (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    DepthExpr.depthEval quantumEventUnitWeight
        ((Sampling.Reuse.nativeProgram I expansion).eventDepth BitWord.model .empty) ≤
      11 * scalarWidth I + 3 + 5 * Nat.choose (scalarWidth I) 2 +
        3 * (scalarWidth I / 2) := by
  refine (DepthExpr.depthEval_mono quantumEventUnitWeight_le_unit _).trans ?_
  rw [Sampling.Reuse.nativeProgram, Execution.unitaryOfEqualWires_depth]
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context,
    UnitaryCircuit.evaluatedEventDepth_seq, circuit_unit_depth]
  have init : (initializer I).evaluatedEventDepth (fun _ => 1) = 1 := rfl
  rw [init]
  have prepared := (FiniteCyclicDLP.OrderPreparation.orderPreparation_scalarBounds
    (problem I) expansion).2.2
  change FiniteCyclicDLP.OrderPreparation.unitDepth expansion ≤ 10 * scalarWidth I + 1
    at prepared
  change 1 + (FiniteCyclicDLP.OrderPreparation.unitDepth expansion + 1 +
    (scalarWidth I + 5 * Nat.choose (scalarWidth I) 2 +
      (if scalarWidth I / 2 = 0 then 0 else 3))) ≤ _
  split_ifs <;> omega

private lemma readout_quantum_event_unit_depth {allowAllocation : Bool}
    (I : ECDLPInstance E)
    (path : (Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := model I)
      (operations := BitWord.model) (classicalOracles := .empty)
      (Sampling.Reuse.readouts I)).Path) :
    (Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := model I)
      (operations := BitWord.model) (classicalOracles := .empty)
      (Sampling.Reuse.readouts I)).depth quantumEventUnitWeight path = 2 * scalarWidth I := by
  rw [Circuit.measurementSequence_depth]
  simp [quantumEventUnitWeight, Circuit.zEvent, Sampling.Reuse.readouts, Sampling.sampleWidth,
    Function.comp_def, scalarWidth, two_mul]

private lemma sampling_quantum_event_unit_depth_aux {allowAllocation : Bool}
    (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (path : (Sampling.Reuse.code (allowAllocation := allowAllocation) I expansion).Path) :
    (Sampling.Reuse.code (allowAllocation := allowAllocation) I expansion).depth
      quantumEventUnitWeight path ≤
      quantumEventRoundDepthBound (fieldWidth E) (scalarWidth I) := by
  have first := reset_quantum_event_unit_depth (allowAllocation := allowAllocation) I path.1
  have word := native_quantum_event_unit_depth I expansion
  have readout := readout_quantum_event_unit_depth (allowAllocation := allowAllocation)
    I path.2.2.1
  have last := reset_quantum_event_unit_depth (allowAllocation := allowAllocation) I path.2.2.2
  change (Sampling.Reuse.reset (allowAllocation := allowAllocation) I).depth
    quantumEventUnitWeight path.1 +
    (DepthExpr.depthEval quantumEventUnitWeight
      ((Sampling.Reuse.nativeProgram I expansion).eventDepth BitWord.model .empty) +
      ((Circuit.measurementSequence (allowAllocation := allowAllocation)
        (Sampling.Reuse.readouts I)).depth quantumEventUnitWeight
        path.2.2.1 +
        (Sampling.Reuse.reset (allowAllocation := allowAllocation) I).depth
          quantumEventUnitWeight path.2.2.2)) ≤ _
  unfold quantumEventRoundDepthBound
  omega

/-- The actual reused sampler retains the maximum of its parallel peripheral branches. -/
lemma sampling_quantum_event_unit_depth (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (path : (Sampling.Reuse.code I expansion).Path) :
    (Sampling.Reuse.code I expansion).depth quantumEventUnitWeight path ≤
      quantumEventRoundDepthBound (fieldWidth E) (scalarWidth I) := by
  exact sampling_quantum_event_unit_depth_aux (allowAllocation := true) I expansion path

private lemma attempt_quantum_weight_zero (I : ECDLPInstance E)
    (nontrivial : 2 ≤ (problem I).order) :
    ResourcePool.weightedCount quantumEventUnitWeight
      (attemptEnvelope (Sampling.executionModel I) (curve E) (modulus I nontrivial)) = 0 := by
  classical
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  by_cases operation : ∃ label, event = .classicalOperation label
  · obtain ⟨label, rfl⟩ := operation
    rfl
  · have zero := attemptEnvelope_count_eq_zero (model := Sampling.executionModel I)
      event (by intro label same; exact operation ⟨label, same⟩)
      (curve E) (modulus I nontrivial)
    exact False.elim ((Multiset.count_eq_zero.mp zero) present)

/-- Checked recovery and first-success feedback contribute no quantum duration. -/
lemma round_quantum_event_unit_depth (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (path : (round I expansion nontrivial).Path) :
    (round I expansion nontrivial).depth quantumEventUnitWeight path ≤
      quantumEventRoundDepthBound (fieldWidth E) (scalarWidth I) := by
  have duration := sampledAttempt_duration
    (Sampling.Reuse.code (allowAllocation := false) I expansion)
    (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) quantumEventUnitWeight path
  have checking := Circuit.depth_le_weightedCount_of_pool_le
    (persistentAttempt (model := Sampling.executionModel I)
      (curve E) (modulus I nontrivial) (Sampling.Reuse.sampleInput I)
      (baseInput I) (targetInput I)) quantumEventUnitWeight
    (attemptEnvelope (Sampling.executionModel I) (curve E) (modulus I nontrivial)) path.2
    (attemptInto_pool_le (curve E) (modulus I nontrivial) _ _ _ _ _ _ _ _ _ _ path.2)
  rw [attempt_quantum_weight_zero I nontrivial] at checking
  have sampling := sampling_quantum_event_unit_depth_aux (allowAllocation := false)
    I expansion path.1
  exact duration.le.trans
    ((Nat.add_le_add sampling checking).trans_eq (Nat.add_zero _))

private lemma initial_quantum_event_unit_depth (I : ECDLPInstance E)
    (path : (Sampling.Reuse.initialCode I).Path) :
    (Sampling.Reuse.initialCode I).depth quantumEventUnitWeight path ≤ 1 := by
  have cells : (Sampling.allocationCode I).depth quantumEventUnitWeight path.1.2 = 0 :=
    MeasurementCells.allocate_depth (model := Sampling.executionModel I)
      (Sampling.bankContext I) 2 (Sampling.sampleWidth I) quantumEventUnitWeight path.1.2
  have bank : (Sampling.preparationCode I).depth quantumEventUnitWeight path.1.1 ≤ 1 := by
    refine (DepthExpr.depthEval_mono quantumEventUnitWeight_le_unit _).trans ?_
    change DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (model I) (layout I) BitWord.model .empty)
        ≤ 1
    rw [ZeroPreparation.zeroPreparation_unit_depth AlgorithmGate.model
      (model I) (layout I) BitWord.model .empty]
    split <;> omega
  change (Sampling.preparationCode I).depth quantumEventUnitWeight path.1.1 +
    (Sampling.allocationCode I).depth quantumEventUnitWeight path.1.2 + 0 ≤ 1
  omega

/-- Parallel preparation contributes at most one layer before the first whole round. -/
lemma firstRound_quantum_event_unit_depth (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (path : (firstRound I expansion nontrivial).Path) :
    (firstRound I expansion nontrivial).depth quantumEventUnitWeight path ≤
      quantumEventRoundDepthBound (fieldWidth E) (scalarWidth I) + 1 := by
  change ((Sampling.Reuse.initialCode I).depth quantumEventUnitWeight path.1.1 +
    (retainPersistent (model := Sampling.executionModel I)
      (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)).depth
      quantumEventUnitWeight path.1.2) +
      (round I expansion nontrivial).depth quantumEventUnitWeight path.2 ≤ _
  have retained := retainPersistent_depth (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I) quantumEventUnitWeight path.1.2
  have initial := initial_quantum_event_unit_depth I path.1.1
  have later := round_quantum_event_unit_depth I expansion nontrivial path.2
  omega

/-- Zero rounds still execute real preparation, allocation and the final classical result pack. -/
lemma zero_quantum_event_unit_depth (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (path : (code I expansion nontrivial 0).Path) :
    (code I expansion nontrivial 0).depth quantumEventUnitWeight path ≤ 1 := by
  change (Sampling.Reuse.initialCode I).depth quantumEventUnitWeight path.1 +
    (((retainPersistent (model := Sampling.executionModel I)
      (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)).depth
      quantumEventUnitWeight path.2.1.1 + 0) +
      (packBatchResult (model := Sampling.executionModel I)
        (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)).depth
        quantumEventUnitWeight path.2.2) ≤ 1
  have retained := retainPersistent_depth (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I) quantumEventUnitWeight path.2.1.1
  have packed :
      (packBatchResult (model := Sampling.executionModel I)
        (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)).depth
          quantumEventUnitWeight path.2.2 = 0 :=
    packBatchResult_depth (model := Sampling.executionModel I)
      (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I) quantumEventUnitWeight path.2.2
  have initial := initial_quantum_event_unit_depth I path.1
  omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
