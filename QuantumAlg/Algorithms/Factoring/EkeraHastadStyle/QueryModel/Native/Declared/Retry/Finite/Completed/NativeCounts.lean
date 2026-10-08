/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.ClassicalCoordinates
import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Peripheral Toffoli count of the completed declared-query EH run

The group operation remains a named oracle query. This theorem counts only
the gates around it: actual Hadamard preparation, expanded inverse QFTs and
physical resets. Its zero Toffoli result does not assign a hidden gate cost
to the declared oracle.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

noncomputable section

private theorem member_toffoli_zero {N : Nat} (input : Input N) :
    ResourcePool.count (model := model input) (.gate AlgorithmGate.Coordinate.toffoli)
      (memberEventBudget input) = 0 := by
  have prepared := UnitaryCircuit.unitaryCircuit_event_count_classical_context
    (ShortDLP.DeclaredStage.prepare (Native.encoding input))
    BitWord.model .empty (.gate AlgorithmGate.Coordinate.toffoli)
  have readout := UnitaryCircuit.unitaryCircuit_event_count_classical_context
    (ShortDLP.DeclaredStage.readout (Native.encoding input))
    BitWord.model .empty (.gate AlgorithmGate.Coordinate.toffoli)
  rw [memberEventBudget]
  simp only [ResourcePool.count_add]
  rw [prepared, readout]
  simp only [ShortDLP.DeclaredStage.prepare,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    ShortDLP.DeclaredStage.declaredStage_readout_nativeCount]
  have hadamardCost := congrArg
    (ResourcePool.count (model := .quantum AlgorithmGate.model
      (ShortDLP.DeclaredStage.oracle (Native.encoding input)))
      (.gate .toffoli))
    (Gate.HadamardLayer.hadamardLayer_circuit_eventCost
      (ShortDLP.DeclaredStage.oracle (Native.encoding input))
      (ShortDLP.firstBits (Native.parameters N) + (Native.parameters N).ell))
  rw [hadamardCost]
  simp

theorem member_singleQubit_count {N : Nat} (input : Input N) :
    ResourcePool.count (model := model input) (.gate AlgorithmGate.Coordinate.singleQubit)
      (memberEventBudget input) =
        ShortDLP.DeclaredStage.sourceMacroCount (Native.encoding input) "hadamard" +
          3 * ShortDLP.DeclaredStage.sourceMacroCount
            (Native.encoding input) "controlled-phase" := by
  have word := UnitaryCircuit.unitaryCircuit_event_count_classical_context
    (ShortDLP.DeclaredStage.circuit (Native.encoding input) 1 1)
    BitWord.model .empty (.gate AlgorithmGate.Coordinate.singleQubit)
  have exactWord := word.trans
    (ShortDLP.DeclaredStage.declaredStage_singleQubit_eq_sourceMacros
      (Native.encoding input) 1 1)
  change ResourcePool.count (model := model input) (.gate .singleQubit)
    ((ShortDLP.DeclaredStage.prepare (Native.encoding input)).eventCost BitWord.model .empty +
      (ResourcePool.singleton (model := model input) (.oracle .groupOperation) +
        (ShortDLP.DeclaredStage.readout (Native.encoding input)).eventCost
          BitWord.model .empty)) = _ at exactWord
  simp only [memberEventBudget, ResourcePool.count_add]
  simpa using exactWord

theorem member_cnot_count {N : Nat} (input : Input N) :
    ResourcePool.count (model := model input) (.gate AlgorithmGate.Coordinate.cnot)
      (memberEventBudget input) =
        2 * ShortDLP.DeclaredStage.sourceMacroCount
          (Native.encoding input) "controlled-phase" +
        3 * ShortDLP.DeclaredStage.sourceMacroCount (Native.encoding input) "swap" := by
  have word := UnitaryCircuit.unitaryCircuit_event_count_classical_context
    (ShortDLP.DeclaredStage.circuit (Native.encoding input) 1 1)
    BitWord.model .empty (.gate AlgorithmGate.Coordinate.cnot)
  have exactWord := word.trans
    (ShortDLP.DeclaredStage.declaredStage_cnot_eq_sourceMacros
      (Native.encoding input) 1 1)
  change ResourcePool.count (model := model input) (.gate .cnot)
    ((ShortDLP.DeclaredStage.prepare (Native.encoding input)).eventCost BitWord.model .empty +
      (ResourcePool.singleton (model := model input) (.oracle .groupOperation) +
        (ShortDLP.DeclaredStage.readout (Native.encoding input)).eventCost
          BitWord.model .empty)) = _ at exactWord
  simp only [memberEventBudget, ResourcePool.count_add]
  simpa using exactWord

private theorem reset_gate_count {N : Nat} (input : Input N)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := model input) (.gate coordinate) (resetEventBudget input) =
      ShortDLP.totalQubits (Native.parameters N) *
        (if coordinate = .singleQubit then 1 else 0) := by
  cases coordinate <;>
    simp [resetEventBudget, ZReset.Bank.envelope, ZReset.eventEnvelope, eq_comm]

/-- Each completed member contributes its actual expanded gate ledger. The
independent budget reserves sixteen first-batch resets and seventeen for each
further batch, including the terminal physical reset. -/
theorem completedEventBudget_gate_count {N : Nat} (input : Input N)
    (laterCount : Nat) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := model input) (.gate coordinate)
      (Retry.Finite.Cleanup.completedEventBudget N input laterCount) =
      16 * (laterCount + 1) *
        ResourcePool.count (model := model input) (.gate coordinate)
          (memberEventBudget input) +
      (16 + 17 * laterCount) * ShortDLP.totalQubits (Native.parameters N) *
        (if coordinate = .singleQubit then 1 else 0) := by
  have sourceZero := declared_source_count_eq_zero
    (model := model input) (.gate coordinate) (fun _ => by simp) N
  have recoveryZero := declared_recovery_count_eq_zero
    (model := model input) (.gate coordinate) (fun _ => by simp) N
  cases coordinate <;>
    simp [Retry.Finite.Cleanup.completedEventBudget,
      Retry.Finite.Cleanup.eventBudget,
      Retry.Finite.Cleanup.nextCompletedEventBudget,
      Retry.Finite.eventBudget, Retry.eventBudget,
      Retry.firstEventBudget, Retry.nextEventBudget,
      Batch.Recovery.firstEventBudget, Batch.Recovery.nextEventBudget,
      Batch.firstEventBudget, Batch.nextEventBudget,
      Batch.setupEventBudget, Batch.reusedSampleEventBudget,
      reuseEventBudget, Batch.sourceEventBudget,
      preparationEventBudget, reset_gate_count,
      Batch.copyEvent, Retry.packEvent, Retry.selectionEventBudget,
      ClassicalRoutines.FirstAccepted.Direct.Optional.eventEnvelope,
      ClassicalRoutines.FirstAccepted.Direct.copyTrace,
      sourceZero, recoveryZero] <;> ring

/-- The independent completed-event allowance has no peripheral Toffoli
coordinate, including the actual source, recovery, packing and reset tails. -/
theorem completedEventBudget_toffoli_zero {N : Nat} (input : Input N)
    (laterCount : Nat) :
    ResourcePool.count (model := model input) (.gate AlgorithmGate.Coordinate.toffoli)
      (Retry.Finite.Cleanup.completedEventBudget N input laterCount) = 0 := by
  have sourceZero := declared_source_count_eq_zero
    (model := model input) (.gate AlgorithmGate.Coordinate.toffoli)
    (fun _ => by simp) N
  have recoveryZero := declared_recovery_count_eq_zero
    (model := model input) (.gate AlgorithmGate.Coordinate.toffoli)
    (fun _ => by simp) N
  simp [Retry.Finite.Cleanup.completedEventBudget,
    Retry.Finite.Cleanup.eventBudget,
    Retry.Finite.Cleanup.nextCompletedEventBudget,
    Retry.Finite.eventBudget, Retry.eventBudget,
    Retry.firstEventBudget, Retry.nextEventBudget,
    Batch.Recovery.firstEventBudget, Batch.Recovery.nextEventBudget,
    Batch.firstEventBudget, Batch.nextEventBudget,
    Batch.setupEventBudget, Batch.reusedSampleEventBudget,
    reuseEventBudget, Batch.sourceEventBudget,
    preparationEventBudget, member_toffoli_zero,
    resetEventBudget, ZReset.Bank.envelope, ZReset.eventEnvelope,
    Batch.copyEvent, Retry.packEvent, Retry.selectionEventBudget,
    ClassicalRoutines.FirstAccepted.Direct.Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace,
    sourceZero, recoveryZero]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- No path of the actual all-count completed candidate calls a peripheral
Toffoli gate; the declared group oracle is counted separately. -/
public theorem completedAlgorithm_toffoli_count (input : Input N) (count : Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    ResourcePool.count (model := model input) (.gate AlgorithmGate.Coordinate.toffoli)
      ((completedAlgorithm base noQuantum input count).run.code.resourcePool path) = 0 := by
  cases count with
  | zero => rfl
  | succ laterCount =>
      have bounded := completedFiniteAlgorithm_resourcePool_le
        base noQuantum input laterCount path
      have countBound := ResourcePool.le_iff_count.mp bounded
        (.gate AlgorithmGate.Coordinate.toffoli)
      exact Nat.eq_zero_of_le_zero
        ((completedEventBudget_toffoli_zero input laterCount) ▸ countBound)

/-- Every positive completed path is bounded by the actual member gate ledger
and the independently paid first and later physical resets. -/
theorem completedAlgorithm_gate_count_le_positive (input : Input N) (count : Nat)
    (positive : 0 < count) (coordinate : AlgorithmGate.Coordinate)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    ResourcePool.count (model := model input) (.gate coordinate)
      ((completedAlgorithm base noQuantum input count).run.code.resourcePool path) ≤
      16 * count *
        ResourcePool.count (model := model input) (.gate coordinate)
          (memberEventBudget input) +
      (16 + 17 * Nat.pred count) * ShortDLP.totalQubits (Native.parameters N) *
        (if coordinate = .singleQubit then 1 else 0) := by
  cases count with
  | zero => omega
  | succ laterCount =>
      have bounded := completedFiniteAlgorithm_resourcePool_le
        base noQuantum input laterCount path
      have countBound := ResourcePool.le_iff_count.mp bounded (.gate coordinate)
      simpa only [completedAlgorithm, Nat.pred_succ] using
        countBound.trans_eq (completedEventBudget_gate_count input laterCount coordinate)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
