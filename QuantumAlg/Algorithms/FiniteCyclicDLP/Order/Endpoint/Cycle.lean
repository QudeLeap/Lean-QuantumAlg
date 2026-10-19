/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Specification
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Specification
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Retained.Distribution
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Semantics

/-!
# Certified caller protocols for the complete finite-cyclic DLP batch

The actual Born batch establishes the caller's sampling-quality event. The
classical continuation returns precisely the recovery of those retained
samples, including for arbitrary incoming hidden group-service state. Each
subprotocol's quantum-time bound refers to its complete actual execution.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

private def samplingAlgorithm (P : KnownOrderProblem G) :
    Algorithm (OrderExecution.model P) OrderExecution.pre (sampledContext P)
      (.fixedVector (sampleCount P)
        (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))) :=
  ⟨OrderBatch.run P (sampleCount P) (OrderExecution.canonicalExpansion P)⟩

private def recoveryAlgorithm (P : KnownOrderProblem G) :
    Algorithm (OrderExecution.model P) (sampledContext P) (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) :=
  ⟨{ code := retainedRecovery P
     output := Output.all (outputContext P)
       (.read (.storage (outputRef P).toCStorageRef)) }⟩

private lemma run_restoresBorrowed {model : ExecutionModel}
    (environment : model.Environment)
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (selected : AlgorithmRun model pre post shape)
    (noBorrowed : pre.borrowedQuantumWires = []) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) :
    selected.RestoresBorrowed environment input := by
  have restored := Circuit.borrowedRestored_of_noBorrowedQuantum selected.code environment
    noBorrowed Reference
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
  have history := Execution.observeBorrowed_mapClassical input.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
  change selected.code.BorrowedRestored Reference input.state
    (selected.code.execute environment Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
  unfold Circuit.BorrowedRestored at restored ⊢
  rw [restored]
  refine Eq.trans ?_ history
  apply congrArg (Execution.observeBorrowed Reference)
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

private lemma sampling_success (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    ((samplingProblem P).successLB (OrderExecution.sourceEnvironment P) secret).value ≤
      ((samplingAlgorithm P).relationalDistribution
        (OrderExecution.sourceEnvironment P) input).toOuterMeasure
        {pair | (samplingProblem P).accepts
          (OrderExecution.sourceEnvironment P) secret pair.1 pair.2} := by
  have success := run_success P secret input
  rw [run_outputDistribution_raw, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply] at success
  change ENNReal.ofReal ((2 : Real) / 3) ≤ _
  simpa only [samplingAlgorithm, Algorithm.relationalDistribution,
    AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
    samplingProblem, PMF.toOuterMeasure_map_apply, Set.preimage,
    Set.mem_ofPred_eq, Set.mem_singleton_iff] using success

private lemma sampling_solves (P : KnownOrderProblem G) :
    Algorithm.Solves (samplingAlgorithm P) (samplingProblem P) where
  success := by
    intro environment secret Reference input valid _initialized
    have same : environment = OrderExecution.sourceEnvironment P := valid
    subst environment
    exact sampling_success P secret input
  states := by
    intro environment witness Reference input valid initialized requirement present
    exact False.elim (List.not_mem_nil present)
  borrowed := by
    intro environment witness Reference input valid initialized
    exact run_restoresBorrowed environment (samplingAlgorithm P).run
      RuntimeCtx.borrowedQuantumWires_empty input
  events := by
    intro environment witness Reference input valid initialized path supported
    exact le_of_eq (OrderBatch.code_events P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path)
  resident := by
    intro environment witness Reference input valid initialized path supported
    exact (OrderBatch.code_resident_le P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path).trans_eq
        (OrderBatch.post_residentSpace P (sampleCount P))
  auxiliary := by
    intro environment witness Reference input valid initialized path supported
    exact (OrderBatch.code_auxiliary_le P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path).trans_eq
        (OrderBatch.post_auxiliarySpace P (sampleCount P))
  time := by
    intro environment witness Reference input valid initialized path supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact le_of_eq (OrderBatch.code_depth P (sampleCount P)
      (OrderExecution.canonicalExpansion P) path)

private lemma recovery_record (P : KnownOrderProblem G) :
    ∃ record : Store (outputContext P) × (OrderExecution.model P).HiddenState →
        (Store (outputContext P) × (OrderExecution.model P).HiddenState) ×
          (recoveryCircuit P).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State (outputContext P) Reference
          ((OrderExecution.model P).HiddenState × History)),
        (recoveryCircuit P).execute
          (OrderExecution.sourceEnvironment P) Reference state = state.mapClassical (fun entry =>
          let result := record (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before, (record before).1.1.read (.storage (outputRef P).toCStorageRef) =
        recoveredValue P (.fixedVector fun index => before.1.read (retainedSample P index)) := by
  by_cases trivial : P.order = 1
  · rw [recoveryCircuit_order_one P trivial]
    obtain ⟨record, executed, values⟩ :=
      ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_actualRecord
        (environment := OrderExecution.sourceEnvironment P)
          (model := OrderExecution.model P) (outputRef P)
    refine ⟨record, executed, ?_⟩
    intro before
    rw [values, Store.read_write_same, recoveredValue_order_one P trivial]
  · rw [recoveryCircuit_nontrivial P trivial]
    obtain ⟨record, executed, values⟩ :=
      OrderRecovery.Native.recoveryInto_actualRecord_correct
        (quantumEnvironment := OrderOracle.interpretation P) P (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P)
    refine ⟨record, executed, ?_⟩
    intro before
    rw [values, Store.read_write_same, recoveredValue_nontrivial P trivial]
    rfl

/-- The continuation's actual relational law retains the complete initial sample
store while reading the exact checked recovery from its final destination. -/
private lemma recovery_relational (P : KnownOrderProblem G) {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      (sampledContext P) Reference) :
    (recoveryAlgorithm P).relationalDistribution (OrderExecution.sourceEnvironment P) input =
      (input.state.toPMF input.normalized).map (fun entry =>
        (entry.1, recoveredValue P (entry.1.read
          (OrderBatch.samplesInput P (sampleCount P))))) := by
  obtain ⟨record, executed, values⟩ := recovery_record P
  have mapped := AlgorithmRun.relationalDistribution_retained_eq_map
    (model := OrderExecution.model P) (sampledContext P) (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)
    (recoveryCircuit P) (OrderExecution.sourceEnvironment P)
      (recoveryAlgorithm P).run.output record executed input
  change (recoveryAlgorithm P).run.relationalDistribution
    (OrderExecution.sourceEnvironment P) input = _
  refine mapped.trans ?_
  apply congrArg ((input.state.toPMF input.normalized).map)
  funext entry
  change (entry.1, (record (entry.1.pushRetained (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P),
      entry.2)).1.1.read (.storage (outputRef P).toCStorageRef)) = _
  rw [values]
  apply congrArg (fun value => (entry.1, recoveredValue P value))
  change CShape.Value.fixedVector (fun index =>
    (entry.1.pushRetained (outputKey P)
      (.option (.unsignedWord (OrderPreparation.width P))) (outputKey_fresh P)).read
        (retainedSample P index)) =
    CShape.Value.fixedVector (fun index => entry.1.read (OrderBatch.sampleInput P index))
  apply congrArg CShape.Value.fixedVector
  funext index
  exact Store.read_pushRetained_underRetained _ _ _ _ _

private lemma recovery_success (P : KnownOrderProblem G) {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      (sampledContext P) Reference) :
    ((recoveryAlgorithm P).relationalDistribution
      (OrderExecution.sourceEnvironment P) input).toOuterMeasure
      {pair | (recoveryProblem P).accepts
        (OrderExecution.sourceEnvironment P) () pair.1 pair.2} = 1 := by
  rw [recovery_relational, PMF.toOuterMeasure_map_apply]
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro entry supported
  rfl

private lemma recovery_solves (P : KnownOrderProblem G) :
    Algorithm.Solves (recoveryAlgorithm P) (recoveryProblem P) where
  success := by
    intro environment witness Reference input valid initialized
    have same : environment = OrderExecution.sourceEnvironment P := valid
    subst environment
    cases witness
    rw [recovery_success]
    exact le_rfl
  states := by
    intro environment witness Reference input valid initialized requirement present
    exact False.elim (List.not_mem_nil present)
  borrowed := by
    intro environment witness Reference input valid initialized
    apply run_restoresBorrowed environment (recoveryAlgorithm P).run _ input
    exact (OrderBatch.code P (sampleCount P)
      (OrderExecution.canonicalExpansion P)).borrowedQuantumWires_preserved.trans
        RuntimeCtx.borrowedQuantumWires_empty
  events := by
    intro environment witness Reference input valid initialized path supported
    exact retainedRecovery_pool_le P path
  resident := by
    intro environment witness Reference input valid initialized path supported
    exact retainedRecovery_resident_le P path
  auxiliary := by
    intro environment witness Reference input valid initialized path supported
    exact retainedRecovery_auxiliary_le P path
  time := by
    intro environment witness Reference input valid initialized path supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact retainedRecovery_depth_le P (fun _ => 1) path

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
