/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Scalar
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Scalar
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Specification
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.First
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Schedule
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.First
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Schedule
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor

import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Retained.Distribution
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Semantics

/-!
# Complete sequential finite-cyclic DLP sampling and classical recovery

Each actual prepared sample is a complete source experiment; later samples
reuse the same bank after its physical terminal reset. The checked classical
continuation receives the actual retained samples and hidden service state.
Its events remain in the execution ledger and have zero canonical quantum duration
[Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

private def recoveryAlgorithm (P : KnownOrderProblem G) :
    Algorithm (Reusable.model P) (sampledContext P) (outputContext P)
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

private lemma recovery_record (P : KnownOrderProblem G) :
    ∃ record : Store (outputContext P) × (Reusable.model P).HiddenState →
        (Store (outputContext P) × (Reusable.model P).HiddenState) ×
          (recoveryCircuit P).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State (outputContext P) Reference
          ((Reusable.model P).HiddenState × History)),
        (recoveryCircuit P).execute
          (Reusable.sourceEnvironment P) Reference state = state.mapClassical (fun entry =>
          let result := record (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before, (record before).1.1.read (.storage (outputRef P).toCStorageRef) =
        recoveredValue P (.fixedVector fun index => before.1.read (retainedSample P index)) := by
  by_cases trivial : P.order = 1
  · rw [binaryEndpoint_recoveryCircuit_order_one P trivial]
    obtain ⟨record, executed, values⟩ :=
      ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_actualRecord
        (environment := Reusable.sourceEnvironment P)
        (model := Reusable.model P) (outputRef P)
    refine ⟨record, executed, ?_⟩
    intro before
    rw [values, Store.read_write_same, binaryEndpoint_recoveredValue_order_one P trivial]
  · rw [binaryEndpoint_recoveryCircuit_nontrivial P trivial]
    obtain ⟨record, executed, values⟩ :=
      OrderRecovery.Native.recoveryInto_actualRecord_correct
        (quantumEnvironment := Binary.Oracle.interpretation P)
        (oracles := Binary.Oracle.model P) P (recoverySpec P trivial)
        (sampleCount P) (retainedSample P) (outputRef P)
    refine ⟨record, executed, ?_⟩
    intro before
    rw [values, Store.read_write_same, binaryEndpoint_recoveredValue_nontrivial P trivial]
    rfl

/-- The continuation's actual relational law retains the complete initial sample
store while reading the exact checked recovery from its final destination. -/
private lemma recovery_relational (P : KnownOrderProblem G) {Reference : Register}
    (input : OracleInput (Reusable.model P).classicalOracles
      (sampledContext P) Reference) :
    (recoveryAlgorithm P).relationalDistribution (Reusable.sourceEnvironment P) input =
      (input.state.toPMF input.normalized).map (fun entry =>
        (entry.1, recoveredValue P (entry.1.read
          (Reusable.samplesInput P (sampleCount P))))) := by
  obtain ⟨record, executed, values⟩ := recovery_record P
  have mapped := AlgorithmRun.relationalDistribution_retained_eq_map
    (model := Reusable.model P) (sampledContext P) (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P)
    (recoveryCircuit P) (Reusable.sourceEnvironment P)
      (recoveryAlgorithm P).run.output record executed input
  change (recoveryAlgorithm P).run.relationalDistribution (Reusable.sourceEnvironment P) input = _
  refine mapped.trans ?_
  apply congrArg ((input.state.toPMF input.normalized).map)
  funext entry
  change (entry.1, (record (entry.1.pushRetained (outputKey P)
    (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P),
      entry.2)).1.1.read (.storage (outputRef P).toCStorageRef)) = _
  rw [values]
  apply congrArg (fun value => (entry.1, recoveredValue P value))
  change CShape.Value.fixedVector (fun index =>
    (entry.1.pushRetained (outputKey P)
      (.option (.unsignedWord (OrderPreparation.width P))) (binaryEndpoint_outputKey_fresh P)).read
        (retainedSample P index)) =
    CShape.Value.fixedVector (fun index => entry.1.read (Reusable.sampleInput P index))
  apply congrArg CShape.Value.fixedVector
  funext index
  exact Store.read_pushRetained_underRetained _ _ _ _ _

private lemma recovery_success (P : KnownOrderProblem G) {Reference : Register}
    (input : OracleInput (Reusable.model P).classicalOracles
      (sampledContext P) Reference) :
    ((recoveryAlgorithm P).relationalDistribution
      (Reusable.sourceEnvironment P) input).toOuterMeasure
      {pair | (recoveryProblem P).accepts (Reusable.sourceEnvironment P) () pair.1 pair.2} = 1 := by
  rw [recovery_relational, PMF.toOuterMeasure_map_apply]
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro entry supported
  rfl

private lemma recovery_solves (P : KnownOrderProblem G) :
    Algorithm.Solves (recoveryAlgorithm P) (recoveryProblem P) where
  success := by
    intro environment witness Reference input valid initialized
    have same : environment = Reusable.sourceEnvironment P := valid
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
    exact (Reusable.code P (sampleCount P)
      (OrderExecution.canonicalExpansion P)).borrowedQuantumWires_preserved.trans
        RuntimeCtx.borrowedQuantumWires_empty
  events := by
    intro environment witness Reference input valid initialized path supported
    exact binaryEndpoint_retainedRecovery_pool_le P path
  resident := by
    intro environment witness Reference input valid initialized path supported
    exact binaryEndpoint_retainedRecovery_resident_le P path
  auxiliary := by
    intro environment witness Reference input valid initialized path supported
    exact binaryEndpoint_retainedRecovery_auxiliary_le P path
  time := by
    intro environment witness Reference input valid initialized path supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact binaryEndpoint_retainedRecovery_depth_le P (fun _ => 1) path

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
