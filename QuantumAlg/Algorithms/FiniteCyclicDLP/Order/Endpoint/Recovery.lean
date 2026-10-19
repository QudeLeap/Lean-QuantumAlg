/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Run
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Semantics

/-!
# Actual output value of the all-order recovery tail

The retained result cell is written by the same actual record used for
resource accounting. Order one writes zero; every other positive order writes
the chronological first candidate accepted by raw recovery and hidden group
verification.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

open Execution

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma sequence_read {model : ExecutionModel}
    {environment : model.Environment}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    {Reference : Register} {History Value : Type} [Fintype History] [Fintype Value]
    (state : State pre Reference (model.HiddenState × History))
    (read : Store post → Value) :
    ((first.seq second).execute environment Reference state).mapClassical
        (fun entry => read entry.1) =
      (second.execute environment Reference
        (first.execute environment Reference state)).mapClassical
        (fun entry => read entry.1) := by
  have executed := congrArg
    (fun output => output.mapClassical (fun entry => read entry.1))
    (Circuit.execute_seq (environment := environment) first second state)
  refine executed.trans ?_
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]

/-- Pure result determined by the actual retained sample vector. -/
@[expose] public def recoveredValue (P : KnownOrderProblem G)
    (samples : CShape.Value (.fixedVector (sampleCount P)
      (.fixedVector (OrderExecution.sampleWidth P) (.finite 2)))) :
    CShape.Value (.option (.unsignedWord (OrderPreparation.width P))) :=
  if trivial : P.order = 1 then
    .optionSome (CShape.wordOfNat (OrderPreparation.width P) 0)
  else
    OrderRecovery.Native.recoveryValue P (recoverySpec P trivial)
      (sampleCount P) samples.get

omit [Fintype G] in
/-- At order one, recovery returns the unique residue without inspecting the samples. -/
public lemma recoveredValue_order_one (P : KnownOrderProblem G)
    (trivial : P.order = 1)
    (samples : CShape.Value (.fixedVector (sampleCount P)
      (.fixedVector (OrderExecution.sampleWidth P) (.finite 2)))) :
    recoveredValue P samples =
      .optionSome (CShape.wordOfNat (OrderPreparation.width P) 0) := by
  simp [recoveredValue, trivial]

omit [Fintype G] in
/-- At every nontrivial order, recovery is the checked native selection value. -/
public lemma recoveredValue_nontrivial (P : KnownOrderProblem G)
    (nontrivial : P.order ≠ 1)
    (samples : CShape.Value (.fixedVector (sampleCount P)
      (.fixedVector (OrderExecution.sampleWidth P) (.finite 2)))) :
    recoveredValue P samples =
      OrderRecovery.Native.recoveryValue P (recoverySpec P nontrivial)
        (sampleCount P) samples.get := by
  simp [recoveredValue, nontrivial]

/-- The selected recovery branch reads its actual inputs and writes precisely
the corresponding pure value to the retained output cell. -/
public lemma recoveryCircuit_read (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (outputContext P) Reference
      ((OrderExecution.model P).HiddenState × History)) :
    ((recoveryCircuit P).execute (OrderExecution.sourceEnvironment P) Reference state).mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)) =
      state.mapClassical (fun entry => recoveredValue P
        (.fixedVector fun index => entry.1.read (retainedSample P index))) := by
  by_cases trivial : P.order = 1
  · rw [recoveryCircuit_order_one P trivial]
    obtain ⟨record, executed, values⟩ :=
      ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroInto_actualRecord
        (environment := OrderExecution.sourceEnvironment P)
        (model := OrderExecution.model P) (outputRef P)
    have observed := congrArg
      (fun output => output.mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)))
      (executed Reference state)
    refine observed.trans ((ExecutionState.executionState_mapClassical_comp state
      (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2))))
      (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))).trans ?_)
    congr 1
    funext entry
    simp only [Function.comp_def, values, Store.read_write_same,
      recoveredValue, trivial, dite_true]
  · rw [recoveryCircuit_nontrivial P trivial]
    obtain ⟨record, executed, values⟩ :=
      OrderRecovery.Native.recoveryInto_actualRecord_correct
        (quantumEnvironment := OrderOracle.interpretation P) P
        (recoverySpec P trivial) (sampleCount P)
        (retainedSample P) (outputRef P)
    have observed := congrArg
      (fun output => output.mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)))
      (executed Reference state)
    refine observed.trans ((ExecutionState.executionState_mapClassical_comp state
      (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2))))
      (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))).trans ?_)
    congr 1
    funext entry
    simp only [Function.comp_def, values, Store.read_write_same,
      recoveredValue, trivial, dite_false]
    rfl

/-- Actual result allocation preserves the complete sample vector supplied to
the same recovery record. -/
public lemma retainedRecovery_read (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference
      ((OrderExecution.model P).HiddenState × History)) :
    ((retainedRecovery P).execute (OrderExecution.sourceEnvironment P) Reference state).mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)) =
      (retainedState P state).mapClassical (fun entry => recoveredValue P
        (.fixedVector fun index => entry.1.read (retainedSample P index))) := by
  rw [retainedRecovery_sequence]
  have first := sequence_read (environment := OrderExecution.sourceEnvironment P)
    (outputAllocation P) (recoveryCircuit P) state
    (fun store => store.read (.storage (outputRef P).toCStorageRef))
  refine first.trans ?_
  rw [outputRetain_execute]
  exact recoveryCircuit_read P (retainedState P state)

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
