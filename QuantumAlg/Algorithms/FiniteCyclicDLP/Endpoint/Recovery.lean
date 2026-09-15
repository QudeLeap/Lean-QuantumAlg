/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection.Correctness
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Complete observed state of the original finite-cyclic recovery tail

The actual selector writes the first accepted candidate of the original raw
samples and the same borrowed target. Allocation supplies its only result
cell. The equality retains every quantum and external-reference coordinate;
it applies before any normalization or probability assumption.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

private theorem sequence_read {pre middle post : RuntimeCtx .quantum}
    (first : Circuit pre middle) (second : Circuit middle post)
    {Reference : Register} {History Value : Type} [Fintype History] [Fintype Value]
    (state : State pre Reference History) (read : Store post → Value) :
    ((first.seq second).execute Reference state).mapClassical (fun entry => read entry.1) =
      (second.execute Reference (first.execute Reference state)).mapClassical
        (fun entry => read entry.1) := by
  have executed := congrArg
    (fun output : State post Reference (History × (first.seq second).Path) =>
      output.mapClassical (fun entry => read entry.1))
    (Circuit.execute_seq first second state)
  refine executed.trans ?_
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]

/-- The original raw values and shared target determine the chronological checked candidate. -/
def recoveredValue (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (samples : (CShape.fixedVector (retryCount P)
      (.fixedVector (orderWidth P + orderWidth P) (.finite 2))).Value)
    (target : CShape.Word (orderWidth P)) :
    CShape.Value (.option (.unsignedWord (orderWidth P))) :=
  CallCountedRecovery.Native.groupRecoveryValue (recoveryParameters P B A)
    (retryCount P) samples.get target

/-- The complete classical tail reads its actual inputs and changes only the real output cell. -/
theorem finiteCyclic_recoveryCircuit_read (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (outputContext P) Reference History) :
    ((recoveryCircuit P B A).execute Reference state).mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)) =
      state.mapClassical (fun entry =>
        CallCountedRecovery.Native.groupRecoveryValue (recoveryParameters P B A)
          (retryCount P) (fun index => entry.1.read (retainedSample P index))
          (entry.1.read (retainedTarget P))) := by
  obtain ⟨record, executed, values⟩ :=
    CallCountedRecovery.Native.groupRecoveryInto_actualRecord_correct
      (recoveryParameters P B A) (retryCount P)
      (retainedSample P) (retainedTarget P) (outputRef P)
  have observed := congrArg
    (fun output : State (outputContext P) Reference
      (History × (recoveryCircuit P B A).Path) =>
      output.mapClassical (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)))
    (executed Reference state)
  refine observed.trans ((ExecutionState.executionState_mapClassical_comp state
    (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2)))
    (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))).trans ?_)
  congr 1
  funext entry
  simp only [Function.comp_def, values]
  exact Store.read_write_same _ _ _

/-- Actual result allocation preserves every original sample and the original borrowed target. -/
theorem finiteCyclic_retainedRecovery_read (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext P) Reference History) :
    ((retainedRecovery P B A).execute Reference state).mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)) =
      state.mapClassical (fun entry => recoveredValue P B A
        (entry.1.read (GateLevelAttempt.Native.Batch.samplesInput
          (pre P) (input_quantumWires P) P (retryCount P)))
        (entry.1.read (GateLevelAttempt.Native.Batch.liftInput
          (pre P) (input_quantumWires P) P (retryCount P) (targetRef P)))) := by
  have first := sequence_read
    (Circuit.retain (sampledContext P) (outputKey P)
      (.option (.unsignedWord (orderWidth P))) (outputKey_fresh P))
    (recoveryCircuit P B A) state
    (fun store => store.read (.storage (outputRef P).toCStorageRef))
  refine first.trans ((finiteCyclic_recoveryCircuit_read P B A _).trans ?_)
  change (state.mapClassical (fun entry =>
    (entry.1.pushRetained (outputKey P) (.option (.unsignedWord (orderWidth P)))
      (outputKey_fresh P), (entry.2, ())))).mapClassical
    (fun entry => recoveredValue P B A
      (.fixedVector fun index => entry.1.read (retainedSample P index))
      (entry.1.read (retainedTarget P))) = _
  refine (ExecutionState.executionState_mapClassical_comp state
    (fun entry => (entry.1.pushRetained (outputKey P)
      (.option (.unsignedWord (orderWidth P))) (outputKey_fresh P), (entry.2, ())))
    (fun entry => recoveredValue P B A
      (.fixedVector fun index => entry.1.read (retainedSample P index))
      (entry.1.read (retainedTarget P)))).trans ?_
  congr 1
  funext entry
  change recoveredValue P B A
    (.fixedVector fun index =>
      (entry.1.pushRetained (outputKey P) (.option (.unsignedWord (orderWidth P)))
        (outputKey_fresh P)).read (retainedSample P index))
    ((entry.1.pushRetained (outputKey P) (.option (.unsignedWord (orderWidth P)))
      (outputKey_fresh P)).read (retainedTarget P)) = _
  apply congrArg₂ (recoveredValue P B A)
  · simp only [retainedSample]
    rfl
  · exact Store.read_pushRetained_underRetained entry.1 _ _ _ _

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
