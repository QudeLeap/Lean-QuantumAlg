/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Solves
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Distribution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Protocol
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Resources
import all QuantumAlg.Core.Execution.Restart.Sequence
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.State.History

/-!
# The first complete sample includes its actual physical preparation

The empty-input prefix prepares and allocates the one binary bank exactly
once. Its first Fourier sample and terminal reset form one complete intended
computation. All later samples start from that real reset, and the preparation
layer is charged to this first cycle [Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable.Cycle.First

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The real one-time prefix followed by one complete measured and reset sample. -/
public def code (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit (model P) pre (context P count) :=
  (initialCode P count).seq (round P slot expansion)

/-- Every result of the first complete sample has the fixed zero owned bank. -/
public def stateRequirement (P : KnownOrderProblem G) {count : Nat} (slot : Fin count) :
    StateRequirement pre (context P count) :=
  .marginal (context P count).borrowedSelectionᶜ (Cycle.resultRead P slot)
    (fun _ _ => .pure (NormalizedVector.ket (zeroSeed P count)))

/-- First complete source sampling protocol.

**Input.** Empty executable input, with arbitrary external reference and hidden
classical group-service state.
**Output.** The designated retained Fourier sample, all live entries, and a
fixed zero bank in every actual output fiber.
**Resource budget.** One binary-bank preparation, one native sampling word,
all exponent measurements and one full terminal reset; at most one additional
preparation layer beyond the independent round depth.
**Success.** The original selected Fourier event has probability at least
`N phi(N)/(4q^2)`.
**Source.** [Sho95, source.tex:1713-1984]; [dW19, qcnotes.tex:5409-5420].
-/
@[expose] public def problem (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    Problem (model P) pre (context P count) (.fixedVector (sampleWidth P) (.finite 2)) where
  Witness := Input P
  valid := fun environment _ _ => environment = sourceEnvironment P
  initialization := fun _ _ _ => True
  accepts := fun _ secret _ value => Probability.SelectedOutcome P secret (observedOutcome P value)
  successLB := fun _ _ => Cycle.successLowerBound P
  states := fun _ _ => [stateRequirement P slot]
  resources := {
    events := eventBudget P 1 expansion
    resident := (context P count).residentSpace
    auxiliary := (context P count).auxiliarySpace }
  quantumTimeLimit := 1 + roundUnitDepth P expansion

/-- The sole first-cycle implementation retains the actual first sample and all live entries. -/
public def algorithm (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    Algorithm (model P) pre (context P count) (.fixedVector (sampleWidth P) (.finite 2)) where
  run := ⟨code P slot expansion, Output.all (context P count) (Cycle.resultRead P slot)⟩

/-- Actual initial preparation supplies the first sample's full binary Born law. -/
public lemma reusableFirst_outputDistribution (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order) {Reference : Register}
    (input : OracleInput (model P).classicalOracles pre Reference) :
    ((algorithm P slot expansion).outputDistribution
      (sourceEnvironment P) input).map (observedOutcome P) =
      Binary.outcomePMF P expansion := by
  let entered : State pre Reference ((model P).HiddenState × Store pre) :=
    input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun entry => (entry.1, (entry.2, entry.1)))
  have actual := initial_round_toPMF P slot expansion entered normalized
  have executed :
      (algorithm P slot expansion).run.execute (sourceEnvironment P) Reference input.state =
        ((initialCode P count).seq (round P slot expansion)).execute
          (sourceEnvironment P) Reference entered := by
    dsimp only [algorithm, code, AlgorithmRun.execute]
    apply congrArg (((initialCode P count).seq (round P slot expansion)).execute
      (sourceEnvironment P) Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  simp only [Algorithm.outputDistribution, AlgorithmRun.outputDistribution,
    AlgorithmRun.executionDistribution, executed, PMF.map_comp, Function.comp_def]
  dsimp (config := { instances := true }) only [algorithm, code, AlgorithmRun.Record]
  simpa only [AlgorithmRun.result, Cycle.resultRead, Output.all, Output.eval,
    OutputRead.eval] using actual

/-- The first actual sample has the same full selected-family source probability. -/
public lemma reusableFirst_success (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order) (secret : Input P)
    {Reference : Register} (input : OracleInput (model P).classicalOracles pre Reference) :
    ((problem P slot expansion).successLB (sourceEnvironment P) secret).value ≤
      ((algorithm P slot expansion).relationalDistribution
        (sourceEnvironment P) input).toOuterMeasure
        {pair | (problem P slot expansion).accepts (sourceEnvironment P) secret pair.1 pair.2} := by
  have source := Binary.binary_selected_probability P expansion secret
  rw [← reusableFirst_outputDistribution P slot expansion input] at source
  simpa only [problem, Cycle.successLowerBound, algorithm, Algorithm.outputDistribution,
    Algorithm.relationalDistribution, AlgorithmRun.outputDistribution,
    AlgorithmRun.relationalDistribution, PMF.toOuterMeasure_map_apply,
    Set.preimage, Set.mem_ofPred_eq] using source

/-- The first preparation cannot alter the predetermined terminal reset state. -/
public lemma reusableFirst_reinitializedAt (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit.ReinitializedAt (code P slot expansion)
      (sourceEnvironment P) (zeroSeed P count) :=
  QuantumAlg.Circuit.RestartCleanup.afterAt (initialCode P count) (round P slot expansion)
    (sourceEnvironment P)
    (zeroSeed P count) (round_reinitializedAt P slot expansion)

/-- The first actual cycle also has measured, full-reference physical restart. -/
public lemma restartCleanup (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit.RestartCleanup (code P slot expansion) (sourceEnvironment P) :=
  QuantumAlg.Circuit.RestartCleanup.after (initialCode P count) (round P slot expansion)
    (sourceEnvironment P)
    (by
      intro Reference History _ state
      exact QuantumAlg.Circuit.borrowedRestored_of_noBorrowedQuantum
        (initialCode P count) (sourceEnvironment P) RuntimeCtx.borrowedQuantumWires_empty
          Reference state)
    (round_restartCleanup P slot expansion)

/-- The initial physical layer and one actual round obey their independent depth allowance. -/
public lemma reusableFirst_depth_le (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order) (path : (code P slot expansion).Path) :
    (code P slot expansion).depth (fun _ => 1) path ≤ 1 + roundUnitDepth P expansion :=
  Nat.add_le_add (initialCode_depth_le P count path.1) (round_depth_le P slot expansion path.2)

/-- Every actual first-cycle path pays the same physical preparation and full reset ledger. -/
public lemma reusableFirst_events_le (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order) (path : (code P slot expansion).Path) :
    (code P slot expansion).resourcePool path ≤ eventBudget P 1 expansion := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append, ← QuantumAlg.Circuit.resourcePool,
    ← QuantumAlg.Circuit.resourcePool, initialCode_events]
  simpa only [eventBudget, ResourcePool.scale, one_nsmul] using
    add_le_add (le_refl (ZeroPreparation.eventCost AlgorithmGate.model (Binary.Oracle.model P)
      (Binary.Oracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G)))
      (round_events_le P slot expansion path.2)

/-- Complete first-sample correctness keeps its actual preparation, output state and resources. -/
public lemma reusableFirst_solves (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    Algorithm.Solves (algorithm P slot expansion) (problem P slot expansion) where
  success := by
    intro environment secret Reference input valid _initialized
    have same : environment = sourceEnvironment P := valid
    subst environment
    exact reusableFirst_success P slot expansion secret input
  states := by
    intro environment witness Reference input valid _initialized
    have environmentEq : environment = sourceEnvironment P := valid
    subst environment
    intro requirement present
    have same : requirement = stateRequirement P slot := List.mem_singleton.mp present
    subst requirement
    exact AlgorithmRun.stateRequirement_of_reinitializedAt
      (algorithm P slot expansion).run (sourceEnvironment P) (zeroSeed P count)
      (reusableFirst_reinitializedAt P slot expansion) (Cycle.resultRead P slot) input
  borrowed := by
    intro environment witness Reference input valid _initialized
    have environmentEq : environment = sourceEnvironment P := valid
    subst environment
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (restartCleanup P slot expansion).restores reference state
  events := by
    intro _environment _witness _Reference _input _valid _initialized path _supported
    exact reusableFirst_events_le P slot expansion path
  resident := by
    intro _environment _witness _Reference _input _valid _initialized path _supported
    exact (QuantumAlg.Circuit.peakResidentSpace_seq
      (initialCode P count) (round P slot expansion) path).trans_le
        (SpacePool.max_le (initialCode_resident_le P count path.1)
          ((round_resident P slot expansion path.2).le))
  auxiliary := by
    intro _environment _witness _Reference _input _valid _initialized path _supported
    exact (QuantumAlg.Circuit.peakAuxiliarySpace_seq
      (initialCode P count) (round P slot expansion) path).trans_le
        (SpacePool.max_le (initialCode_auxiliary_le P count path.1)
          ((round_auxiliary P slot expansion path.2).le))
  time := by
    intro _environment _witness _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact reusableFirst_depth_le P slot expansion path

/-- The next cycle receives the same actual stored state, already reset by the first sample. -/
public lemma reusableFirst_nextInput_initialized (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order) {Reference : Register}
    (input : OracleInput (model P).classicalOracles pre Reference) :
    Cycle.initialized P count ((code P slot expansion).nextInput
      (sourceEnvironment P) input).localState := by
  unfold Cycle.initialized
  rw [Cycle.reusableCycle_localState_quantumMarginal]
  change (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
    (context P count).quantumLayout.zeroLabel)).Holds
      (((code P slot expansion).execute (sourceEnvironment P) Reference
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
          (fun record => (record.1, record.2.1))).quantumMarginal.marginalLeft
  rw [ExecutionState.mapClassical_quantumMarginal, code,
    QuantumAlg.Circuit.execute_seq, State.mapHistory_quantumMarginal]
  exact round_pure P slot expansion _

end

end QuantumAlg.FiniteCyclicDLP.Reusable.Cycle.First
