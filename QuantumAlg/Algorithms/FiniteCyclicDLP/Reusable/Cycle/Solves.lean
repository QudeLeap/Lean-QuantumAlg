/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Admission
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Reference
public import QuantumAlg.Core.Algorithm.AlgorithmRun.FixedOutput
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Protocol
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Probability

/-!
# One actual binary round reusableCycle_solves its independently specified sample protocol

The output distribution comes from the actual zero-seeded native word,
measurements and full terminal reset. Source success, every observed result's
fixed zero bank, borrowed restoration and path-wise resources all refer to
that one execution [Sho95, source.tex:1756-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable.Cycle

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The actual round output, decoded without an instruction, has its binary Born law. -/
public lemma reusableCycle_outputDistribution (P : KnownOrderProblem G) {count : Nat} (slot :
  Fin count)
    (expansion : OrderExpansion P.order) {Reference : Register}
    (input : OracleInput (model P).classicalOracles (context P count) Reference)
    (admitted : initialized P count input.localState) :
    ((algorithm P slot expansion).outputDistribution
      (sourceEnvironment P) input).map (observedOutcome P) =
      Binary.outcomePMF P expansion := by
  let entered : State (context P count) Reference
      ((model P).HiddenState × Store (context P count)) :=
    input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun entry => (entry.1, (entry.2, entry.1)))
  have pure : (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds
        entered.quantumMarginal.marginalLeft := by
    rw [show entered.quantumMarginal = input.state.quantumMarginal from
      ExecutionState.mapClassical_quantumMarginal _ _]
    exact input_pure P count input admitted
  have actual := round_toPMF P slot expansion entered normalized pure
  have executed :
      (algorithm P slot expansion).run.execute (sourceEnvironment P) Reference input.state =
        (round P slot expansion).execute (sourceEnvironment P) Reference entered := by
    dsimp only [algorithm, AlgorithmRun.execute]
    apply congrArg ((round P slot expansion).execute (sourceEnvironment P) Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  simp only [Algorithm.outputDistribution, AlgorithmRun.outputDistribution,
    AlgorithmRun.executionDistribution, executed, PMF.map_comp, Function.comp_def]
  dsimp (config := { instances := true }) only [algorithm, AlgorithmRun.Record]
  simpa only [AlgorithmRun.result, resultRead, Output.all, Output.eval,
    OutputRead.eval] using actual

/-- The source selected-family lower bound applies to this same actual round's relational law. -/
public lemma success (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) (secret : Input P) {Reference : Register}
    (input : OracleInput (model P).classicalOracles (context P count) Reference)
    (admitted : initialized P count input.localState) :
    ((problem P slot expansion).successLB (sourceEnvironment P) secret).value ≤
      ((algorithm P slot expansion).relationalDistribution
        (sourceEnvironment P) input).toOuterMeasure
        {pair | (problem P slot expansion).accepts (sourceEnvironment P) secret pair.1 pair.2} := by
  have source := Binary.binary_selected_probability P expansion secret
  rw [← reusableCycle_outputDistribution P slot expansion input admitted] at source
  simpa only [problem, successLowerBound, algorithm, Algorithm.outputDistribution,
    Algorithm.relationalDistribution, AlgorithmRun.outputDistribution,
    AlgorithmRun.relationalDistribution, PMF.toOuterMeasure_map_apply,
    Set.preimage, Set.mem_ofPred_eq] using source

/-- The complete native, measured and reset round meets all independent one-sample obligations. -/
public lemma reusableCycle_solves (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    Algorithm.Solves (algorithm P slot expansion) (problem P slot expansion) where
  success := by
    intro environment secret Reference input valid admitted
    have same : environment = sourceEnvironment P := valid
    subst environment
    exact success P slot expansion secret input admitted
  states := by
    intro environment witness Reference input valid _admitted
    have environmentEq : environment = sourceEnvironment P := valid
    subst environment
    intro requirement present
    have same : requirement = stateRequirement P slot := List.mem_singleton.mp present
    subst requirement
    exact AlgorithmRun.stateRequirement_of_reinitializedAt
      (algorithm P slot expansion).run (sourceEnvironment P) (zeroSeed P count)
      (round_reinitializedAt P slot expansion) (resultRead P slot) input
  borrowed := by
    intro environment witness Reference input valid _admitted
    have environmentEq : environment = sourceEnvironment P := valid
    subst environment
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (round_restartCleanup P slot expansion).restores reference state
  events := by
    intro _environment _witness _Reference _input _valid _admitted path _supported
    exact round_events_le P slot expansion path
  resident := by
    intro _environment _witness _Reference _input _valid _admitted path _supported
    exact (round_resident P slot expansion path).le
  auxiliary := by
    intro _environment _witness _Reference _input _valid _admitted path _supported
    exact (round_auxiliary P slot expansion path).le
  time := by
    intro _environment _witness _Reference _input _valid _admitted path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact round_depth_le P slot expansion path

end

end QuantumAlg.FiniteCyclicDLP.Reusable.Cycle
