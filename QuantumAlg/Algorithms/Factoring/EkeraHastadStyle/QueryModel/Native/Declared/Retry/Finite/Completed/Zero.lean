/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.AllKeys
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.SelectionAll.Reference

/-!
# Independent classical zero-batch EH execution

Requesting no quantum batch allocates one real empty optional result. Its
complete caller/reference state is unchanged; no quantum bank or native event
is introduced. The full contract and classical schedule concern this explicit
retained-cell circuit and do not invoke another algorithm.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The actual zero-batch branch allocates only its initialized optional factor cell. -/
def zeroAlgorithm (N : Nat) :
    Algorithm (model N) base (zeroContext base N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run :=
    { code := .retain (model := model N) base base.canonicalFreshKey
        (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh
      output := Output.all (zeroContext base N)
        (.read (.storage (zeroRef base N).toCStorageRef)) }

variable (N : Nat)
variable {environment : (model N).Environment}

/-- Zero actual batches return the initialized empty option with certainty. -/
private lemma zeroAlgorithm_output_none {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (zeroAlgorithm base N).run.outputDistribution environment original .optionNone = 1 := by
  rw [AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  change ENNReal.ofReal
    (((Circuit.retain (model := model N) base base.canonicalFreshKey
      (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh).execute
        environment Reference (original.state.mapClassical
        (fun entry => (entry.1, (entry.2, entry.1))))).effectWeight
      (fun entry => if entry.1.read (.storage (zeroRef base N).toCStorageRef) =
        CShape.Value.optionNone then
          Effect.one (Register.prod (zeroContext base N).register Reference)
        else Effect.zero (Register.prod (zeroContext base N).register Reference))) = 1
  have observed_mass :
      original.state.effectWeight (fun entry =>
        if (entry.1.pushRetained base.canonicalFreshKey
          (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh).read
          (.storage (zeroRef base N).toCStorageRef) = CShape.Value.optionNone then
            Effect.one (Register.prod (zeroContext base N).register Reference)
          else Effect.zero (Register.prod (zeroContext base N).register Reference)) =
        original.state.mass := by
    unfold ExecutionState.effectWeight ExecutionState.mass
    apply Finset.sum_congr rfl
    intro entry _
    change (if (entry.1.pushRetained base.canonicalFreshKey
      (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh).read
      (.storage (CStorageRef.retainedHead base base.canonicalFreshKey
        (.option (.unsignedWord (modulusBits N))) base.canonicalFreshKey_fresh)) =
        CShape.Value.optionNone then
          Effect.one (Register.prod (zeroContext base N).register Reference)
        else Effect.zero (Register.prod (zeroContext base N).register Reference)).weight
          (original.state.block entry) = (original.state.block entry).mass
    rw [if_pos (by rfl)]
    change (Effect.one (Register.prod base.register Reference)).weight
      (original.state.block entry) = (original.state.block entry).mass
    exact Effect.weight_one _
  rw [Circuit.execute_retain, ExecutionState.effectWeight_mapClassical_decision]
  rw [ExecutionState.effectWeight_mapClassical_decision]
  exact (congrArg ENNReal.ofReal observed_mass).trans
    ((congrArg ENNReal.ofReal original.normalized).trans ENNReal.ofReal_one)

/-- The actual zero-count allocation has exactly the pure empty optional-output law. -/
lemma zeroAlgorithm_outputDistribution {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (zeroAlgorithm base N).run.outputDistribution environment original =
      PMF.pure CShape.Value.optionNone := by
  have empty := zeroAlgorithm_output_none (environment := environment) base N original
  have supported := (PMF.apply_eq_one_iff _ _).mp empty
  apply PMF.ext
  intro value
  by_cases same : value = CShape.Value.optionNone
  · subst value
    exact empty.trans (PMF.pure_apply_self _).symm
  · have absent : value ∉
        ((zeroAlgorithm base N).run.outputDistribution environment original).support := by
      simpa only [supported, Set.mem_singleton_iff] using same
    have zero : (zeroAlgorithm base N).run.outputDistribution environment original value = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using absent
    exact zero.trans (PMF.pure_apply_of_ne _ _ same).symm

private lemma zeroAlgorithm_outputState {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    ((zeroAlgorithm base N).run.finalState environment Reference original.state).mapClassical
        (zeroAlgorithm base N).run.output.eval =
      original.state.mapClassical
        (fun _ => (.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value)) := by
  let enter := fun entry : Store base × (model N).HiddenState =>
    (entry.1, (entry.2, entry.1))
  let record : Store base × (model N).HiddenState → (zeroAlgorithm base N).run.Record :=
    fun entry =>
      (entry.1.pushRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
        base.canonicalFreshKey_fresh, (entry.2, (entry.1, ())))
  have actual : (zeroAlgorithm base N).run.execute environment Reference original.state =
      original.state.mapClassical record := by
    have retained := (Circuit.execute_retain (environment := environment) (model := model N)
      (original.state.mapClassical enter)
      base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
      base.canonicalFreshKey_fresh).trans
        (ExecutionState.executionState_mapClassical_comp original.state enter
          (fun entry =>
            (entry.1.pushRetained base.canonicalFreshKey
              (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh,
                (entry.2.1, (entry.2.2, ())))))
    exact retained.trans (ExecutionState.executionState_mapClassical_congr_decision
      original.state _ record (fun _ => rfl) _ _)
  have observed := congrArg
    (fun final : ExecutionState (zeroAlgorithm base N).run.Record
        (Register.prod base.register Reference) =>
      final.mapClassical (zeroAlgorithm base N).run.result) actual
  exact (AlgorithmRun.finalState_readout (zeroAlgorithm base N).run
    environment Reference original.state).trans
    (observed.trans (ExecutionState.executionState_mapClassical_comp
      original.state record (zeroAlgorithm base N).run.result))

private lemma zeroAlgorithm_statePromise {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed original.caller.state.quantumMarginal
      ((ExecutionState.quantumMarginal_mass original.caller.state).trans
        original.caller.normalized)).Holds
      ((((zeroAlgorithm base N).run.finalState environment Reference original.state).mapClassical
        (zeroAlgorithm base N).run.output.eval).block value) := by
  change ((((zeroAlgorithm base N).run.finalState environment Reference original.state).mapClassical
    (zeroAlgorithm base N).run.output.eval).block value).matrix =
      (((((zeroAlgorithm base N).run.finalState environment Reference original.state).mapClassical
        (zeroAlgorithm base N).run.output.eval).block value).mass : ℝ) •
          original.caller.state.quantumMarginal.matrix
  rw [OracleInput.oracleInput_caller_quantumMarginal, zeroAlgorithm_outputState]
  by_cases empty : value = .optionNone
  · subst value
    rw [ExecutionState.executionState_mapClassical_const_block]
    change original.state.quantumMarginal.matrix =
      original.state.quantumMarginal.mass • original.state.quantumMarginal.matrix
    rw [(ExecutionState.quantumMarginal_mass original.state).trans original.normalized]
    simp only [one_smul]
  · have absent :
        (original.state.mapClassical
          (fun _ => (.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value))).block
            value = DensityOperator.zero _ := by
      apply DensityOperator.ext
      rw [ExecutionState.mapClassical_block_matrix]
      simp only [Ne.symm empty, if_false, Finset.sum_const_zero, DensityOperator.zero_matrix]
    rw [absent]
    exact StatePromise.holds_zero (.mixed original.state.quantumMarginal
      ((ExecutionState.quantumMarginal_mass original.state).trans original.normalized))

/-- Zero requested batches realize the empty independent first-success law. -/
lemma zeroAlgorithm_sourceDistribution (input : Input N) {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (zeroAlgorithm base N).run.outputDistribution environment original =
      AllKeys.sourceDistribution input 0 := by
  rw [zeroAlgorithm_outputDistribution]
  simp only [AllKeys.sourceDistribution,
    ClassicalRoutines.FirstAccepted.Direct.Optional.Distribution.selectedDistribution,
    PMF.independentReplicateVector, PMF.pure_map,
    ClassicalRoutines.FirstAccepted.Direct.Optional.Distribution.firstValue,
    List.Vector.toList_nil, List.foldl_nil]

/-- The actual classical branch preserves every quantum/reference block at its readout. -/
lemma zeroAlgorithm_stateRequirement_holds {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (Cleanup.stateRequirement base noQuantum N 0).Holds original.caller
      ((zeroAlgorithm base N).run.finalState environment Reference original.state) := by
  exact fun value => StatePromise.mixed_fullSelection
    (zeroContext base N).quantumLayout Reference original.caller.state.quantumMarginal
    ((ExecutionState.quantumMarginal_mass original.caller.state).trans
      original.caller.normalized) _ (zeroAlgorithm_statePromise base N original value)

/-- The independent classical branch meets all source, state and resource obligations. -/
lemma zeroAlgorithm_solves (input : Input N) :
    Algorithm.Solves (zeroAlgorithm base N)
      (AllKeys.problem base noQuantum input 0) := by
  constructor
  · intro environment _witness Reference original _valid _initialized
    change 1 - AllKeys.sourceFailure input ^ 0 ≤ _
    simp only [pow_zero, tsub_self, zero_le]
  · intro environment _witness Reference original _valid _initialized requirement present
    have same : requirement = Cleanup.stateRequirement base noQuantum N 0 :=
      List.mem_singleton.mp present
    subst requirement
    exact zeroAlgorithm_stateRequirement_holds base noQuantum N original
  · intro environment _witness Reference original _valid _initialized
    have empty : base.borrowedQuantumWires = [] := by
      have subset := base.borrowedQuantumWires_sublist
      rw [noQuantum] at subset
      exact List.sublist_nil.mp subset
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (zeroAlgorithm base N).run.code environment empty reference state
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact le_rfl
  · intro _environment _witness _Reference _original _valid _initialized path _supported axis
    change max (base.residentSpace axis)
      (max (SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis +
        base.residentSpace axis) 0) ≤
      SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis + base.residentSpace axis
    omega
  · intro _environment _witness _Reference _original _valid _initialized path _supported axis
    change max (base.auxiliarySpace axis)
      (max (SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis +
        base.auxiliarySpace axis) 0) ≤
      SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) axis + base.auxiliarySpace axis
    omega
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact Nat.le_refl 0

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
