/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Reference
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Output.Reference

/-!
# The actual chronological factor-vector distribution of the finite retry chain

The first batch's full reference law and its actual deterministic recovery
establish the initial factor law. Its genuinely fresh result is separate
from the original measurement cells, and its actual code establishes the
bank seed. The subsequent joint suffix law therefore has no remaining
initialization, separation, source-support or independence premise.

The real complete Output reads all chronological factor cells. Its PMF is
the existing independent vector PMF for exactly one first batch and `count`
later batches, followed solely by the structural typed-vector encoding.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] RuntimeResults.context RuntimeResults.liftInput
  RuntimeResults.liftWrite RuntimeResults.input ExecutionState.referenceFiberSum

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

private lemma firstCells_result_separate (index : Fin (measurementBits N)) :
    (firstCells base noQuantum N index).key ∉
      (CInputRef.storage
        (NativeBatchRecovery.resultRef base noQuantum N).toCStorageRef).storageKeys := by
  let before := RuntimeResults.liftWrite (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatch.cells base noQuantum N index) 16
  intro present
  have same := List.mem_singleton.mp present
  apply (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh
  have live : before.key ∈ (NativeBatch.context base noQuantum N).keys :=
    List.mem_map_of_mem before.toCStorageRef.present
  have keyEq : before.key = (NativeBatch.context base noQuantum N).canonicalFreshKey := same
  exact keyEq ▸ live

private lemma output_read (input : Input N) (count : Nat)
    (store : Store (context base noQuantum N count)) :
    (run base noQuantum input count).output.eval store =
      .fixedVector (List.Vector.cons
        (store.read (suffixInput N
          (.storage (NativeBatchRecovery.resultRef base noQuantum N).toCStorageRef) count))
        (suffixValues N (NativeBatchRecovery.context base noQuantum N) count store)).get := by
  change CShape.Value.fixedVector (fun index =>
    store.read (resultRefs base noQuantum N count index)) = _
  apply congrArg CShape.Value.fixedVector
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · exact (congrArg (fun ref => store.read ref)
      (suffixInput_storage N (NativeBatchRecovery.resultRef base noQuantum N) count)).symm
  · simp only [List.Vector.get_cons_succ, suffixValues, List.Vector.get_ofFn]
    rfl

attribute [local irreducible] NativeBatch.context NativeBatch.code
  NativeBatchRecovery.body NativeBatchRecovery.tail NativeBatchRecovery.step

private lemma first_output_on_source_support (input : Input N)
    (store : Store (NativeBatch.context base noQuantum N))
    (hidden : RuntimeRound.model.HiddenState)
    (supported : (NativeBatch.run base noQuantum N).output.eval store ∈
      (NativeBatch.sourceDistribution input).support) :
    (NativeBatchRecovery.run base noQuantum input).output.eval
        (NativeBatchRecovery.step base noQuantum input (store, hidden)).1.1 =
      NativeBatchRecovery.packedValue ((NativeBatch.run base noQuantum N).output.eval store) := by
  have readParameter : ((NativeBatch.run base noQuantum N).output.eval store).second.first =
      store.read (NativeBatch.finalParameter base noQuantum N) := by
    unfold NativeBatch.run NativeBatch.resultShape
    rw [Output.all_eval, OutputRead.eval_read]
    exact NativeBatchRecovery.read_middle store (NativeBatch.finalSample base noQuantum N)
      (NativeBatch.finalParameter base noQuantum N) (NativeBatch.finalResults base noQuantum N)
  have parameterStored := readParameter.symm.trans
    (NativeBatchRecovery.sourceDistribution_parameter input _ supported)
  exact (NativeBatchRecovery.run_output base noQuantum input
    (NativeBatchRecovery.decodeSource ((NativeBatch.run base noQuantum N).output.eval store))
    store hidden parameterStored).trans
    (NativeBatchRecovery.packedValue_sourceOutput base noQuantum store).symm

/-- The actual first recovered factor has its full original reference kernel for any history. -/
lemma first_weighted_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((NativeBatchRecovery.code base noQuantum input).execute environment Reference state)
        (fun entry _ => weight
          ((NativeBatchRecovery.run base noQuantum input).output.eval entry.1))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            factor).toReal : ℂ) * weight factor) leftRef rightRef := by
  let sourceState := (NativeBatch.code base noQuantum N).execute environment Reference state
  have supported (entry : Store (NativeBatch.context base noQuantum N) ×
      (RuntimeRound.model.HiddenState × (History × (NativeBatch.code base noQuantum N).Path)))
      (positive : 0 < (sourceState.block entry).mass) :
      (NativeBatch.run base noQuantum N).output.eval entry.1 ∈
        (NativeBatch.sourceDistribution input).support :=
    NativeBatchReuseRecovery.read_mem_support_of_reference state sourceState
      (fun record => (NativeBatch.run base noQuantum N).output.eval record.1)
      (NativeBatch.sourceDistribution input)
      (NativeBatch.nativeBatch_output_indicator_reference base noQuantum input state)
      entry positive
  have tailLaw := NativeBatchReuseRecovery.retained_reference (environment := environment)
    (NativeBatchRecovery.tail base noQuantum input)
    (NativeBatchRecovery.step base noQuantum input)
    (NativeBatchRecovery.tail_execute base noQuantum input) sourceState
    (fun store => weight ((NativeBatchRecovery.run base noQuantum input).output.eval store))
    leftRef rightRef
  have recovered := NativeBatchReuseRecovery.reference_eq_on_support sourceState
    (fun entry _ => weight ((NativeBatchRecovery.run base noQuantum input).output.eval
      (NativeBatchRecovery.step base noQuantum input (entry.1, entry.2.1)).1.1))
    (fun entry _ => weight (NativeBatchRecovery.packedValue
      ((NativeBatch.run base noQuantum N).output.eval entry.1)))
    (fun entry positive _ => congrArg weight
      (first_output_on_source_support base noQuantum input entry.1 entry.2.1
        (supported entry positive)))
    leftRef rightRef
  have sourceLaw := NativeBatch.nativeBatch_output_weighted_reference (environment := environment)
    base noQuantum input state
    (fun output => weight (NativeBatchRecovery.packedValue output)) leftRef rightRef
  have mapped := (PMF.sum_map_toReal_mul (NativeBatch.sourceDistribution input)
    NativeBatchRecovery.packedValue weight).symm
  rw [NativeBatchRecovery.sourceDistribution_map_packedValue input] at mapped
  have mappedLaw := congrArg (fun coefficient : ℂ =>
    ExecutionState.referenceFiberSum state (fun _ _ => coefficient) leftRef rightRef) mapped
  exact (Circuit.referenceFiberSum_execute_seq (environment := environment)
    (NativeBatch.code base noQuantum N)
    (NativeBatchRecovery.tail base noQuantum input) state
    (fun store => weight ((NativeBatchRecovery.run base noQuantum input).output.eval store))
    leftRef rightRef).trans (tailLaw.trans (recovered.trans (sourceLaw.trans mappedLaw)))

/-- All actual chronological factors have the original vector kernel in every reference entry. -/
lemma code_weighted_reference (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (weight : (CShape.fixedVector (count + 1)
      (LatticeBatchRecoveryOutput.OutputShape N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum input count).execute
      environment Reference state)
        (fun entry _ => weight ((run base noQuantum input count).output.eval entry.1))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ output : (CShape.fixedVector (count + 1)
            (LatticeBatchRecoveryOutput.OutputShape N)).Value,
          ((((PMF.independentReplicateVector
            ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            (count + 1)).map (fun values => CShape.Value.fixedVector values.get))
              output).toReal : ℂ) * weight output) leftRef rightRef := by
  let first := NativeBatchRecovery.code base noQuantum input
  let previous : CInputRef (NativeBatchRecovery.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
    .storage (NativeBatchRecovery.resultRef base noQuantum N).toCStorageRef
  let rest := suffixCode input (NativeBatchRecovery.context base noQuantum N)
    (firstWires base noQuantum N) (firstCells base noQuantum N) count
  let advanced := first.execute environment Reference state
  let restWeight := fun factor : (LatticeBatchRecoveryOutput.OutputShape N).Value =>
    fun values : List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value count =>
      weight (.fixedVector (List.Vector.cons factor values).get)
  have restLaw := suffix_weighted_reference (environment := environment) input count
    (NativeBatchRecovery.context base noQuantum N) (firstWires base noQuantum N) previous
    (firstCells base noQuantum N) (cells_distinct base noQuantum N 0)
    (firstCells_result_separate base noQuantum) advanced
    (NativeBatchRecovery.code_seedBlocks base noQuantum input state) restWeight leftRef rightRef
  have aligned := congrArg
    (fun read : Store (context base noQuantum N count) → ℂ =>
      ExecutionState.referenceFiberSum (rest.execute environment Reference advanced)
        (fun entry _ => read entry.1) leftRef rightRef)
    (funext fun store => congrArg weight (output_read base noQuantum input count store))
  have firstLaw := first_weighted_reference (environment := environment) base noQuantum input state
    (fun factor => ∑ values : List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value count,
      ((PMF.independentReplicateVector
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        count values).toReal : ℂ) * restWeight factor values) leftRef rightRef
  have vectorLaw := (PMF.independentReplicateVector_weighted_cons
    ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue) count
    (fun values => weight (.fixedVector values.get))).symm
  have encodedLaw := (PMF.sum_map_toReal_mul
    (PMF.independentReplicateVector
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue) (count + 1))
    (fun values => CShape.Value.fixedVector values.get) weight).symm
  have kernelLaw := congrArg (fun coefficient : ℂ => ExecutionState.referenceFiberSum state
    (fun _ _ => coefficient) leftRef rightRef) (vectorLaw.trans encodedLaw)
  exact (Circuit.referenceFiberSum_execute_seq (environment := environment) first rest state
    (fun store => weight ((run base noQuantum input count).output.eval store))
    leftRef rightRef).trans (aligned.trans (restLaw.trans (firstLaw.trans kernelLaw)))

/-- The actual complete run reads exactly the independent chronological typed factor vector. -/
lemma run_outputDistribution (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference) :
    (run base noQuantum specification count).outputDistribution environment input =
      (PMF.independentReplicateVector
        ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue)
        (count + 1)).map (fun values => CShape.Value.fixedVector values.get) := by
  let program := run base noQuantum specification count
  let entered : State base Reference (RuntimeRound.model.HiddenState × Store base) :=
    input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have enter : program.execute environment Reference input.state =
      (code base noQuantum specification count).execute environment Reference entered := rfl
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum input.state
    (program.execute
      environment Reference input.state) input.normalized (program.execute_normalized environment
        input)
    program.result _
  intro selected leftRef rightRef
  have actual := congrArg
    (fun final : ExecutionState program.Record
        ((context base noQuantum N count).register.prod Reference) =>
      ExecutionState.referenceFiberSum final
        (fun entry _ => if program.result entry = selected then 1 else 0)
        leftRef rightRef) enter
  have observed := code_weighted_reference (environment := environment)
    base noQuantum specification count entered
    (fun output => if output = selected then 1 else 0) leftRef rightRef
  have collapsed := congrArg
    (fun coefficient : ℂ => ExecutionState.referenceFiberSum entered
      (fun _ _ => coefficient) leftRef rightRef)
    (PMF.sum_toReal_indicator
      ((PMF.independentReplicateVector
        ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue)
        (count + 1)).map (fun values => CShape.Value.fixedVector values.get)) selected)
  exact actual.trans (observed.trans (collapsed.trans
    (ExecutionState.referenceFiberSum_mapClassical input.state
      (fun entry => (entry.1, (entry.2, entry.1))) (fun _ _ => _) leftRef rightRef)))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain
