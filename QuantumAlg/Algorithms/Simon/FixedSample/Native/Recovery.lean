/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Probability
import all QuantumAlg.Algorithms.Simon.FixedSample.Probability
import all QuantumAlg.Components.Classical.GF2.Native.Retained.Run
import all QuantumAlg.Core.Execution.MappedTail

/-!
# Actual fixed-sample Simon recovery

The measured sample slots feed the original retained GF(2) recovery exactly
once. Every sampled quantum wire and caller cell remains listed in the final
Output. The complete executed state determines the output PMF; the original
finite-sample Simon bound is used only after identifying that same joint law.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

universe u

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma mapped_decision {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (firstDecision secondDecision : DecidableEq D) (state : ExecutionState C R)
    (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R firstDecision state update =
      @ExecutionState.mapClassical C D _ _ R secondDecision state update := by
  cases Subsingleton.elim firstDecision secondDecision
  rfl

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)
  {environment : (executionModel n).Environment}

/-- The real recovery retains its optional result beside the complete sampled context. -/
def recoveryContext : RuntimeCtx .quantum :=
  let ctx := context base noQuantum n count
  ClassicalRoutines.GF2.Native.retainedCtx ctx n ctx.canonicalFreshKey ctx.canonicalFreshKey_fresh

/-- Read the actual retained optional word. -/
def recoveryRead : CInputRef (recoveryContext base noQuantum n count)
    (.option (.unsignedWord n)) :=
  let ctx := context base noQuantum n count
  ClassicalRoutines.GF2.Native.retainedRead ctx n ctx.canonicalFreshKey ctx.canonicalFreshKey_fresh

/-- Sample into the real fixed slots, then execute the original polynomial recovery. -/
def recoveryCode (sampling : SamplingCircuit n) :
    Circuit (executionModel n) base (recoveryContext base noQuantum n count) :=
  let ctx := context base noQuantum n count
  .seq (code base noQuantum n count sampling)
    (ClassicalRoutines.GF2.Native.retainedCircuit (model := executionModel n)
      (samplesInput base noQuantum n count)
      ctx.canonicalFreshKey ctx.canonicalFreshKey_fresh)

/-- One actual sampling-and-recovery run with every surviving resource explicitly listed. -/
def recoveryRun (sampling : SamplingCircuit n) :
    AlgorithmRun (executionModel n) base
      (recoveryContext base noQuantum n count) (.option (.unsignedWord n)) where
  code := recoveryCode base noQuantum n count sampling
  output := Output.all (recoveryContext base noQuantum n count)
    (.read (recoveryRead base noQuantum n count))

/-- No sampled bank, result slot or caller entry is omitted from the output. -/
lemma nativeSimon_recovery_output_listing (sampling : SamplingCircuit n) :
    (recoveryRun base noQuantum n count sampling).output.listing =
      (recoveryContext base noQuantum n count).keys := rfl

/-- The complete final state is the actual sampled state followed by the real retained write. -/
lemma nativeSimon_recovery_finalState (sampling : SamplingCircuit n) (Reference : Register)
    (state : ExecutionState (Store base × Unit) (Register.prod base.register Reference)) :
    (recoveryRun base noQuantum n count sampling).finalState environment Reference state =
      ((run base noQuantum n count sampling).finalState environment Reference state).mapClassical
        (fun before =>
          let ctx := context base noQuantum n count
          (before.pushRetained ctx.canonicalFreshKey (.option (.unsignedWord n))
            ctx.canonicalFreshKey_fresh).write
            (CWriteRef.retainedHead ctx ctx.canonicalFreshKey (.option (.unsignedWord n))
              ctx.canonicalFreshKey_fresh)
            (ClassicalRoutines.GF2.Native.gf2RecoveryValue
              (before.read (samplesInput base noQuantum n count)))) := by
  let ctx := context base noQuantum n count
  let input := samplesInput base noQuantum n count
  obtain ⟨record, executed, correct⟩ :=
    ClassicalRoutines.GF2.Native.gf2Retained_actualRecord_correct (environment := environment)
      (model := executionModel n) input
      ctx.canonicalFreshKey ctx.canonicalFreshKey_fresh
  have actual := Circuit.execute_seq_retained_mapClassical_tail
    (environment := environment) ctx.canonicalFreshKey
    (.option (.unsignedWord n)) ctx.canonicalFreshKey_fresh
    (code base noQuantum n count sampling)
    (ClassicalRoutines.GF2.Native.retainedCircuit (model := executionModel n)
      input ctx.canonicalFreshKey
      ctx.canonicalFreshKey_fresh) record executed Reference
    (state.mapClassical (fun before => (before.1, (before.2, before.1))))
  let firstRun := run base noQuantum n count sampling
  let fullRun := recoveryRun base noQuantum n count sampling
  let update := fun entry : firstRun.Record =>
    let result := record (entry.1, entry.2.1)
    (result.1.1, (result.1.2, (entry.2.2.1, (entry.2.2.2, result.2))))
  let finalWrite := fun before : Store ctx =>
    (before.pushRetained ctx.canonicalFreshKey (.option (.unsignedWord n))
      ctx.canonicalFreshKey_fresh).write
      (CWriteRef.retainedHead ctx ctx.canonicalFreshKey (.option (.unsignedWord n))
        ctx.canonicalFreshKey_fresh)
      (ClassicalRoutines.GF2.Native.gf2RecoveryValue (before.read input))
  have joined : fullRun.execute environment Reference state =
      (firstRun.execute environment Reference state).mapClassical update := by
    refine actual.trans ?_
    exact mapped_decision (C := firstRun.Record) (D := fullRun.Record)
      _ _ (firstRun.execute environment Reference state) update
  change (fullRun.execute environment Reference state).mapClassical Prod.fst =
    ((firstRun.execute environment Reference state).mapClassical Prod.fst).mapClassical finalWrite
  rw [joined]
  refine (ExecutionState.executionState_mapClassical_comp
    (firstRun.execute environment Reference state) update Prod.fst).trans ?_
  refine Eq.trans ?_ (ExecutionState.executionState_mapClassical_comp
    (firstRun.execute environment Reference state) Prod.fst finalWrite).symm
  congr 1
  funext entry
  exact correct (entry.1, entry.2.1)

/-- Actual output blocks retain the sampled quantum-reference state grouped by recovery value. -/
lemma nativeSimon_recovery_readoutState (sampling : SamplingCircuit n) (Reference : Register)
    (state : ExecutionState (Store base × Unit) (Register.prod base.register Reference)) :
    ((recoveryRun base noQuantum n count sampling).execute environment Reference state).mapClassical
        (recoveryRun base noQuantum n count sampling).result =
      ((run base noQuantum n count sampling).execute environment Reference state).mapClassical
        (fun entry => ClassicalRoutines.GF2.Native.gf2RecoveryValue
          ((run base noQuantum n count sampling).result entry)) := by
  change ((recoveryRun base noQuantum n count sampling).execute environment
    Reference state).mapClassical
    (fun entry => (recoveryRun base noQuantum n count sampling).output.eval entry.1) = _
  rw [← AlgorithmRun.finalState_readout, nativeSimon_recovery_finalState
    (environment := environment)]
  erw [ExecutionState.executionState_mapClassical_comp,
    ExecutionState.executionState_mapClassical_comp]
  congr 1

private lemma mapped_probability {C D Value : Type} [Fintype C] [Fintype D] [Fintype Value]
    {R : Register} (first : ExecutionState C R) (second : ExecutionState D R)
    (firstNormalized : first.IsNormalized) (secondNormalized : second.IsNormalized)
    (firstRead : C → Value) (secondRead : D → Value)
    (same : first.mapClassical firstRead = second.mapClassical secondRead) :
    (first.toPMF firstNormalized).map firstRead =
      (second.toPMF secondNormalized).map secondRead := by
  apply PMF.ext
  intro value
  have left := congrArg (fun probability : PMF Value => probability value)
    (ExecutionState.toPMF_mapClassical first firstNormalized firstRead).symm
  have right := congrArg (fun probability : PMF Value => probability value)
    (ExecutionState.toPMF_mapClassical second secondNormalized secondRead)
  refine left.trans (Eq.trans ?_ right)
  simp only [ExecutionState.toPMF_apply, same]

/-- The actual recovery distribution is the original recovery applied to actual sample slots. -/
lemma nativeSimon_recovery_outputDistribution (sampling : SamplingCircuit n)
    {Reference : Register} (input : Execution.OracleInput .empty base Reference) :
    (recoveryRun base noQuantum n count sampling).outputDistribution environment input =
      ((run base noQuantum n count sampling).outputDistribution environment input).map
        ClassicalRoutines.GF2.Native.gf2RecoveryValue := by
  change (((recoveryRun base noQuantum n count sampling).execute environment Reference
    input.state).toPMF
      ((recoveryRun base noQuantum n count sampling).execute_normalized environment input)).map
      (recoveryRun base noQuantum n count sampling).result = _
  rw [AlgorithmRun.outputDistribution, PMF.map_comp]
  exact mapped_probability _ _ _ _ _ _
    (nativeSimon_recovery_readoutState
      (environment := environment) base noQuantum n count sampling Reference input.state)

private lemma recovery_value (value : (CShape.fixedVector count (.bits n)).Value) :
    ClassicalRoutines.GF2.Native.gf2RecoveryValue value =
      match ClassicalAlgorithms.GF2.recover? (batchSamples (sampleOutcomes n count value)) with
      | none => .optionNone
      | some word => .optionSome (.unsignedWord word) := by
  have decoded :
      (fun row => ClassicalAlgorithms.TerminalDecode.eval
        (ClassicalRoutines.TerminalDecode.decodeInput .bigEndian (value.get row))) =
        batchSamples (sampleOutcomes n count value) := by
    funext row
    simp only [batchSamples, sampleOutcomes, List.Vector.get_ofFn, decodeWord]
    cases value.get row with
    | bits bits => rfl
  unfold ClassicalRoutines.GF2.Native.gf2RecoveryValue
  rw [decoded]
  rfl

/-- The same executed output PMF is recovered from the original independent Born vector law. -/
lemma nativeSimon_recovery_bornDistribution (sampling : SamplingCircuit n)
    {Reference : Register} (input : Execution.OracleInput .empty base Reference) :
    (recoveryRun base noQuantum n count sampling).outputDistribution environment input =
      (PMF.independentReplicateVector (sampling.outcomePMF environment.quantum) count).map
        (fun batch => match ClassicalAlgorithms.GF2.recover? (batchSamples batch) with
          | none => CShape.Value.optionNone
          | some word => .optionSome (.unsignedWord word)) := by
  rw [nativeSimon_recovery_outputDistribution (environment := environment),
    ← nativeSimon_run_outputDistribution
      (environment := environment) base noQuantum n count sampling input, PMF.map_comp]
  congr 1
  funext value
  exact recovery_value n count value

/-- At the original count n + κ, the actual optional output equals the hidden word
with probability at least 1 - 2⁻κ. The circuit and input have no secret parameter. -/
lemma nativeSimon_recovery_success (sampling : SamplingCircuit n)
    (secret : Word n) (κ : SecurityParameter)
    (promise : SamplingPromise sampling environment.quantum secret) {Reference : Register}
    (input : Execution.OracleInput .empty base Reference) :
    1 - ((2 : ENNReal)⁻¹) ^ κ.value ≤
      (recoveryRun base noQuantum n (sampleCount n κ) sampling).outputDistribution environment input
        (.optionSome (.unsignedWord secret)) := by
  rw [nativeSimon_recovery_bornDistribution (environment := environment)]
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  refine (goodBatchMass_ge sampling environment.quantum secret κ promise).trans ?_
  apply MeasureTheory.OuterMeasure.mono
  intro batch good
  change (match ClassicalAlgorithms.GF2.recover? (batchSamples batch) with
    | none => CShape.Value.optionNone
    | some word => .optionSome (.unsignedWord word)) =
      .optionSome (.unsignedWord secret)
  rw [ClassicalAlgorithms.GF2.recover?_complete (batchSamples batch) secret good]

end

end QuantumAlg.SimonsProblem.FixedSample.Native
