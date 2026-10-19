/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Probability.Candidate
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Support
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Loop
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Boundary
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First.Loop
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Input.Oracle.Empty
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Prefix

/-!
# Finite success of the same actual allocated streaming recovery run

The actual allocation and seven-cell retention initialize the original
first-accepted latches. Each real prefix preserves both public point values
from the original problem input. The source-derived candidate floor applies
to every complete unnormalized failure fiber. The original native loop
therefore contracts its failure mass, and the actual final option pack
returns only the original secret when it returns a value.

Every probability concerns StreamingRecovery.run itself. All actual Paths, original
Store History, hidden state and arbitrary external Reference remain in its execution. No
independence, positive corrected floor, initialized caller bank or point-representation
premise is added. Zero requested rounds and a nonpositive corrected floor remain
covered. Resource bounds have separate theorem owners.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.FiniteSuccess

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP Canonical.Probability ECDLP.Measured
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

private lemma indicator_decision_weight {Records : Type} [Fintype Records] {R : Register}
    (state : ExecutionState Records R) (condition : Records → Prop)
    (first second : DecidablePred condition) :
    state.effectWeight (fun record => @ite (Effect R) (condition record) (first record)
      (Effect.one R) (Effect.zero R)) =
      state.effectWeight (fun record => @ite (Effect R) (condition record) (second record)
        (Effect.one R) (Effect.zero R)) := by
  cases Subsingleton.elim first second
  rfl

private lemma initialized_failure_weight {origin ctx : RuntimeCtx .quantum}
    (setup : Circuit Model origin ctx) (width scalarWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State origin Reference (Unit × History)) :
    persistentFailureWeight (model := Model) (ctx := ctx)
      (width := width) (scalarWidth := scalarWidth)
      ((setup.seq (retainPersistent (model := Model) ctx width scalarWidth)).execute environment
        Reference
        initial) =
        initial.mass := by
  exact (storedWeight_seq setup (retainPersistent (model := Model) ctx width scalarWidth) initial
    (fun stored => if (stored.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))).trans
    ((retainPersistent_failure_weight (model := Model) (ctx := ctx) width scalarWidth
      (setup.execute environment Reference initial)).trans
      (setup.execute_mass environment Reference initial))

private lemma initialized_selected_invariant {origin ctx : RuntimeCtx .quantum}
    (setup : Circuit Model origin ctx) (width scalarWidth order : Nat) (positiveOrder : 0 < order)
    (consequence : Store (persistentCtx ctx width scalarWidth) → Prop)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State origin Reference (Unit × History)) :
    storeSupported ((setup.seq (retainPersistent (model := Model) ctx width scalarWidth)).execute
      environment Reference initial)
      (fun stored =>
        (stored.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
          order ∧
        ((stored.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true → consequence stored)) := by
  let invariant : Store (persistentCtx ctx width scalarWidth) → Prop := fun stored =>
    (stored.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
      order ∧
    ((stored.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
      true → consequence stored)
  change storeSupported
    ((setup.seq (retainPersistent (model := Model) ctx width scalarWidth)).execute environment
      Reference
      initial) invariant
  refine (storeSupported_seq setup (retainPersistent (model := Model) ctx width scalarWidth)
    initial invariant).mpr ?_
  intro entry present
  have values := retainPersistent_latches_supported (environment := environment) (model := Model)
    (ctx := ctx) width scalarWidth
    (setup.execute environment Reference initial) entry present
  constructor
  · rw [values.2]
    change 0 % 2 ^ scalarWidth < order
    rw [Nat.zero_mod]
    exact positiveOrder
  · intro accepted
    exact False.elim (Bool.false_ne_true (values.1.symm.trans accepted))

private lemma support_execute_mapHistory {model : ExecutionModel}
    {environment : model.Environment}
    {origin result : RuntimeCtx model.kind}
    (code : Circuit model origin result) {Reference : Register}
    {Before After : Type} [Fintype Before] [Fintype After]
    (state : State origin Reference (model.HiddenState × Before)) (update : Before → After)
    (predicate : Store result → Prop) :
    storeSupported (code.execute environment Reference
      (state.mapHistory (fun record => (record.1, update record.2)))) predicate ↔
        storeSupported (code.execute environment Reference state) predicate := by
  rw [Circuit.execute_mapHistory code environment Reference state update, storeSupported_mapHistory]

private lemma four_stage_support {model : ExecutionModel}
    {environment : model.Environment}
    {origin first second final result : RuntimeCtx model.kind}
    (setup : Circuit model origin first) (allocation : Circuit model first second)
    (body : Circuit model second final) (packing : Circuit model final result)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State origin Reference (model.HiddenState × History)) (predicate : Store result →
      Prop) :
    storeSupported ((setup.seq ((allocation.seq body).seq packing)).execute environment Reference
      initial)
      predicate ↔
      storeSupported (packing.execute environment Reference
        (((setup.seq allocation).seq body).execute environment Reference initial)) predicate := by
  have reassoc := Circuit.seqAssoc_execute setup allocation body environment Reference initial
  refine (storeSupported_seq_assoc setup (allocation.seq body) packing initial predicate).trans
    ((storeSupported_seq (setup.seq (allocation.seq body)) packing initial predicate).trans ?_)
  rw [reassoc]
  let current : State final Reference
      (model.HiddenState × (History × (setup.seq (allocation.seq body)).Path)) :=
    (setup.seq (allocation.seq body)).execute environment Reference initial
  have mapped := (support_execute_mapHistory (environment := environment) packing current
    (fun history : History × (setup.seq (allocation.seq body)).Path =>
      (history.1, (Circuit.seqAssocPath setup allocation body).symm history.2)) predicate).symm
  refine mapped.trans ?_
  apply Iff.of_eq
  apply congrArg (fun inputState : State final Reference
    (model.HiddenState × (History × ((setup.seq allocation).seq body).Path)) =>
      storeSupported (packing.execute environment Reference inputState) predicate)
  dsimp only [State.mapHistory]
  exact ExecutionState.executionState_mapClassical_congr current (by funext record; rfl)


private lemma two_output_mass {Value : Type} [Finite Value]
    (distribution : PMF Value) (left right : Value) (distinct : left ≠ right)
    (zero : ∀ value, value ≠ left → value ≠ right → distribution value = 0) :
    distribution left + distribution right = 1 := by
  let := Fintype.ofFinite Value
  have restricted : (∑ value ∈ ({left, right} : Finset Value), distribution value) =
      ∑ value, distribution value := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro value _ excluded
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at excluded
    exact zero value excluded.1 excluded.2
  have total : (∑ value ∈ ({left, right} : Finset Value), distribution value) = 1 :=
    restricted.trans (by simpa only [tsum_fintype] using distribution.tsum_coe)
  simpa [distinct] using total

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- The unchanged source-derived failure coefficient includes the complete exceptional error. -/
def failureRatio : ℝ := 1 - ((problem.order : ℝ) * Nat.totient problem.order /
  (4 * (fourierModulus problem : ℝ) ^ 2) -
    4 * Real.sqrt (preparedExceptionalMass problem points seed))

private def setup : Circuit Model (Recovery.PublicInput.frame E (orderWidth problem))
    (Recovery.PublicInput.context E (orderWidth problem)) :=
  BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))

private def sample : CInputRef (Recovery.PublicInput.context E (orderWidth problem))
    (.fixedVector (orderWidth problem + orderWidth problem) (.finite 2)) :=
  recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)))

private def attempts (nontrivial : 2 ≤ problem.order) (count : Nat) :
    Circuit Model
      (persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
        (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
        (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  sampledAttempts (round E fieldTail problem points seed problem.order
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)) count
      (ECDLP.Canonical.Layout.curveSpec E)
    (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem))

/-- The real persistent failure state after allocation and all requested attempts, before packing.
-/
def failurePrefixState (nontrivial : 2 ≤ problem.order) (count : Nat) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :=
  (((setup E problem).seq (retainPersistent (model := Model) (Recovery.PublicInput.context E
    (orderWidth problem))
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))).seq
      (attempts E fieldTail odd problem points seed nontrivial count)).execute environment Reference
        (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original)

set_option maxHeartbeats 800000 in
-- Checking the complete allocated failure-prefix proof exceeded the default finite budget.
/-- Actual unnormalized failure fibers contract along the exact allocated run's real prefixes. -/
lemma actual_failurePrefix_weight_le
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (count : Nat) (input : SecretInput problem) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    persistentFailureWeight (model := Model) (ctx := Recovery.PublicInput.context E (orderWidth
      problem))
      (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      (failurePrefixState (environment := environment) E fieldTail odd problem points seed
        nontrivial count original) ≤
        (failureRatio E problem points seed) ^ count := by
  let width := ECDLP.Canonical.Layout.fieldWidth E
  let scalarWidth := orderWidth problem
  let ctx := Recovery.PublicInput.context E scalarWidth
  let initial := Recovery.PublicInput.Support.enteredState E scalarWidth problem original
  let allocation : Circuit Model ctx (persistentCtx ctx width scalarWidth) :=
    retainPersistent (model := Model) ctx width scalarWidth
  let lower := (problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)
  have initialized : persistentFailureWeight (model := Model) (ctx := ctx)
      (width := width) (scalarWidth := scalarWidth)
      (((setup E problem).seq allocation).execute environment Reference initial) = 1 :=
    (initialized_failure_weight (setup E problem) width scalarWidth initial).trans
      (Recovery.PublicInput.Support.enteredState_mass E scalarWidth problem original)
  have geometric := sampledAttempts_failure_weight_le_on_prefix (environment := environment)
    (round E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)) count
        (ECDLP.Canonical.Layout.curveSpec E)
    (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E scalarWidth) (Recovery.PublicInput.contextTargetRef E
      scalarWidth)
    problem.generator.toMathlib problem.target.toMathlib initial
    (fun priorCode => Recovery.PublicInput.Support.persistentProgram_supported_represents E
      scalarWidth
      problem priorCode original) lower (samplingCandidateFloor_le_one problem points seed)
    (fun History _ state => by
      have floor := CandidateProbability.actual_persistent_round_candidate_weight_bound
        (environment := environment)
        E fieldTail odd problem points seed sameWidth fits nontrivial addends input state
      refine floor.trans_eq ?_
      exact indicator_decision_weight _ _ _ _)
    ((setup E problem).seq allocation)
  rw [initialized, mul_one] at geometric
  exact geometric

section

-- Generic composition laws use these native operations without expanding their implementation.
attribute [local irreducible] sampleUnderPersistent retainPersistent

set_option maxHeartbeats 800000 in
-- Checking the complete four-stage output-probability proof exceeded the default finite budget.
/-- Actual option packing reads exactly the failure mass of that same complete run prefix. -/
lemma actual_run_none_probability_eq (nontrivial : 2 ≤ problem.order) (count : Nat)
    {Reference : Register} (original : Input (Recovery.PublicInput.frame E (orderWidth problem))
      Reference) :
    (run E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)
      nontrivial count).outputDistribution environment (Recovery.PublicInput.Support.oracleInput E
        (orderWidth problem) problem original)
          .optionNone =
      ENNReal.ofReal (persistentFailureWeight (model := Model)
        (ctx := Recovery.PublicInput.context E (orderWidth problem))
        (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
        (failurePrefixState (environment := environment) E fieldTail odd problem points seed
          nontrivial count original)) := by
  let width := ECDLP.Canonical.Layout.fieldWidth E
  let scalarWidth := orderWidth problem
  let ctx := Recovery.PublicInput.context E scalarWidth
  let initial := Recovery.PublicInput.Support.enteredState E scalarWidth problem original
  let actual := run E fieldTail problem points seed problem.order
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd) nontrivial count
  let supplied := Recovery.PublicInput.Support.oracleInput E scalarWidth problem original
  let storeEffects : Store (batchResultCtx ctx width scalarWidth) →
      Effect ((batchResultCtx ctx width scalarWidth).register.prod Reference) := fun stored =>
    if stored.read (batchResultRead ctx width scalarWidth) = .optionNone then
      Effect.one ((batchResultCtx ctx width scalarWidth).register.prod Reference)
    else Effect.zero ((batchResultCtx ctx width scalarWidth).register.prod Reference)
  let effects : actual.Record →
      Effect ((batchResultCtx ctx width scalarWidth).register.prod Reference) :=
    fun record => storeEffects record.1
  have executed : actual.execute environment Reference supplied.state =
      actual.code.execute environment Reference initial := by
    dsimp only [AlgorithmRun.execute, Recovery.PublicInput.Support.enteredState, initial, supplied]
    apply congrArg (actual.code.execute environment Reference)
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  have readout (record : actual.Record) :
      actual.result record = record.1.read (batchResultRead ctx width scalarWidth) := rfl
  have observed := AlgorithmRun.outputDistribution_apply_eq_effectWeight actual environment supplied
    .optionNone
  conv at observed =>
    rhs
    arg 1
    arg 2
    equals effects =>
      funext record
      by_cases absent : record.1.read (batchResultRead ctx width scalarWidth) = .optionNone
      · simp only [effects, storeEffects, readout, if_pos absent]
        dsimp only [ctx, width, scalarWidth]
      · simp only [effects, storeEffects, readout, if_neg absent]
        dsimp only [ctx, width, scalarWidth]
  have sameWeight := congrArg (fun state : ExecutionState actual.Record
    ((batchResultCtx ctx width scalarWidth).register.prod Reference) => state.effectWeight effects)
    executed
  have packed := Circuit.storedWeight_four_stage (setup E problem)
    (retainPersistent (model := Model) ctx width scalarWidth)
    (attempts E fieldTail odd problem points seed nontrivial count)
    (packBatchResult (model := Model) ctx width scalarWidth) environment initial storeEffects
  have unpacked := packBatchResult_none_weight (environment := environment) (model := Model)
    (ctx := ctx) width scalarWidth
    (failurePrefixState (environment := environment) E fieldTail odd problem points seed
      nontrivial count original)
  conv at unpacked =>
    lhs
    arg 2
    equals (fun entry => storeEffects entry.1) =>
      funext entry
      by_cases absent : entry.1.read (batchResultRead ctx width scalarWidth) = .optionNone
      · simp only [storeEffects, if_pos absent]
      · simp only [storeEffects, if_neg absent]
  have packedNone := packed.trans unpacked
  refine observed.trans (congrArg ENNReal.ofReal (sameWeight.trans ?_))
  dsimp only [actual, run, tailRun, sampledRecoveryRun, sampledRecoveryTail, effects]
  exact packedNone

/-- The exact allocated streaming run obeys the original finite geometric failure bound. -/
lemma actual_run_none_probability_le
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (count : Nat) (input : SecretInput problem) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    (run E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)
      nontrivial count).outputDistribution environment (Recovery.PublicInput.Support.oracleInput E
        (orderWidth problem) problem original)
          .optionNone ≤
      ENNReal.ofReal ((failureRatio E problem points seed) ^ count) := by
  rw [actual_run_none_probability_eq E fieldTail odd problem points seed nontrivial count original]
  exact ENNReal.ofReal_le_ofReal (actual_failurePrefix_weight_le E fieldTail odd problem points
    seed sameWidth fits nontrivial addends count input original)

set_option maxHeartbeats 800000 in
-- Checking the full Store, path and Reference support proof exceeded the default finite budget.
/-- Every actual returned word of this same run is the original unique secret. -/
lemma actual_run_supported_secret (nontrivial : 2 ≤ problem.order) (count : Nat)
    (input : SecretInput problem) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (record : (run E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd) nontrivial
        count).Record)
    (positive : 0 < (((run E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd) nontrivial
        count).execute environment Reference
        (Recovery.PublicInput.Support.oracleInput E (orderWidth problem) problem
          original).state).block
          record).mass)
    (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (output : (run E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd) nontrivial
        count).result record =
        .optionSome value) :
    value = CShape.wordOfNat (orderWidth problem) input.secret.val := by
  let width := ECDLP.Canonical.Layout.fieldWidth E
  let scalarWidth := orderWidth problem
  let ctx := Recovery.PublicInput.context E scalarWidth
  let initial := Recovery.PublicInput.Support.enteredState E scalarWidth problem original
  let allocation : Circuit Model ctx (persistentCtx ctx width scalarWidth) :=
    retainPersistent (model := Model) ctx width scalarWidth
  let body := attempts E fieldTail odd problem points seed nontrivial count
  let packing : Circuit Model (persistentCtx ctx width scalarWidth)
      (batchResultCtx ctx width scalarWidth) := packBatchResult (model := Model) ctx width
        scalarWidth
  let invariant := fun stored : Store (persistentCtx ctx width scalarWidth) =>
    (stored.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        problem.order ∧
      ((stored.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        (stored.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
          problem.generator.toMathlib = problem.target.toMathlib)
  have initialized : storeSupported (((setup E problem).seq allocation).execute environment
    Reference initial)
      invariant := initialized_selected_invariant (setup E problem) width scalarWidth problem.order
        (lt_of_lt_of_le (by decide : 0 < 2) nontrivial) _ initial
  have maintained : storeSupported ((((setup E problem).seq allocation).seq body).execute
    environment Reference initial) invariant :=
    sampledAttempts_supported_validity_on_prefix
      (round E fieldTail problem points seed problem.order
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)) count
          (ECDLP.Canonical.Layout.curveSpec E)
      (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
      (Recovery.PublicInput.contextBaseRef E scalarWidth) (Recovery.PublicInput.contextTargetRef
        E scalarWidth)
      problem.generator.toMathlib problem.target.toMathlib initial
      (fun priorCode => Recovery.PublicInput.Support.persistentProgram_supported_represents E
        scalarWidth
        problem priorCode original) ((setup E problem).seq allocation) initialized
  have packed : storeSupported (packing.execute environment Reference
      ((((setup E problem).seq allocation).seq body).execute environment Reference initial))
      (fun stored => ∀ returned, stored.read (batchResultRead ctx width scalarWidth) =
        .optionSome returned → returned = CShape.wordOfNat scalarWidth input.secret.val) := by
    intro entry present returned same
    exact packBatchResult_supported_secret (model := Model) (placement := ctx) problem input
      ((((setup E problem).seq allocation).seq body).execute environment Reference initial)
      (fun earlier present accepted =>
        ⟨(maintained earlier present).1, (maintained earlier present).2 accepted⟩)
      entry present returned same
  have completed := (four_stage_support (environment := environment)
    (setup E problem) allocation body packing initial _).mpr
    packed
  let actual := run E fieldTail problem points seed problem.order
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd) nontrivial count
  let supplied := Recovery.PublicInput.Support.oracleInput E scalarWidth problem original
  have executed : actual.execute environment Reference supplied.state =
      actual.code.execute environment Reference initial := by
    dsimp only [AlgorithmRun.execute, Recovery.PublicInput.Support.enteredState, initial, supplied]
    apply congrArg (actual.code.execute environment Reference)
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  have positive' : 0 < ((actual.code.execute environment Reference initial).block record).mass :=
    (congrArg (fun state : ExecutionState actual.Record
      ((batchResultCtx ctx width scalarWidth).register.prod Reference) =>
        0 < (state.block record).mass) executed).mp positive
  have readout : actual.result record = record.1.read (batchResultRead ctx width scalarWidth) := rfl
  have returned : record.1.read (batchResultRead ctx width scalarWidth) = .optionSome value :=
    readout.symm.trans output
  have supported : storeSupported (actual.code.execute environment Reference initial)
      (fun stored => ∀ returned, stored.read (batchResultRead ctx width scalarWidth) =
        .optionSome returned → returned = CShape.wordOfNat scalarWidth input.secret.val) := by
    dsimp only [actual, run, tailRun, sampledRecoveryRun, sampledRecoveryTail]
    exact completed
  exact supported record positive' value returned

end

/-- Every different returned scalar has zero probability in the actual output PMF. -/
lemma actual_run_wrong_probability_zero (nontrivial : 2 ≤ problem.order) (count : Nat)
    (input : SecretInput problem) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (different : value ≠ CShape.wordOfNat (orderWidth problem) input.secret.val) :
    (run E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)
      nontrivial count).outputDistribution environment (Recovery.PublicInput.Support.oracleInput E
        (orderWidth problem) problem original)
          (.optionSome value) = 0 := by
  by_contra positive
  let actual := run E fieldTail problem points seed problem.order
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd) nontrivial count
  let supplied := Recovery.PublicInput.Support.oracleInput E (orderWidth problem) problem original
  have supported : CShape.Value.optionSome value ∈ (actual.outputDistribution environment
    supplied).support :=
    (PMF.mem_support_iff _ _).mpr positive
  obtain ⟨record, present, output⟩ := (PMF.mem_support_map_iff actual.result
    (actual.executionDistribution environment supplied) (.optionSome value)).mp supported
  have mass := (ExecutionState.mem_support_toPMF_iff (actual.execute environment Reference
    supplied.state)
    (actual.execute_normalized environment supplied) record).mp present
  exact different (actual_run_supported_secret E fieldTail odd problem points seed nontrivial count
    input original record mass value output)

set_option maxHeartbeats 800000 in
-- Checking the full finite-run output probability proof exceeded the default finite budget.
/-- The same allocated run has the original complete geometric secret-success probability. -/
lemma actual_run_secret_probability_ge
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (count : Nat) (input : SecretInput problem) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    1 - ENNReal.ofReal ((failureRatio E problem points seed) ^ count) ≤
      (run E fieldTail problem points seed problem.order
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)
        nontrivial count).outputDistribution environment (Recovery.PublicInput.Support.oracleInput
          E (orderWidth problem) problem original)
            (.optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)) := by
  let actual := run E fieldTail problem points seed problem.order
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd) nontrivial count
  let supplied := Recovery.PublicInput.Support.oracleInput E (orderWidth problem) problem original
  let distribution := actual.outputDistribution environment supplied
  let wanted := CShape.wordOfNat (orderWidth problem) input.secret.val
  have total : distribution .optionNone + distribution (.optionSome wanted) = 1 := by
    apply two_output_mass distribution .optionNone (.optionSome wanted) (by intro same; cases same)
    intro value absent different
    cases value with
    | optionNone => exact False.elim (absent rfl)
    | optionSome value =>
        exact actual_run_wrong_probability_zero E fieldTail odd problem points seed nontrivial
          count input original value (fun same => different (congrArg CShape.Value.optionSome same))
  have complement : 1 - distribution .optionNone ≤ distribution (.optionSome wanted) := by
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using total.symm.le
  exact (tsub_le_tsub_left (actual_run_none_probability_le E fieldTail odd problem points seed
    sameWidth fits nontrivial addends count input original) 1).trans complement

private lemma oracleInput_eq_of_state_eq {ctx : RuntimeCtx .quantum} {Reference : Register}
    (first second : OracleInput .empty ctx Reference) (same : first.state = second.state) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

omit [Fact p.Prime] in
private lemma oracleInput_eq_of_domain {Reference : Register}
    (supplied : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      supplied.caller.localState) :
    Recovery.PublicInput.Support.oracleInput E (orderWidth problem) problem supplied.caller =
      supplied := by
  have sameCaller := Recovery.PublicInput.Support.prescribedInput_eq_of_domain E
    (orderWidth problem) problem supplied.caller valid
  apply oracleInput_eq_of_state_eq
  let attach := fun original : Input (Recovery.PublicInput.frame E (orderWidth problem))
      Reference => (OracleInput.withEmptyService original).state
  have attached := congrArg attach sameCaller
  have encoded :
      (Recovery.PublicInput.Support.oracleInput E (orderWidth problem) problem
        supplied.caller).state =
      attach (Recovery.PublicInput.Support.prescribedInput E (orderWidth problem) problem
        supplied.caller) := by
    dsimp only [Recovery.PublicInput.Support.oracleInput, attach, OracleInput.withEmptyService]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  exact encoded.trans
    (attached.trans (OracleInput.oracleInput_empty_caller_withEmptyService_state supplied))

/-- Every full reference extension in the original local public-point domain has the same bound.
-/
lemma actual_run_secret_probability_ge_on_domain
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (count : Nat) (input : SecretInput problem) {Reference : Register}
    (supplied : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      supplied.caller.localState) :
    1 - ENNReal.ofReal ((failureRatio E problem points seed) ^ count) ≤
      (run E fieldTail problem points seed problem.order
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)
        nontrivial count).outputDistribution environment supplied
          (.optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)) := by
  rw [← oracleInput_eq_of_domain E problem supplied valid]
  exact actual_run_secret_probability_ge E fieldTail odd problem points seed sameWidth fits
    nontrivial addends count input supplied.caller

/-- The original first accepted word survives every further actual streaming round and pack. -/
lemma actual_first_accepted_survives (nontrivial : 2 ≤ problem.order) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference (Unit × History))
    (wanted : (CShape.unsignedWord (orderWidth problem)).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted (Recovery.PublicInput.context E (orderWidth
        problem))
        (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).toCStorageRef)).toBool = true ∧
        entry.1.read (.storage (persistentSelected (Recovery.PublicInput.context E (orderWidth
          problem))
          (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).toCStorageRef) = wanted)
    (result : Store (batchResultCtx (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
        (Unit × (History × ((attempts E fieldTail odd problem points seed nontrivial count).seq
          (packBatchResult (model := Model) (Recovery.PublicInput.context E (orderWidth problem))
            (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))).Path)))
    (positive : 0 < ((((attempts E fieldTail odd problem points seed nontrivial count).seq
      (packBatchResult (model := Model) (Recovery.PublicInput.context E (orderWidth problem))
        (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))).execute environment Reference
          state).block
          result).mass) :
    result.1.read (batchResultRead (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) = .optionSome wanted :=
  sampledAttempts_pack_first_supported
    (round E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))
    count (ECDLP.Canonical.Layout.curveSpec E)
    (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) state wanted holds result
      positive

end

end ExecutionContract.FiniteSuccess
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
