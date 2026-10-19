/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Failure
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Support
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect.Failure

/-!
# Success of the actual initialized first boundary

The real one-time prefix initializes the failure weight to one. The first
sampled attempt contracts that weight by the original exceptional-error
factor; the following physical reset preserves the accepted bit exactly.
Supported selected words retain the original scalar bound and group equation.
All probabilities therefore belong to the actual pair read, with its complete
original input history and arbitrary external Reference. No positive-floor,
caller-seed or additional secret-witness hypothesis is required.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP Canonical.Probability
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open GenericPointAddition.InPlace

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

attribute [local irreducible] Nat.size Nat.clog
-- Keep unchanged runtime carriers and prescribed input states abstract during transport.
attribute [local irreducible] Recovery.PublicInput.context Recovery.PublicInput.frame
  persistentAccepted persistentSelected Recovery.PublicInput.Support.oracleInput

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

private lemma execute_from_equal_input {model : ExecutionModel}
    {environment : model.Environment}
    {origin final : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model origin final shape) {Reference : Register}
    (input prescribed : OracleInput model.classicalOracles origin Reference)
    (same : prescribed = input)
    (decision : DecidableEq (Store origin × (model.HiddenState × Store origin))) :
    run.execute environment Reference input.state = run.code.execute environment Reference
      (@ExecutionState.mapClassical (Store origin × model.HiddenState)
        (Store origin × (model.HiddenState × Store origin)) _ _ _ decision prescribed.state
          (fun value => (value.1, (value.2, value.1)))) := by
  subst prescribed
  change run.code.execute environment Reference _ = _
  apply congrArg (run.code.execute environment Reference)
  exact ExecutionState.executionState_mapClassical_congr input.state rfl

private lemma supported_completed {model : ExecutionModel}
    {environment : model.Environment}
    {origin ctx : RuntimeCtx model.kind}
    (before : Circuit model origin ctx) (checked following actual : Circuit model ctx ctx)
    (equivalent : Circuit.OperationalEquiv (checked.seq following) actual)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State origin Reference (model.HiddenState × History))
    (predicate : Store ctx → Prop)
    (supported : storeSupported
      (following.execute environment Reference (checked.execute environment Reference
        (before.execute environment Reference initial)))
      predicate) :
    storeSupported ((before.seq actual).execute environment Reference initial) predicate := by
  have complete : storeSupported ((before.seq (checked.seq following)).execute environment
    Reference initial)
      predicate :=
    (storeSupported_seq before (checked.seq following) initial predicate).mpr
      ((storeSupported_seq checked following (before.execute environment Reference initial)
        predicate).mpr
        supported)
  rw [(Circuit.OperationalEquiv.prepend before equivalent).symm.execute,
    storeSupported_mapHistory]
  exact complete

private lemma failure_le_of_unit {complete sampled initial mass ratio : ℝ}
    (same : complete = sampled) (bound : sampled ≤ ratio * initial)
    (initialized : initial = mass) (normalized : mass = 1) : complete ≤ ratio := by
  calc
    complete = sampled := same
    _ ≤ ratio * initial := bound
    _ = ratio := by rw [initialized, normalized, mul_one]

private lemma support_of_state_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    {first second : State ctx Reference History} (same : first = second)
    (predicate : Store ctx → Prop) (supported : storeSupported second predicate) :
    storeSupported first predicate := same.symm ▸ supported

private lemma weight_le_of_state_eq {Record : Type} [Fintype Record] {R : Register}
    {first second : ExecutionState Record R} (same : first = second)
    (effect : Record → Effect R) {ratio : ℝ} (bounded : second.effectWeight effect ≤ ratio) :
    first.effectWeight effect ≤ ratio :=
  (congrArg (fun state : ExecutionState Record R => state.effectWeight effect) same).trans_le
    bounded

private lemma success_from_supported {model : ExecutionModel}
    {environment : model.Environment}
    {origin ctx : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model origin ctx shape) {Reference : Register}
    (input : OracleInput model.classicalOracles origin Reference)
    (accepts : CShape.Value shape → Prop) (flag : Store ctx → Bool)
    (predicate : Store ctx → Prop) (ratio : ℝ)
    (supported : storeSupported (run.execute environment Reference input.state) predicate)
    (accepts_iff : ∀ record : run.Record,
      predicate record.1 → (accepts (run.result record) ↔ flag record.1 = true))
    (bounded : (run.execute environment Reference input.state).effectWeight
      (fun record => if flag record.1 = false then Effect.one (ctx.register.prod Reference)
        else Effect.zero (ctx.register.prod Reference)) ≤ ratio) :
    1 - ENNReal.ofReal ratio ≤ (run.relationalDistribution environment input).toOuterMeasure
      {pair | accepts pair.2} := by
  have agrees : ∀ record ∈ (run.executionDistribution environment input).support,
      accepts (run.result record) ↔ flag record.1 = true := by
    intro record member
    have positive := (ExecutionState.mem_support_toPMF_iff _ _ _).mp member
    exact accepts_iff record (supported record positive)
  have observed := AlgorithmRun.relational_success_eq_one_sub_failure_effectWeight
    run environment input
    (fun pair => accepts pair.2) (fun record => flag record.1) agrees
  exact (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal bounded) 1).trans_eq observed.symm

private lemma sample_failure_weight {ctx : RuntimeCtx .quantum}
    (code : Circuit Model ctx ctx false) (width scalarWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Unit × History)) :
    persistentFailureWeight (model := Model) (ctx := ctx)
      (width := width) (scalarWidth := scalarWidth)
      ((sampleUnderPersistent code width scalarWidth).execute environment Reference state) =
        persistentFailureWeight (model := Model) (ctx := ctx)
          (width := width) (scalarWidth := scalarWidth) state := by
  unfold persistentFailureWeight
  rw [sampleUnderPersistent_acceptance_effectWeight code width scalarWidth state false]
  simp only [ExecutionState.effectWeight, Effect.weight_one]
  change ((sampleUnderPersistent code width scalarWidth).execute environment Reference
    (state.selectClassical (fun entry => (entry.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool)
        false)).mass = _
  rw [Circuit.execute_mass]
  exact selected_mass state _ false

private lemma failureWeight_equiv {origin ctx : RuntimeCtx .quantum}
    {width scalarWidth : Nat}
    {source target : Circuit Model origin (persistentCtx ctx width scalarWidth)}
    (equivalent : Circuit.OperationalEquiv source target)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State origin Reference (Unit × History)) :
    persistentFailureWeight (model := Model) (ctx := ctx)
      (width := width) (scalarWidth := scalarWidth) (source.execute environment Reference state) =
        persistentFailureWeight (model := Model) (ctx := ctx)
          (width := width) (scalarWidth := scalarWidth) (target.execute environment Reference
            state) := by
  unfold persistentFailureWeight
  rw [equivalent.execute, State.effectWeight_mapHistory]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

private def selectionSound (store : Store (sectionCtx E problem)) : Prop :=
  (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat < problem.order ∧
    ((store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
      (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
        problem.generator.toMathlib = problem.target.toMathlib)

private lemma initialized_attempt_supported (r : Nat) (coefficient : (ZMod p)ˣ)
    (nontrivial : 2 ≤ problem.order) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    storeSupported
      (((«prefix» E problem).seq
        (attempt E fieldTail problem points seed r coefficient nontrivial)).execute environment
          Reference
          (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original))
      (selectionSound E problem) := by
  let initial := Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original
  let before := «prefix» E problem
  let checked := attempt E fieldTail problem points seed r coefficient nontrivial
  have initialized : storeSupported (before.execute environment Reference initial) (selectionSound
    E problem) :=
    FiniteSuccess.initialized_selected_invariant
      (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) problem.order problem.order_pos
      _ initial
  have maintained : storeSupported ((before.seq checked).execute environment Reference initial)
      (selectionSound E problem) :=
    sampled_step_supported (round E fieldTail problem points seed r coefficient)
      (ECDLP.Canonical.Layout.curveSpec E)
      (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem))
      problem.generator.toMathlib problem.target.toMathlib initial
      (fun code => Recovery.PublicInput.Support.persistentProgram_supported_represents E
        (orderWidth problem) problem code original) before initialized
  exact maintained

/-- The actual checked pair remains bounded and sound after its following physical reset. -/
lemma initialized_supported (r : Nat) (coefficient : (ZMod p)ˣ)
    (nontrivial : 2 ≤ problem.order) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    storeSupported
      ((initializedAlgorithm E fieldTail problem points seed r coefficient
        nontrivial).run.code.execute environment Reference
          (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original))
      (selectionSound E problem) := by
  let initial := Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original
  let before := «prefix» E problem
  let checked := attempt E fieldTail problem points seed r coefficient nontrivial
  let following := reset E fieldTail problem seed
  have maintained := initialized_attempt_supported (environment := environment) E fieldTail
    problem points seed r coefficient
    nontrivial original
  have afterAttempt : storeSupported (checked.execute environment Reference (before.execute
    environment Reference initial))
      (selectionSound E problem) := (storeSupported_seq before checked initial _).mp maintained
  have afterReset : storeSupported
      (following.execute environment Reference (checked.execute environment Reference
        (before.execute environment Reference initial)))
      (selectionSound E problem) :=
    candidateCheck_sampleUnderPersistent_latches_property (resetChild E fieldTail problem seed)
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
      (checked.execute environment Reference (before.execute environment Reference initial))
      (fun pair => pair.2.toNat < problem.order ∧
        (pair.1 = true → pair.2.toNat • problem.generator.toMathlib = problem.target.toMathlib))
      afterAttempt
  exact supported_completed before checked following
    (first E fieldTail problem points seed r coefficient nontrivial)
    (first_equiv E fieldTail problem points seed r coefficient nontrivial)
    initial (selectionSound E problem) afterReset

/-- The completed first boundary has the same failure weight as its original sampled attempt. -/
lemma initialized_failure_weight (r : Nat) (coefficient : (ZMod p)ˣ)
    (nontrivial : 2 ≤ problem.order) {Reference : Register} {History : Type} [Fintype History]
    (initial : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference (Unit ×
      History)) :
    persistentFailureWeight (model := Model) (ctx := Recovery.PublicInput.context E (orderWidth
      problem))
      (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((initializedAlgorithm E fieldTail problem points seed r coefficient
        nontrivial).run.code.execute environment Reference initial) =
      persistentFailureWeight (model := Model) (ctx := Recovery.PublicInput.context E
        (orderWidth problem))
        (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
        ((attempt E fieldTail problem points seed r coefficient nontrivial).execute environment
          Reference
          ((«prefix» E problem).execute environment Reference initial)) := by
  change persistentFailureWeight (model := Model)
    (ctx := Recovery.PublicInput.context E (orderWidth problem))
    (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    (((«prefix» E problem).seq
      (first E fieldTail problem points seed r coefficient nontrivial)).execute environment
        Reference
        initial) = _
  rw [persistentFailureWeight_seq]
  rw [failureWeight_equiv
    (first_equiv E fieldTail problem points seed r coefficient nontrivial).symm]
  rw [persistentFailureWeight_seq]
  exact sample_failure_weight (resetChild E fieldTail problem seed)
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) _

/-- The complete physical first boundary meets the original one-attempt failure ceiling. -/
lemma initialized_failure_le (odd : Odd p)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    persistentFailureWeight (model := Model) (ctx := Recovery.PublicInput.context E (orderWidth
      problem))
      (width := ECDLP.Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((initializedAlgorithm E fieldTail problem points seed problem.order
        (Semantics.radixUnit p fieldTail.succ odd) nontrivial).run.code.execute environment
          Reference
          (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original)) ≤
      FiniteSuccess.failureRatio E problem points seed := by
  exact failure_le_of_unit
    (initialized_failure_weight E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial _)
    (firstAttempt_failureWeight_le E fieldTail odd problem points seed sameWidth fits
      nontrivial addends (SecretInput.ofKnownOrderProblem problem) original)
    (FiniteSuccess.initialized_failure_weight
      (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
      (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem original))
    (Recovery.PublicInput.Support.enteredState_mass E (orderWidth problem) problem original)

attribute [local irreducible] storeSupported

private lemma initialized_execution_eq (r : Nat) (coefficient : (ZMod p)ˣ)
    (nontrivial : 2 ≤ problem.order) {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      input.caller.localState) :
    (initializedAlgorithm E fieldTail problem points seed r coefficient nontrivial).run.execute
      environment Reference input.state =
      (initializedAlgorithm E fieldTail problem points seed r coefficient
        nontrivial).run.code.execute environment Reference
          (Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem input.caller) :=
  execute_from_equal_input
    (initializedAlgorithm E fieldTail problem points seed r coefficient nontrivial).run input
    (Recovery.PublicInput.Support.oracleInput E (orderWidth problem) problem input.caller)
    (FiniteSuccess.oracleInput_eq_of_domain E problem input valid) _

private lemma initialized_execution_supported (r : Nat) (coefficient : (ZMod p)ˣ)
    (nontrivial : 2 ≤ problem.order) {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      input.caller.localState) :
    storeSupported ((initializedAlgorithm E fieldTail problem points seed r coefficient
      nontrivial).run.execute environment Reference input.state) (selectionSound E problem) :=
  support_of_state_eq
    (initialized_execution_eq E fieldTail problem points seed r coefficient nontrivial input valid)
    (selectionSound E problem)
    (initialized_supported E fieldTail problem points seed r coefficient nontrivial input.caller)

private lemma initialized_execution_failure_le (odd : Odd p)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      input.caller.localState) :
    ((initializedAlgorithm E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial).run.execute environment Reference
        input.state).effectWeight (fun record =>
          if (record.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = false
          then Effect.one ((sectionCtx E problem).register.prod Reference)
          else Effect.zero ((sectionCtx E problem).register.prod Reference)) ≤
            FiniteSuccess.failureRatio E problem points seed :=
  weight_le_of_state_eq
    (initialized_execution_eq E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial input valid) _
    (initialized_failure_le E fieldTail problem points seed odd sameWidth fits nontrivial
      addends input.caller)

omit [Fact p.Prime] in
private lemma success_floor_eq :
    (successLB E problem points seed).value =
      1 - ENNReal.ofReal (FiniteSuccess.failureRatio E problem points seed) := rfl

private lemma initialized_read_accepts (store : Store (sectionCtx E problem))
    (sound : selectionSound E problem store) :
    initializedAccepts E problem ((read E problem).eval store) ↔
      (store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true := by
  change (_ = true ∧ _ < problem.order ∧ _ = problem.target.toMathlib) ↔ _ = true
  exact ⟨fun accepted => accepted.1, fun accepted => ⟨accepted, sound.1, sound.2 accepted⟩⟩

/-- The actual pair-read relational distribution satisfies the independent corrected floor. -/
lemma initialized_success (odd : Odd p)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      input.caller.localState) :
    (successLB E problem points seed).value ≤
      ((initializedAlgorithm E fieldTail problem points seed problem.order
        (Semantics.radixUnit p fieldTail.succ odd)
          nontrivial).run.relationalDistribution environment input).toOuterMeasure
            {pair | initializedAccepts E problem pair.2} := by
  let actual := (initializedAlgorithm E fieldTail problem points seed problem.order
    (Semantics.radixUnit p fieldTail.succ odd) nontrivial).run
  apply (success_floor_eq E problem points seed).trans_le
  apply success_from_supported actual input (initializedAccepts E problem)
    (fun store => (store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool)
    (selectionSound E problem) (FiniteSuccess.failureRatio E problem points seed)
    (initialized_execution_supported E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial input valid) ?_
    (initialized_execution_failure_le E fieldTail problem points seed odd sameWidth fits
      nontrivial addends input valid)
  intro record sound
  exact initialized_read_accepts E problem record.1 sound

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
