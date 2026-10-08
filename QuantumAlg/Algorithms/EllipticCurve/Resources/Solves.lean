/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Selection
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.FullRun
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Space
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Borrowed
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete actual logical resources for original elliptic-curve discrete logarithms

One actual circuit supplies the returned scalar, every probability, all
native events, live spaces and depth. The original exceptional error remains
in its finite repetition condition. The hidden scalar is selected only inside
the proof; neither it nor an external reference is an executable parameter.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass ScalarMultiplication.MeasuredPlacement
  FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open FiniteCyclicDLP.Canonical.Probability

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem output_probability_le_relational {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model pre post shape)
    {Reference : Register}
    (supplied : OracleInput model.classicalOracles pre Reference) (value : shape.Value)
    (accepts : Store pre → shape.Value → Prop) (accepted : ∀ store, accepts store value) :
    run.outputDistribution supplied value ≤
      (run.relationalDistribution supplied).toOuterMeasure {pair | accepts pair.1 pair.2} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  apply (run.executionDistribution supplied).toOuterMeasure_mono
  intro record member
  have same : run.result record = value := member.1
  change accepts record.2.2.1 (run.result record)
  rw [same]
  exact accepted record.2.2.1

private theorem oracleInput_eq_of_state_eq {oracles : ClassicalOracleModel}
    {kind : ProblemKind} {pre : RuntimeCtx kind} {Reference : Register}
    (left right : OracleInput oracles pre Reference) (same : left.state = right.state) :
    left = right := by
  cases left with
  | mk leftState leftNormalized =>
    cases right with
    | mk rightState rightNormalized =>
      cases same
      rfl

private theorem emptyOracleInput_ofCaller {pre : RuntimeCtx .quantum} {Reference : Register}
    (input : OracleInput .empty pre Reference) :
    OracleInput.ofKernel input.caller (fun _ => PMF.pure ()) = input := by
  classical
  have stateEq : (OracleInput.ofKernel input.caller (fun _ => PMF.pure ())).state =
      input.state := by
    change kernelChoice input.caller.state (fun _ => PMF.pure ()) = input.state
    rw [kernelChoice_pure]
    rw [show input.caller.state = input.state.mapClassical Prod.fst from rfl]
    rw [ExecutionState.executionState_mapClassical_comp_instances
      (result := Classical.decEq (Store pre × ClassicalOracleModel.empty.HiddenState))]
    have identity : ((fun value : Store pre =>
        (value, (() : ClassicalOracleModel.empty.HiddenState))) ∘
          (Prod.fst : Store pre × ClassicalOracleModel.empty.HiddenState → Store pre)) = id := by
      funext value
      rcases value with ⟨store, hidden⟩
      cases hidden
      rfl
    rw [identity]
    exact (ExecutionState.executionState_mapClassical_congr_decision input.state id id
      (fun _ => rfl) (Classical.decEq _) inferInstance).trans
        (ExecutionState.mapClassical_id input.state)
  exact oracleInput_eq_of_state_eq _ _ stateEq

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The algorithm contains exactly the original actual repeated measured execution. -/
public def algorithm (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (count : Nat) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
      (inputContext E I) (outputContext E I)
      (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))) where
  run := exponentRepeatedRun E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I)
    points seed I.subgroupOrder_prime.two_le count

/-- The registered generic algorithm has the real first reset-bounded checked
section for every symbolic count of at least two attempts. That section also
retains an already accepted scalar through its checked recovery. This is a
first-boundary fact, not a complete-cycle schedule. -/
theorem algorithm_firstBoundary_certificate
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points)
    (count : Nat) :
    let problem := ECDLP.Canonical.problem I
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body := (persistentSamplingReadout E fieldTail odd problem points).seq
      (persistentCheckedRecovery E problem I.subgroupOrder_prime.two_le)
    let first := (reset.seq body).seq reset
    let setup := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
    let allocation := retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
    let terminal := packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
    RetainsFirst E problem first ∧
      Nonempty (Circuit.OperationalEquiv
        (algorithm E fieldTail sameWidth fits odd I points seed ((count + 1) + 1)).run.code
        (setup.seq ((allocation.seq
          (first.seq (Circuit.OperationalEquiv.rotatedTail reset body count))).seq
            terminal))) ∧
      (∀ {Reference : Register}
        (input : OracleInput .empty
          (persistentCtx (PublicInput.terminal E (orderWidth problem))
            (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference),
        ∀ requirement ∈
          (checkedSectionProblem E fieldTail sameWidth fits problem points seed
            I.subgroupOrder_prime.two_le addends).states,
          requirement.Holds input.caller
            ((firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
              I.subgroupOrder_prime.two_le (checkedSectionRead E problem)).finalState
                Reference input.state)) ∧
      (∀ path : (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          I.subgroupOrder_prime.two_le).Path,
        (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          I.subgroupOrder_prime.two_le).resourcePool path ≤
          checkedSectionEventBudget E problem I.subgroupOrder_prime.two_le) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact firstCheckedSection_retainsFirst E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le .unit
  · exact ⟨exponentRepeatedRun_firstCycle E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count⟩
  · intro Reference input requirement member
    exact firstCheckedSection_problemStates E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends input
      requirement member
  · exact firstCheckedSection_pool_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le

/-- The registered generic execution's reused checked section also fits the
independently fixed complete-section native event allowance. -/
theorem algorithm_reusedBoundary_pool_le
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (path : (reusedCheckedSectionCode E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le).Path) :
    (reusedCheckedSectionCode E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le).resourcePool path ≤
      checkedSectionEventBudget E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le :=
  reusedCheckedSection_pool_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le path

/-- The registered generic owner applies the independent checked-section
depth protocol to both real nonterminal boundary shapes. -/
theorem algorithm_checkedSection_depth_certificate
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points) :
    let problem := ECDLP.Canonical.problem I
    (∀ path : (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).Path,
      (checkedSectionProblem E fieldTail sameWidth fits problem points seed
        I.subgroupOrder_prime.two_le addends).depth.Holds
          (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
            I.subgroupOrder_prime.two_le) path) ∧
    (∀ path : (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).Path,
      (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        I.subgroupOrder_prime.two_le addends).depth.Holds
          (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
            I.subgroupOrder_prime.two_le) path) := by
  dsimp only
  constructor
  · exact firstCheckedSection_problemDepth E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends
  · exact reusedCheckedSection_problemDepth E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends

/-- Both real nonterminal checked sections respect the independent resident
and auxiliary allowances on every complete interpreter path. -/
theorem algorithm_checkedSection_space_certificate
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points) :
    let problem := ECDLP.Canonical.problem I
    let firstProtocol := checkedSectionProblem E fieldTail sameWidth fits problem points seed
      I.subgroupOrder_prime.two_le addends
    let reusedProtocol := reusedCheckedSectionProblem E fieldTail sameWidth fits problem
      points seed I.subgroupOrder_prime.two_le addends
    (∀ path : (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).Path,
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).peakResidentSpace path ≤ firstProtocol.resources.resident ∧
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).peakAuxiliarySpace path ≤ firstProtocol.resources.auxiliary) ∧
    (∀ path : (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).Path,
      (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).peakResidentSpace path ≤ reusedProtocol.resources.resident ∧
      (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).peakAuxiliarySpace path ≤
          reusedProtocol.resources.auxiliary) := by
  dsimp only
  constructor
  · intro path
    exact ⟨firstCheckedSection_resident_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le path,
      firstCheckedSection_auxiliary_le E fieldTail sameWidth fits odd
        (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le path⟩
  · intro path
    exact ⟨reusedCheckedSection_resident_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le path,
      reusedCheckedSection_auxiliary_le E fieldTail sameWidth fits odd
        (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le path⟩

/-- Both real nonterminal checked sections restore the full borrowed and
external-reference observation for every local caller input. -/
theorem algorithm_checkedSection_borrowed_certificate
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) :
    let problem := ECDLP.Canonical.problem I
    (∀ {Reference : Register}
      (input : OracleInput .empty
        (persistentCtx (PublicInput.terminal E (orderWidth problem))
          (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference),
      (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le (checkedSectionRead E problem)).RestoresBorrowed input) ∧
    (∀ {Reference : Register}
      (input : OracleInput .empty
        (persistentCtx (PublicInput.terminal E (orderWidth problem))
          (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference),
      (reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le (checkedSectionRead E problem)).RestoresBorrowed input) := by
  dsimp only
  constructor
  · exact firstCheckedSection_problemBorrowed E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le
  · exact reusedCheckedSection_problemBorrowed E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le

/-- The registered generic algorithm's actual first checked attempt obeys
the original candidate-floor failure contraction from every admitted public
input and reference. Its public points are established by the real prefix,
not supplied as an extra condition on the caller. -/
theorem algorithm_firstAttempt_failureWeight_le
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points)
    {Reference : Register}
    (original : Input (Allocation.before p.size
      (2 * orderWidth (ECDLP.Canonical.problem I))) Reference) :
    let problem := ECDLP.Canonical.problem I
    let terminal := PublicInput.terminal E (orderWidth problem)
    let width := ECDLP.Canonical.Layout.fieldWidth E
    let scalarWidth := orderWidth problem
    let setup := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
    let allocation := retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      terminal width scalarWidth
    let prior := setup.seq allocation
    let initial := PublicInput.persistentInitialState E scalarWidth problem original
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := terminal) (width := width) (scalarWidth := scalarWidth)
      ((persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
        I.subgroupOrder_prime.two_le).execute Reference
          (prior.execute Reference initial)) ≤
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
      persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (ctx := terminal) (width := width) (scalarWidth := scalarWidth)
        (prior.execute Reference initial) := by
  let problem := ECDLP.Canonical.problem I
  let setup := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
  let allocation := retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.terminal E (orderWidth problem))
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
  let witness : SecretInput problem :=
    ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I⟩
  exact persistentCheckedAttempt_failureWeight_on_originalPrefix E fieldTail sameWidth fits odd
    problem points seed I.subgroupOrder_prime.two_le addends witness
    (setup.seq allocation) original

private theorem main_output_probability (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure)
    (Reference : Register)
    (supplied : OracleInput .empty (inputContext E I) Reference)
    (valid : (problem E I count failure).valid supplied.caller.localState) :
    1 - ENNReal.ofReal failure ≤
      (exponentRepeatedRun E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I) points
        seed I.subgroupOrder_prime.two_le count).outputDistribution supplied
          (.optionSome (CShape.wordOfNat (orderWidth (ECDLP.Canonical.problem I))
            (ECDLP.Canonical.secret I).val)) := by
  let original := PublicInput.unframedInput E (orderWidth (ECDLP.Canonical.problem I))
    supplied.caller
  let witness : SecretInput (ECDLP.Canonical.problem I) :=
    ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I⟩
  have same := PublicInput.initialInput_unframedInput E
    (orderWidth (ECDLP.Canonical.problem I)) (ECDLP.Canonical.problem I)
    supplied.caller valid
  have actual : repeatedOracleInput E (ECDLP.Canonical.problem I) original = supplied := by
    unfold repeatedOracleInput
    rw [same]
    exact emptyOracleInput_ofCaller supplied
  have correct := exponentRepeatedRun_secret_probability_ge E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) I.subgroupOrder_prime.two_le points seed addends count witness
    original
  rw [actual] at correct
  exact (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal calibrated) 1).trans correct

private theorem main_success (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure)
    (Reference : Register)
    (supplied : OracleInput .empty (inputContext E I) Reference)
    (valid : (problem E I count failure).valid supplied.caller.localState) :
    (problem E I count failure).successLB.value ≤
      ((algorithm E fieldTail sameWidth fits odd I points seed count).relationalDistribution
        supplied).toOuterMeasure
          {pair | (problem E I count failure).accepts pair.1 pair.2} := by
  have output := main_output_probability E fieldTail sameWidth fits odd I points seed addends
    count failure calibrated Reference supplied valid
  have bridge := output_probability_le_relational
    (exponentRepeatedRun E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I) points seed
      I.subgroupOrder_prime.two_le count) supplied
    (.optionSome (CShape.wordOfNat (orderWidth (ECDLP.Canonical.problem I))
      (ECDLP.Canonical.secret I).val))
    (fun _store output => AcceptedOutput E I output)
    (fun _store => ⟨ECDLP.Canonical.secret I, ECDLP.Canonical.secret_spec I, rfl⟩)
  exact output.trans bridge

private theorem run_restores_of_noBorrowedQuantum {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model pre post shape) (noBorrowed : pre.borrowedQuantumWires = [])
    {Reference : Register}
    (supplied : OracleInput model.classicalOracles pre Reference) :
    run.RestoresBorrowed supplied := by
  let recorded := supplied.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have restored := run.code.borrowedRestored_of_noBorrowedQuantum noBorrowed Reference
    recorded
  change Execution.observeBorrowedAfter run.code Reference
      (run.code.execute Reference recorded) = Execution.observeBorrowed Reference supplied.state
  have observed := Execution.observeBorrowed_mapClassical supplied.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
  have recordedObservation : Execution.observeBorrowed Reference recorded =
      Execution.observeBorrowed Reference supplied.state := by
    convert observed using 1
    apply congrArg (fun state : State pre Reference (model.HiddenState × Store pre) =>
      Execution.observeBorrowed Reference state)
    exact ExecutionState.executionState_mapClassical_congr supplied.state rfl
  exact restored.trans recordedObservation

private theorem main_borrowed (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (count : Nat) {Reference : Register}
    (supplied : OracleInput .empty (inputContext E I) Reference) :
    (algorithm E fieldTail sameWidth fits odd I points seed count).run.RestoresBorrowed
      supplied := by
  exact run_restores_of_noBorrowedQuantum
    (algorithm E fieldTail sameWidth fits odd I points seed count).run
    (PublicInput.before_noBorrowedQuantum E (orderWidth (ECDLP.Canonical.problem I)))
    supplied

/-- The same actual run solves the original problem under its complete error/retry condition. -/
public theorem algorithm_solves (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed count failure) :
    (algorithm E fieldTail sameWidth fits odd I points seed count).Solves
      (problem E I count failure) where
  success := fun Reference supplied valid _initialized =>
    main_success E fieldTail sameWidth fits odd I points seed addends count failure
      calibrated Reference supplied valid
  states := by
    intro Reference supplied valid initialized requirement member
    cases member
  borrowed := by
    intro Reference supplied valid initialized
    exact main_borrowed E fieldTail sameWidth fits odd I points seed count supplied
  events := by
    intro Reference supplied valid initialized path supported
    exact exponentRepeatedRun_pool_le E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I)
      points seed I.subgroupOrder_prime.two_le count path
  resident := by
    intro Reference supplied valid initialized path supported
    exact exponentRepeatedRun_resident_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path
  auxiliary := by
    intro Reference supplied valid initialized path supported
    exact exponentRepeatedRun_auxiliary_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count path
  depth := by
    intro Reference supplied valid initialized path supported
    exact exponentRepeatedRun_depth_le E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count
      (fun _ => 1) path

end

end QuantumAlg.EllipticCurve.LogicalResources
