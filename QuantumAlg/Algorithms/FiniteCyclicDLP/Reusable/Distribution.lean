/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Reference
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Initial
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Reference
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Initial
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Util.PMF.VectorMass

/-!
# Independent samples from literal sequential reuse of one binary DLP bank

The product law follows from complete reference observations at each actual
round. Each selected slot is written once and all previous samples survive
the following measurements and physical resets. This includes the empty
sample vector while retaining the actual initial quantum preparation
[Sho95, source.tex:1784-1984] [dW19, qcnotes.tex:5409-5420].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Distinct selected slots have their complete product law jointly with stable earlier data. -/
private lemma selected_rounds_reference (P : KnownOrderProblem G) (count attempts : Nat)
    (selection : Fin attempts → Fin count) (distinct : Function.Injective selection)
    (expansion : OrderExpansion P.order)
    (weight : (CShape.fixedVector count
      (.fixedVector (sampleWidth P) (.finite 2))).Value → ℂ)
    (stable : ∀ index store basis,
      weight ((measuredStore P (selection index) store basis).read (samplesInput P count)) =
        weight (store.read (samplesInput P count)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (seeded : BasisSeeded.Holds (context P count).quantumLayout.zeroLabel state)
    (outcomes : Fin count → TerminalZMeasure.Outcome (sampleWidth P))
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((QuantumAlg.Circuit.forRange attempts
        (fun index => round P (selection index) expansion)).execute
          (sourceEnvironment P) Reference state)
      (fun entry _ => weight (entry.1.read (samplesInput P count)) *
        ∏ index : Fin attempts,
          if observedOutcome P (entry.1.read (sampleInput P (selection index))) =
            outcomes (selection index) then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read (samplesInput P count)) *
          ∏ index : Fin attempts,
            ((Binary.outcomePMF P expansion (outcomes (selection index))).toReal : ℂ))
        leftRef rightRef := by
  induction attempts generalizing History weight with
  | zero =>
      simp only [QuantumAlg.Circuit.forRange, QuantumAlg.Circuit.execute_id,
        Fin.prod_univ_zero, mul_one]
      exact ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight (entry.1.read (samplesInput P count))) leftRef rightRef
  | succ attempts ih =>
      let first := round P (selection 0) expansion
      let advanced := first.execute (sourceEnvironment P) Reference state
      let indicator := fun values : (CShape.fixedVector count
          (.fixedVector (sampleWidth P) (.finite 2))).Value =>
        if observedOutcome P (values.get (selection 0)) = outcomes (selection 0)
          then (1 : ℂ) else 0
      have tailStable : ∀ (index : Fin attempts) store basis,
          (weight ((measuredStore P (selection index.succ) store basis).read
              (samplesInput P count)) *
            indicator ((measuredStore P (selection index.succ) store basis).read
              (samplesInput P count))) =
          weight (store.read (samplesInput P count)) *
            indicator (store.read (samplesInput P count)) := by
        intro index store basis
        rw [stable]
        apply congrArg (fun value : ℂ => weight (store.read (samplesInput P count)) * value)
        unfold indicator
        rw [samplesInput_get, samplesInput_get, observed_other_after_measurement]
        intro same
        have impossible := distinct same
        exact Fin.succ_ne_zero index impossible
      have tail := ih (fun index => selection index.succ)
        (fun left right same => Fin.succ_injective _ (distinct same))
        (fun values => weight values * indicator values) tailStable advanced
        (round_seeded P (selection 0) expansion state)
      have composed := QuantumAlg.Circuit.referenceFiberSum_execute_seq
        (environment := sourceEnvironment P)
        (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
        (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
        first (QuantumAlg.Circuit.forRange attempts
          (fun index => round P (selection index.succ) expansion)) state
        (fun store => weight (store.read (samplesInput P count)) *
          ∏ index : Fin (attempts + 1),
            if observedOutcome P (store.read (sampleInput P (selection index))) =
              outcomes (selection index) then 1 else 0) leftRef rightRef
      refine composed.trans ?_
      simp only [Fin.prod_univ_succ]
      have leftReassociate :
          ExecutionState.referenceFiberSum
            ((QuantumAlg.Circuit.forRange attempts
              (fun index => round P (selection index.succ) expansion)).execute
                (sourceEnvironment P) Reference advanced)
            (fun entry _ => weight (entry.1.read (samplesInput P count)) *
              ((if observedOutcome P (entry.1.read (sampleInput P (selection 0))) =
                outcomes (selection 0) then 1 else 0) *
                ∏ index : Fin attempts,
                  if observedOutcome P (entry.1.read (sampleInput P (selection index.succ))) =
                    outcomes (selection index.succ) then 1 else 0)) leftRef rightRef =
          ExecutionState.referenceFiberSum
            ((QuantumAlg.Circuit.forRange attempts
              (fun index => round P (selection index.succ) expansion)).execute
                (sourceEnvironment P) Reference advanced)
            (fun entry _ => (weight (entry.1.read (samplesInput P count)) *
              indicator (entry.1.read (samplesInput P count))) *
              ∏ index : Fin attempts,
                if observedOutcome P (entry.1.read (sampleInput P (selection index.succ))) =
                  outcomes (selection index.succ) then 1 else 0) leftRef rightRef := by
        simp only [indicator, samplesInput_get, mul_assoc]
      refine leftReassociate.trans (tail.trans ?_)
      let probability := ∏ index : Fin attempts,
        ((Binary.outcomePMF P expansion (outcomes (selection index.succ))).toReal : ℂ)
      have firstLaw := round_outcome_weighted_reference P (selection 0) expansion
        (fun values => weight values * probability)
        (fun store basis => congrArg (fun value : ℂ => value * probability)
          (stable 0 store basis)) state seeded (outcomes (selection 0)) leftRef rightRef
      have rearrangeLeft :
          ExecutionState.referenceFiberSum advanced
            (fun entry _ => (weight (entry.1.read (samplesInput P count)) *
              indicator (entry.1.read (samplesInput P count))) * probability)
            leftRef rightRef =
          ExecutionState.referenceFiberSum advanced
            (fun entry _ => (weight (entry.1.read (samplesInput P count)) * probability) *
              (if observedOutcome P (entry.1.read (sampleInput P (selection 0))) =
                outcomes (selection 0) then 1 else 0)) leftRef rightRef := by
        apply congrArg (fun observe =>
          ExecutionState.referenceFiberSum advanced observe leftRef rightRef)
        funext entry basis
        simp only [indicator, samplesInput_get]
        ac_rfl
      refine rearrangeLeft.trans (firstLaw.trans ?_)
      apply congrArg (fun observe =>
        ExecutionState.referenceFiberSum state observe leftRef rightRef)
      funext entry basis
      change (_ * probability) * _ = _ * (_ * probability)
      ac_rfl

/-- Every real sequential slot has the independent binary source law with its full reference. -/
private lemma rounds_vector_reference (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (seeded : BasisSeeded.Holds (context P count).quantumLayout.zeroLabel state)
    (outcomes : List.Vector (TerminalZMeasure.Outcome (sampleWidth P)) count)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((rounds P count expansion).execute
      (sourceEnvironment P) Reference state)
      (fun entry _ => if observedVector P count (entry.1.read (samplesInput P count)) = outcomes
        then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ((PMF.independentReplicateVector (Binary.outcomePMF P expansion)
          count outcomes).toReal : ℂ)) leftRef rightRef := by
  have actual := selected_rounds_reference P count count id Function.injective_id expansion
    (fun _ => 1) (by intro _ _ _; rfl) state seeded outcomes.get leftRef rightRef
  simp only [one_mul, id_eq] at actual
  have observation (store : Store (context P count)) :
      (∏ index : Fin count,
        if observedOutcome P (store.read (sampleInput P index)) = outcomes.get index
          then (1 : ℂ) else 0) =
      if observedVector P count (store.read (samplesInput P count)) = outcomes then 1 else 0 := by
    by_cases equal : observedVector P count (store.read (samplesInput P count)) = outcomes
    · rw [if_pos equal]
      apply Finset.prod_eq_one
      intro index _
      have coordinate := congrArg
        (fun vector : List.Vector (TerminalZMeasure.Outcome (sampleWidth P)) count =>
          vector.get index) equal
      have same : observedOutcome P (store.read (sampleInput P index)) = outcomes.get index := by
        simpa only [observedVector, List.Vector.get_ofFn, samplesInput_get] using coordinate
      exact if_pos same
    · rw [if_neg equal]
      have different : ∃ index : Fin count,
          observedOutcome P (store.read (sampleInput P index)) ≠ outcomes.get index := by
        by_contra allSame
        apply equal
        apply List.Vector.ext
        intro index
        have same : observedOutcome P (store.read (sampleInput P index)) = outcomes.get index := by
          by_contra different
          exact allSame ⟨index, different⟩
        simpa only [observedVector, List.Vector.get_ofFn, samplesInput_get] using same
      obtain ⟨index, different⟩ := different
      exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg different)
  simp only [observation] at actual
  refine actual.trans ?_
  apply congrArg (fun coefficient : ℂ =>
    ExecutionState.referenceFiberSum state (fun _ _ => coefficient) leftRef rightRef)
  simp only [PMF.independentReplicateVector_toReal_prod, Complex.ofReal_prod]

/-- The real prefix and sequential run have the product law in every prepared reference fiber. -/
public lemma code_vector_reference (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference ((model P).HiddenState × History))
    (outcomes : List.Vector (TerminalZMeasure.Outcome (sampleWidth P)) count)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code P count expansion).execute
      (sourceEnvironment P) Reference state)
      (fun entry _ => if observedVector P count (entry.1.read (samplesInput P count)) = outcomes
        then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum ((initialCode P count).execute
        (sourceEnvironment P) Reference state)
        (fun _ _ => ((PMF.independentReplicateVector (Binary.outcomePMF P expansion)
          count outcomes).toReal : ℂ)) leftRef rightRef := by
  refine (QuantumAlg.Circuit.referenceFiberSum_execute_seq
    (environment := sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
    (initialCode P count) (rounds P count expansion) state
    (fun store => if observedVector P count (store.read (samplesInput P count)) = outcomes
      then 1 else 0) leftRef rightRef).trans ?_
  exact rounds_vector_reference P count expansion _ (initialCode_seeded P count state)
    outcomes leftRef rightRef

/-- Actual output samples follow the independent product law for every certified empty input. -/
public lemma reusable_run_outputDistribution (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) {Reference : Register}
    (input : OracleInput (model P).classicalOracles pre Reference) :
    ((run P count expansion).outputDistribution
      (sourceEnvironment P) input).map (observedVector P count) =
      PMF.independentReplicateVector (Binary.outcomePMF P expansion) count := by
  let recorded := input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized : recorded.IsNormalized :=
    (ExecutionState.mapClassical_mass input.state _).trans input.normalized
  have initialized : ((initialCode P count).execute
    (sourceEnvironment P) Reference recorded).IsNormalized :=
    (QuantumAlg.Circuit.execute_mass
      (environment := sourceEnvironment P)
      (initialCode P count) Reference recorded).trans normalized
  rw [AlgorithmRun.outputDistribution, PMF.map_comp]
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum
    ((initialCode P count).execute (sourceEnvironment P) Reference recorded) _ initialized
  intro outcomes leftRef rightRef
  exact code_vector_reference P count expansion recorded outcomes leftRef rightRef

/-- Preparing the one bank and taking its first actual sample needs no caller state promise. -/
public lemma initial_round_toPMF (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference ((model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    (((((initialCode P count).seq (round P slot expansion)).execute
      (sourceEnvironment P) Reference state).toPMF
      (by exact (QuantumAlg.Circuit.execute_mass
        (environment := sourceEnvironment P)
        ((initialCode P count).seq (round P slot expansion)) Reference state).trans normalized)).map
      (fun entry => observedOutcome P (entry.1.read (sampleInput P slot)))) =
      Binary.outcomePMF P expansion := by
  have initialized : ((initialCode P count).execute
    (sourceEnvironment P) Reference state).IsNormalized :=
    (QuantumAlg.Circuit.execute_mass
      (environment := sourceEnvironment P) (initialCode P count) Reference state).trans normalized
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum
    ((initialCode P count).execute (sourceEnvironment P) Reference state) _ initialized
  intro outcome leftRef rightRef
  refine (QuantumAlg.Circuit.referenceFiberSum_execute_seq
    (environment := sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
    (initialCode P count) (round P slot expansion) state
    (fun store => if observedOutcome P (store.read (sampleInput P slot)) = outcome
      then 1 else 0) leftRef rightRef).trans ?_
  simpa only [one_mul] using round_outcome_weighted_reference P slot expansion
    (fun _ => 1) (by intro _ _; rfl) ((initialCode P count).execute
      (sourceEnvironment P) Reference state)
    (initialCode_seeded P count state) outcome leftRef rightRef

end

end QuantumAlg.FiniteCyclicDLP.Reusable
