/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.SuccessFloor
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Reuse
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Selected-event weight in the actual original ECDLP execution

Tracing the actual full-reference sampling law gives the exact selected
mass multiplied by the incoming state's mass. Initial allocation and paid
reuse each discharge their own seed condition. The state may have arbitrary
classical correlations and need not be normalized; its zero-mass case is
included without division. Every effect observes the real finite readouts.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (condition : Prop) : Decidable condition := Classical.propDecidable condition

private theorem selected_weight_of_referenceLaw
    {C D Outcome : Type} [Fintype C] [Fintype D] [Finite Outcome]
    {R S Reference : Register}
    (initial : ExecutionState C (Register.prod R Reference))
    (final : ExecutionState D (Register.prod S Reference))
    (read : D → Outcome) (distribution : PMF Outcome) (selected : Finset Outcome)
    [selectedDecidable : DecidablePred (fun outcome => outcome ∈ selected)]
    (observed : ∀ outcome left right,
      ExecutionState.referenceFiberSum final
          (fun entry _ => if read entry = outcome then 1 else 0) left right =
        ((distribution outcome).toReal : ℂ) *
          ExecutionState.referenceFiberSum initial (fun _ _ => 1) left right) :
    final.effectWeight (fun entry =>
      if read entry ∈ selected then Effect.one (Register.prod S Reference)
      else Effect.zero (Register.prod S Reference)) =
        (distribution.toOuterMeasure (↑selected : Set Outcome)).toReal * initial.mass := by
  classical
  let : Fintype Outcome := Fintype.ofFinite Outcome
  have masses (outcome : Outcome) :
      ((final.mapClassical read).block outcome).mass =
        (distribution outcome).toReal * initial.mass := by
    refine (ExecutionState.mapClassical_block_mass_referenceFiberSum final read outcome).trans ?_
    have entries := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun reference _ => observed outcome reference reference)
    have traced := entries.trans ((Finset.mul_sum _ _ _).symm.trans
      (congrArg (fun value : ℂ => ((distribution outcome).toReal : ℂ) * value)
        (ExecutionState.referenceFiberSum_sum_constant initial 1)))
    simpa only [one_mul, ← Complex.ofReal_mul, Complex.ofReal_re] using
      congrArg Complex.re traced
  have grouped : final.effectWeight (fun entry =>
      if read entry ∈ selected then Effect.one (Register.prod S Reference)
      else Effect.zero (Register.prod S Reference)) =
      ∑ outcome ∈ selected, ((final.mapClassical read).block outcome).mass := by
    rw [← ExecutionState.effectWeight_mapClassical final read
      (fun outcome => if outcome ∈ selected then Effect.one (Register.prod S Reference)
        else Effect.zero (Register.prod S Reference))]
    unfold ExecutionState.effectWeight
    calc
      _ = ∑ outcome, if outcome ∈ selected then
          ((final.mapClassical read).block outcome).mass else 0 := by
        apply Finset.sum_congr rfl
        intro outcome _
        by_cases found : outcome ∈ selected
        · simp only [if_pos found]
          exact Effect.weight_one _
        · simp only [if_neg found]
          exact Effect.weight_zero _
      _ = _ := by simp
  rw [grouped]
  simp only [masses, ← Finset.sum_mul]
  congr 1
  rw [PMF.toOuterMeasure_apply_finset, ENNReal.toReal_sum
    (fun outcome _ => distribution.apply_ne_top outcome)]

private theorem selected_circuit_weight_of_referenceLaw
    {pre post : RuntimeCtx .quantum} (code : Circuit pre post)
    {Outcome : Type} [Finite Outcome] {Reference : Register}
    {History : Type} [Fintype History] (state : State pre Reference History)
    (read : Store post → Outcome) (distribution : PMF Outcome) (selected : Finset Outcome)
    [selectedDecidable : DecidablePred (fun outcome => outcome ∈ selected)]
    (observed : ∀ outcome left right,
      ExecutionState.referenceFiberSum (code.execute Reference state)
          (fun entry _ => if read entry.1 = outcome then 1 else 0) left right =
        ((distribution outcome).toReal : ℂ) *
          ExecutionState.referenceFiberSum state (fun _ _ => 1) left right) :
    (code.execute Reference state).effectWeight (fun entry =>
      if read entry.1 ∈ selected then Effect.one (post.register.prod Reference)
      else Effect.zero (post.register.prod Reference)) =
        (distribution.toOuterMeasure (↑selected : Set Outcome)).toReal * state.mass := by
  exact selected_weight_of_referenceLaw state (code.execute Reference state)
    (fun entry => read entry.1) distribution selected observed

private theorem selected_probability_toReal_ge
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) :
    (FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound (problem I)).toReal ≤
      ((outcomePMF I B A).toOuterMeasure
        {outcome | outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I)
          (input I)}).toReal := by
  apply ENNReal.toReal_mono _ (nativeECDLP_selectedFamily_probability_ge I B A)
  rw [PMF.toOuterMeasure_apply]
  exact (outcomePMF I B A).tsum_coe_indicator_ne_top _

attribute [local irreducible] context run sample reusedSample
  FiniteCyclicDLP.Canonical.Probability.selectedRawOutcomeFamily

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

/-- Initial real sampling gives the exact selected weight on every full incoming state. -/
theorem nativeECDLP_first_selected_weight
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    ((run base noQuantum I B A).code.execute Reference state).effectWeight (fun entry =>
      if observedOutcome I (entry.1.read (sampleInput base noQuantum I)) ∈
          FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I) then
        Effect.one ((context base noQuantum I).register.prod Reference)
      else Effect.zero ((context base noQuantum I).register.prod Reference)) =
      ((outcomePMF I B A).toOuterMeasure
        {outcome | outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I)
          (input I)}).toReal * state.mass := by
  refine selected_circuit_weight_of_referenceLaw (pre := base)
    (post := context base noQuantum I) (Outcome := Fin (sampleWidth I) → Bool)
    (Reference := Reference) (History := History)
    (selectedDecidable := fun outcome => Classical.propDecidable _)
    (run base noQuantum I B A).code state
    (fun store => observedOutcome I (store.read (sampleInput base noQuantum I)))
    (outcomePMF I B A)
    (FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I)) ?_
  intro outcome left right
  have actual := nativeECDLP_first_outcome_reference base noQuantum I B A
    (.fixedVector (fun index : Fin 0 => Fin.elim0 index) : CInputRef base (.fixedVector 0 .bit))
    state (fun _ => (1 : ℂ)) outcome left right
  simp only [one_mul] at actual
  refine Eq.trans ?_ actual
  congr 1
  funext entry index
  split_ifs <;> rfl

/-- Paid reuse gives the exact selected weight without a seed or normalization premise. -/
theorem nativeECDLP_reusedSample_selected_weight
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History) :
    ((reusedSample base noQuantum I B A).execute Reference state).effectWeight (fun entry =>
      if observedOutcome I (entry.1.read (sampleInput base noQuantum I)) ∈
          FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I) then
        Effect.one ((context base noQuantum I).register.prod Reference)
      else Effect.zero ((context base noQuantum I).register.prod Reference)) =
      ((outcomePMF I B A).toOuterMeasure
        {outcome | outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I)
          (input I)}).toReal * state.mass := by
  refine selected_circuit_weight_of_referenceLaw (pre := context base noQuantum I)
    (post := context base noQuantum I) (Outcome := Fin (sampleWidth I) → Bool)
    (Reference := Reference) (History := History)
    (selectedDecidable := fun outcome => Classical.propDecidable _)
    (reusedSample base noQuantum I B A) state
    (fun store => observedOutcome I (store.read (sampleInput base noQuantum I)))
    (outcomePMF I B A)
    (FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I)) ?_
  intro outcome left right
  have actual := nativeECDLP_reusedSample_outcome_reference base noQuantum I B A
    (.fixedVector (fun index : Fin 0 => Fin.elim0 index) : CInputRef base (.fixedVector 0 .bit))
    state (fun _ => (1 : ℂ)) outcome left right
  simp only [one_mul] at actual
  refine Eq.trans ?_ actual
  congr 1
  funext entry index
  split_ifs <;> rfl

/-- The original selected floor applies to the same complete first-sample state. -/
theorem nativeECDLP_first_selected_weight_ge
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    (FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound (problem I)).toReal * state.mass ≤
      ((run base noQuantum I B A).code.execute Reference state).effectWeight (fun entry =>
        if observedOutcome I (entry.1.read (sampleInput base noQuantum I)) ∈
            FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I) then
          Effect.one ((context base noQuantum I).register.prod Reference)
        else Effect.zero ((context base noQuantum I).register.prod Reference)) := by
  rw [nativeECDLP_first_selected_weight]
  exact mul_le_mul_of_nonneg_right (selected_probability_toReal_ge I B A) state.mass_nonneg

/-- The original selected floor applies after every actual paid reuse, including zero mass. -/
theorem nativeECDLP_reusedSample_selected_weight_ge
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History) :
    (FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound (problem I)).toReal * state.mass ≤
      ((reusedSample base noQuantum I B A).execute Reference state).effectWeight (fun entry =>
        if observedOutcome I (entry.1.read (sampleInput base noQuantum I)) ∈
            FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I) then
          Effect.one ((context base noQuantum I).register.prod Reference)
        else Effect.zero ((context base noQuantum I).register.prod Reference)) := by
  rw [nativeECDLP_reusedSample_selected_weight]
  exact mul_le_mul_of_nonneg_right (selected_probability_toReal_ge I B A) state.mass_nonneg

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
