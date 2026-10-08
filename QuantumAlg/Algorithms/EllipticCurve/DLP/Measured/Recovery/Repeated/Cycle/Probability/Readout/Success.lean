/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Acceptance
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Section
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect.Failure
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect.Store
import all QuantumAlg.Core.Base.Gate.Effect.Bounds

/-!
# A completed checked section meets its independent success threshold

The source-derived contraction concerns the actual circuit on the admitted
joint input. Its final-Store failure weight is the same observable on the
complete algorithm run, including retained original-input history. Supported
output records identify the independent relation with the final accepted bit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (problem : KnownOrderProblem E.GroupPoint)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

omit [Fact p.Prime] in
private theorem failureWeight_nonneg_le_mass {Reference : Register} {H : Type} [Fintype H]
    (state : State (sectionCtx E problem) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    0 ≤ persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      state ∧
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      state ≤ state.mass := by
  unfold persistentFailureWeight ExecutionState.effectWeight ExecutionState.mass
  constructor
  · exact Finset.sum_nonneg (fun value _ => Effect.weight_nonneg _ _)
  · exact Finset.sum_le_sum (fun value _ => Effect.weight_le_mass _ _)

private theorem ofReal_failure_le_of_contract (final initial floor : ℝ)
    (finalNonneg : 0 ≤ final) (initialNonneg : 0 ≤ initial)
    (initialLe : initial ≤ 1) (contracts : final ≤ (1 - floor) * initial) :
    ENNReal.ofReal final ≤ ENNReal.ofReal (1 - floor) := by
  by_cases scale : 0 ≤ 1 - floor
  · apply ENNReal.ofReal_le_ofReal
    calc
      final ≤ (1 - floor) * initial := contracts
      _ ≤ (1 - floor) * 1 := mul_le_mul_of_nonneg_left initialLe scale
      _ = 1 - floor := mul_one _
  · have nonpos : (1 - floor) * initial ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge scale)) initialNonneg
    have zero : final = 0 := le_antisymm (contracts.trans nonpos) finalNonneg
    simp [zero]

/-- A physical one-section failure contraction, together with the real
supported-record acceptance equivalence, establishes the independent
relational success lower bound for the complete algorithm run. -/
theorem checkedSection_relational_success_ge_of_failureContract
    (floor : ℝ)
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (readout : run.output = Output.all _ (checkedSectionRead E problem))
    (retainsValidity : RetainsValidity E problem run.code)
    (retainsBound : RetainsSelectedBound E problem run.code)
    (retainsFirst : RetainsFirst E problem run.code)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (contracts : persistentFailureWeight
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      (run.code.execute Reference (State.skip input.state)) ≤
        (1 - floor) *
        persistentFailureWeight
          (model := .quantum AlgorithmGate.model .empty BitWord.model)
          (ctx := PublicInput.terminal E (orderWidth problem))
          (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
          (State.skip input.state)) :
    1 - ENNReal.ofReal (1 - floor) ≤
      (run.relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2} := by
  let initial := persistentFailureWeight
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem))
    (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    (State.skip input.state)
  let final := persistentFailureWeight
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem))
    (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    (run.code.execute Reference (State.skip input.state))
  have initialBounds := failureWeight_nonneg_le_mass E problem (State.skip input.state)
  have initialLe : initial ≤ 1 := by
    exact initialBounds.2.trans (le_of_eq ((State.skip_mass input.state).trans input.normalized))
  have finalNonneg : 0 ≤ final :=
    (failureWeight_nonneg_le_mass E problem
      (run.code.execute Reference (State.skip input.state))).1
  have contraction : final ≤ (1 - floor) * initial := contracts
  have finalLe : ENNReal.ofReal final ≤ ENNReal.ofReal (1 - floor) :=
    ofReal_failure_le_of_contract final initial floor finalNonneg
      initialBounds.1 initialLe contraction
  have agrees : ∀ record ∈ (run.executionDistribution input).support,
      checkedSectionAccepts E problem record.2.2.1 (run.result record) ↔
        (checkedSectionLatches E problem record.1).1 = true := by
    intro record supported
    exact checkedSection_accepts_iff_finalAccepted E problem run readout
      retainsValidity retainsBound retainsFirst input valid record supported
  have observed := AlgorithmRun.relational_success_eq_one_sub_failure_effectWeight
    run input (fun pair => checkedSectionAccepts E problem pair.1 pair.2)
    (fun record => (checkedSectionLatches E problem record.1).1) agrees
  have physical :
      (run.execute Reference input.state).effectWeight (fun record =>
        if (checkedSectionLatches E problem record.1).1 = false then
          Effect.one ((sectionCtx E problem).register.prod Reference)
        else Effect.zero ((sectionCtx E problem).register.prod Reference)) = final := by
    calc
      _ = (run.code.execute Reference (State.skip input.state)).effectWeight
          (fun record => if (checkedSectionLatches E problem record.1).1 = false then
            Effect.one ((sectionCtx E problem).register.prod Reference)
          else Effect.zero ((sectionCtx E problem).register.prod Reference)) :=
        AlgorithmRun.storedEffectWeight_eq_code_skip run input (fun store =>
          if (checkedSectionLatches E problem store).1 = false then
            Effect.one ((sectionCtx E problem).register.prod Reference)
          else Effect.zero ((sectionCtx E problem).register.prod Reference))
      _ = final := by
        simp only [final, persistentFailureWeight]
        congr 1
  rw [physical] at observed
  exact (tsub_le_tsub_left finalLe 1).trans_eq observed.symm

/-- The source-derived corrected floor instantiates the generic actual-run
success theorem without an additional positivity premise. -/
theorem checkedSection_successLB_of_failureContract
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (readout : run.output = Output.all _ (checkedSectionRead E problem))
    (retainsValidity : RetainsValidity E problem run.code)
    (retainsBound : RetainsSelectedBound E problem run.code)
    (retainsFirst : RetainsFirst E problem run.code)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (contracts : persistentFailureWeight
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      (run.code.execute Reference (State.skip input.state)) ≤
        (1 - ((problem.order : ℝ) * Nat.totient problem.order /
          (4 * (fourierModulus problem : ℝ) ^ 2) -
            4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
        persistentFailureWeight
          (model := .quantum AlgorithmGate.model .empty BitWord.model)
          (ctx := PublicInput.terminal E (orderWidth problem))
          (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
          (State.skip input.state)) :
    (checkedSectionSuccessLB E problem points seed).value ≤
      (run.relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2} := by
  change 1 - ENNReal.ofReal (1 - ((problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed))) ≤ _
  exact checkedSection_relational_success_ge_of_failureContract E problem _ run
    readout retainsValidity retainsBound retainsFirst input valid contracts

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
