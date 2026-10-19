/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Probability.Finite
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Support
import all QuantumAlg.Core.Execution.Input.Successor.Distribution
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Loop

/-!
# Original input-domain admission into the native persistent carrier

The domain contains exactly the two point interpretations and the original
bounded selected-word/accepted-equation invariant. The caller supplies only
the original point-value domain. Actual allocation initializes the seven
latches; no seed or latch premise is added to the caller.

This proves the domain component of checked-section admission. The first
section has trivial initialization; a reused section additionally requires
the prescribed joint seed established by the preceding reset. Boundary.Seed
proves that seed bridge, and Boundary.Solves assembles the initialized
first-cycle contract from the separate state, time and resource proof owners.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

attribute [local irreducible] persistentCtx ExecutionState.mapClassical Circuit.execute

private lemma caller_supported_execution {origin resultCtx : RuntimeCtx .quantum}
    (code : Circuit Model origin resultCtx) {Reference : Register}
    (input : OracleInput .empty origin Reference) (store : Store resultCtx)
    (positive : 0 < ((code.nextInput environment input).caller.localState.block store).mass) :
    ∃ result : Store resultCtx × (Unit × (Unit × code.Path)), result.1 = store ∧
      0 < ((code.execute environment Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, ()))))).block result).mass := by
  rw [Input.localState_block_mass] at positive
  change 0 < (((code.nextInput environment input).state.mapClassical Prod.fst).block store).mass
    at positive
  obtain ⟨record, sameCaller, present⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff
      (code.nextInput environment input).state Prod.fst store).mp positive
  have jointPositive : 0 < ((code.nextInput environment input).localState.block record).mass := by
    simpa only [OracleInput.oracleInput_localState_block,
      DensityOperator.marginalLeft_mass] using present
  obtain ⟨result, sameStore, _, supported⟩ :=
    Circuit.nextInput_local_supported_execution code environment input record jointPositive
  refine ⟨result, sameStore.trans sameCaller, ?_⟩
  convert supported using 1
  congr 1

private lemma support_from_history {origin resultCtx : RuntimeCtx .quantum}
    (code : Circuit Model origin resultCtx) {Reference : Register}
    (input : OracleInput .empty origin Reference)
    {Before : Type} [Fintype Before]
    (entered : State origin Reference (Model.HiddenState × Before))
    (incoming : entered.mapHistory (fun record => (record.1, ())) =
      input.state.mapClassical (fun value => (value.1, (value.2, ()))))
    (predicate : Store resultCtx → Prop)
    (supported : storeSupported (code.execute environment Reference entered) predicate) :
    storeSupported (code.execute environment Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, ()))))) predicate := by
  rw [← incoming]
  exact (FiniteSuccess.support_execute_mapHistory code entered (fun _ => ()) predicate).mpr
    supported

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (problem : KnownOrderProblem E.GroupPoint)

private def storeDomain (store : Store (sectionCtx E problem)) : Prop :=
  ClassicalRoutines.EllipticCurve.PointRepresents (ECDLP.Canonical.Layout.curveSpec E)
    (store.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem)))) problem.generator.toMathlib ∧
  ClassicalRoutines.EllipticCurve.PointRepresents (ECDLP.Canonical.Layout.curveSpec E)
    (store.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem)))) problem.target.toMathlib ∧
  (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat < problem.order ∧
  ((store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
    (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
      problem.generator.toMathlib = problem.target.toMathlib)

/-- All four original classical admission clauses on the explicitly migrated live carrier. -/
def InputDomain
    (localState : ExecutionState (Store (sectionCtx E problem)) (sectionCtx E problem).register) :
    Prop :=
  ∀ store, 0 < (localState.block store).mass → storeDomain E problem store

section PointSupport

attribute [local irreducible] storeSupported

omit [Fact p.Prime] in
private lemma prefix_supported_points
    (code : Circuit Model (Recovery.PublicInput.frame E (orderWidth problem)) (sectionCtx E
      problem))
    {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      input.caller.localState) :
    storeSupported (code.execute environment Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, ()))))) (fun store =>
      ClassicalRoutines.EllipticCurve.PointRepresents (ECDLP.Canonical.Layout.curveSpec E)
        (store.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
          (Recovery.PublicInput.contextBaseRef E (orderWidth problem))))
            problem.generator.toMathlib ∧
      ClassicalRoutines.EllipticCurve.PointRepresents (ECDLP.Canonical.Layout.curveSpec E)
        (store.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
          (Recovery.PublicInput.contextTargetRef E (orderWidth problem))))
            problem.target.toMathlib) := by
  let entered := Recovery.PublicInput.Support.enteredState E (orderWidth problem) problem
    input.caller
  have incoming : entered.mapHistory (fun record => (record.1, ())) =
      input.state.mapClassical (fun value => (value.1, (value.2, ()))) := by
    dsimp only [entered, Recovery.PublicInput.Support.enteredState, State.mapHistory]
    rw [FiniteSuccess.oracleInput_eq_of_domain E problem input valid]
    exact ExecutionState.executionState_mapClassical_comp_instances input.state _ _
  apply support_from_history code input entered incoming
  unfold storeSupported
  intro record positive
  exact Recovery.PublicInput.Support.persistentProgram_supported_represents E (orderWidth problem)
    problem code input.caller record positive

end PointSupport

/-- Every originally admitted Reference extension enters all four clauses after the real prefix. -/
lemma prefix_nextInput_domain {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference)
    (valid : Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
      input.caller.localState) :
    InputDomain E problem ((«prefix» E problem).nextInput environment input).caller.localState := by
  intro store positive
  obtain ⟨result, finalStore, supported⟩ :=
    caller_supported_execution («prefix» E problem) input store positive
  have points := prefix_supported_points (environment := environment) E problem («prefix» E
    problem) input valid result supported
  let initial : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (Model.HiddenState × Unit) :=
    input.state.mapClassical (fun value => (value.1, (value.2, ())))
  have initialized := FiniteSuccess.initialized_selected_invariant (environment := environment)
    (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)))
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) problem.order problem.order_pos
    (fun stored =>
      (stored.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
        problem.generator.toMathlib = problem.target.toMathlib)
    initial
  have invariant := initialized result supported
  have assembled : storeDomain E problem result.1 :=
    ⟨points.1, points.2, invariant.1, invariant.2⟩
  exact (congrArg (storeDomain E problem) finalStore).mp assembled

/-- The main native problem's original admission suffices; no extra initialization is requested. -/
lemma algorithm_prefix_domain (I : ECDLPInstance E) (count : Nat) (failure : ℝ)
    {Reference : Register} (input : OracleInput .empty (Spec.inputContext E I) Reference)
    (admitted : (QuantumAlg.EllipticCurve.LogicalResources.problem E I count failure).Admits
      environment ()
      input) :
    InputDomain E (ECDLP.Canonical.problem I)
      ((«prefix» E (ECDLP.Canonical.problem I)).nextInput environment input).caller.localState :=
  prefix_nextInput_domain E (ECDLP.Canonical.problem I) input admitted.1

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
