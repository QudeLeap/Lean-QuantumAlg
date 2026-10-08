/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Domain
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Correctness

/-!
# Admission from the actual generic ECC caller prefix

The original initialization and seven-cell allocation establish the first
checked section's public points and retained-selection invariant on every
admitted caller state. No public-point or latch condition is added to the
caller, and all quantum states and external references remain admitted.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Circuit.nextInput Circuit.execute

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)
  (problem : KnownOrderProblem E.GroupPoint)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The original selected initialization and real seven-cell allocation. -/
def checkedRunPrefix :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem) :=
  (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).seq
    (retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem))

private theorem prefix_supported_publicPoints
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem))
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference)
    (valid : PublicInput.inputDomain E (orderWidth problem) problem input.caller.localState)
    (result : Store (sectionCtx E problem) × (Unit × (Unit × code.Path)))
    (positive : 0 < ((code.execute Reference (input.state.mapClassical
      (fun value => (value.1, (value.2, ()))))).block result).mass) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (result.1.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalBaseRef E (orderWidth problem)))) problem.generator.toMathlib ∧
    PointRepresents (Canonical.Layout.curveSpec E)
      (result.1.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalTargetRef E (orderWidth problem)))) problem.target.toMathlib := by
  have restored := code.borrowedRestored_of_noBorrowedQuantum
    (PublicInput.before_noBorrowedQuantum E (orderWidth problem)) Reference
    (input.state.mapClassical (fun value => (value.1, (value.2, ()))))
  obtain ⟨previous, present, same⟩ := code.borrowedRestored_supported_initial
    Reference (input.state.mapClassical (fun value => (value.1, (value.2, ()))))
    _ restored result positive
  have callerPositive : 0 < (input.caller.localState.block previous.1).mass := by
    rw [input.enteredState_eq_skip] at present
    rcases previous with ⟨store, hidden, history⟩
    cases history
    exact input.caller_local_mass_pos_of_joint (store, hidden)
      ((State.skip_block_mass_pos_iff input.state store hidden).mp present)
  obtain ⟨base, target⟩ := valid previous.1 callerPositive
  have prescribed := PublicInput.initialStore_split_left E (orderWidth problem)
    problem previous.1 base target
  have points := PublicInput.persistent_points_of_borrowed E (orderWidth problem)
    problem (split (PublicInput.before_disjoint E (orderWidth problem)) previous.1).1
    result.1 ((heq_of_eq (congrArg Store.readBorrowedClassical prescribed)).trans
      ((heq_of_eq same).trans
        (PublicInput.borrowed_transport_heq code result.1.readBorrowedClassical)))
  rw [points.1, points.2]
  exact ⟨publicPoint_represents E problem.generator,
    publicPoint_represents E problem.target⟩

private theorem allocationAfterSetup_nextInput_domain [Fact p.Prime]
    (setup : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem))) (nontrivial : 2 ≤ problem.order)
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference)
    (valid : PublicInput.inputDomain E (orderWidth problem) problem input.caller.localState) :
    checkedSectionInputDomain E problem
      ((setup.seq (retainPersistent
        (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))).nextInput
          input).caller.localState := by
  intro store positive
  let code := setup.seq (retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem))
  rw [Input.localState_block_mass] at positive
  change 0 < (((code.nextInput input).state.mapClassical Prod.fst).block store).mass
    at positive
  obtain ⟨record, sameCaller, present⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff
      (code.nextInput input).state Prod.fst store).mp positive
  have jointPositive : 0 < ((code.nextInput input).localState.block record).mass := by
    simpa only [OracleInput.oracleInput_localState_block,
      DensityOperator.marginalLeft_mass] using present
  obtain ⟨result, sameStore, _, supported⟩ :=
    Circuit.nextInput_local_supported_execution code input record jointPositive
  have points := prefix_supported_publicPoints E problem code input valid result supported
  have initialized := retainPersistent_initialized_invariant setup
    (Canonical.Layout.fieldWidth E) (orderWidth problem) problem.order
    (lt_of_lt_of_le (by decide : 0 < 2) nontrivial)
    (fun store =>
      (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
        problem.generator.toMathlib = problem.target.toMathlib)
    (input.state.mapClassical (fun value => (value.1, (value.2, ()))))
  have invariant := initialized result supported
  have finalStore : result.1 = store := sameStore.trans sameCaller
  rw [finalStore] at points invariant
  exact ⟨points.1, points.2, invariant.1, invariant.2⟩

/-- The actual caller prefix establishes every clause required to admit
the first completed checked section, with no extra caller assumption. -/
theorem checkedRunPrefix_nextInput_domain [Fact p.Prime] (nontrivial : 2 ≤ problem.order)
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference)
    (valid : PublicInput.inputDomain E (orderWidth problem) problem input.caller.localState) :
    checkedSectionInputDomain E problem
      ((checkedRunPrefix E problem).nextInput input).caller.localState := by
  exact allocationAfterSetup_nextInput_domain E problem
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem)) nontrivial input valid

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
