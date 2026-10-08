/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Validity
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Admission
import all QuantumAlg.Core.Execution.CycleSchedule.InputDistribution
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Actual reset seed admitted by the following checked section

The first and reused nonterminal sections both finish with a physical reset.
Its pure owned bank supplies the independent seeded initialization required by
the next reused section, after the real `nextInput` groups execution histories.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The independent admitted public points hold on every positive block of
the actual entered execution state, with its hidden service and unit history. -/
theorem checkedSection_entered_publicPoints
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (entry : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) × (Unit × Unit))
    (positive : 0 < ((State.skip input.state).block entry).mass) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalBaseRef E (orderWidth problem)))) problem.generator.toMathlib ∧
    PointRepresents (Canonical.Layout.curveSpec E)
      (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalTargetRef E (orderWidth problem)))) problem.target.toMathlib := by
  rcases entry with ⟨store, hidden, history⟩
  cases history
  have sourcePositive : 0 < (input.state.block (store, hidden)).mass :=
    (State.skip_block_mass_pos_iff input.state store hidden).mp positive
  have callerPositive := input.caller_local_mass_pos_of_joint
    (store, hidden) sourcePositive
  exact ⟨(valid store callerPositive).1, (valid store callerPositive).2.1⟩

/-- The two public-point clauses of the checked section's classical domain. -/
def checkedSectionPublicPoints
    (problem : KnownOrderProblem E.GroupPoint)
    (store : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem))) : Prop :=
  PointRepresents (Canonical.Layout.curveSpec E)
    (store.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
      (PublicInput.terminalBaseRef E (orderWidth problem)))) problem.generator.toMathlib ∧
  PointRepresents (Canonical.Layout.curveSpec E)
    (store.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
      (PublicInput.terminalTargetRef E (orderWidth problem)))) problem.target.toMathlib

/-- The actual unit-history state passed to circuit execution has the
admitted public points on every positive block. -/
theorem checkedSection_actualEntered_publicPoints
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (entry : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) × (Unit × Unit))
    (positive : 0 < ((input.state.mapClassical
      (fun value => (value.1, (value.2, ())))).block entry).mass) :
    checkedSectionPublicPoints E problem entry.1 := by
  rw [input.enteredState_eq_skip] at positive
  exact checkedSection_entered_publicPoints E problem input valid entry positive

/-- History projection at a real section boundary preserves the admitted
selected-word range established by the preceding section's execution. -/
theorem checkedSection_nextInput_selectedBound
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    (keeps : RetainsSelectedBound E problem code)
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < ((code.nextInput input).localState.block record).mass) :
    SelectedWithinOrder E problem record.1 := by
  have enteredBound : ∀ entry,
      0 < ((input.state.mapClassical
        (fun value => (value.1, (value.2, ())))).block entry).mass →
      SelectedWithinOrder E problem entry.1 := by
    intro entry present
    rw [input.enteredState_eq_skip] at present
    rcases entry with ⟨store, hidden, history⟩
    cases history
    have sourcePositive : 0 < (input.state.block (store, hidden)).mass :=
      (State.skip_block_mass_pos_iff input.state store hidden).mp present
    have callerPositive := input.caller_local_mass_pos_of_joint
      (store, hidden) sourcePositive
    exact (valid store callerPositive).2.2.1
  obtain ⟨result, sameStore, _, supported⟩ :=
    Circuit.nextInput_local_supported_execution code input record positive
  have bounded := keeps (input.state.mapClassical
    (fun value => (value.1, (value.2, ())))) enteredBound result supported
  rw [sameStore] at bounded
  exact bounded

/-- Both admitted public-point interpretations survive one real persistent
section and the history projection into its successor input. -/
theorem checkedSection_nextInput_publicPoints
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < ((code.nextInput input).localState.block record).mass) :
    checkedSectionPublicPoints E problem record.1 := by
  have noQuantum :
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  obtain ⟨previous, present, baseEq, targetEq⟩ :=
    PublicInput.persistentProgram_nextInput_publicPointReads E (orderWidth problem)
      code noQuantum input record positive
  have priorPoints := checkedSection_actualEntered_publicPoints E problem input valid
    previous present
  unfold checkedSectionPublicPoints at priorPoints ⊢
  constructor
  · rw [← baseEq]
    exact priorPoints.1
  · rw [← targetEq]
    exact priorPoints.2

/-- History projection carries the full accepted-scalar validity invariant
through an actual completed persistent section. -/
theorem checkedSection_nextInput_validity
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    (keeps : RetainsValidity E problem code)
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < ((code.nextInput input).localState.block record).mass) :
    CheckedSelectionValid E problem record.1 := by
  have enteredValid : ∀ entry,
      0 < ((input.state.mapClassical
        (fun value => (value.1, (value.2, ())))).block entry).mass →
      CheckedSelectionValid E problem entry.1 := by
    intro entry present
    rw [input.enteredState_eq_skip] at present
    rcases entry with ⟨store, hidden, history⟩
    cases history
    have sourcePositive : 0 < (input.state.block (store, hidden)).mass :=
      (State.skip_block_mass_pos_iff input.state store hidden).mp present
    have callerPositive := input.caller_local_mass_pos_of_joint
      (store, hidden) sourcePositive
    obtain ⟨base, target, _bound, sound⟩ := valid store callerPositive
    exact ⟨base, target, sound⟩
  obtain ⟨result, sameStore, _, supported⟩ :=
    Circuit.nextInput_local_supported_execution code input record positive
  have retained := keeps (input.state.mapClassical
    (fun value => (value.1, (value.2, ())))) enteredValid result supported
  rw [sameStore] at retained
  exact retained

private theorem nextInput_seeded
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    (fixed : Circuit.ReinitializedAt code
      (checkedSectionSeed E fieldTail sameWidth fits problem seed))
    {Reference : Register}
    (input : OracleInput .empty _ Reference) :
    checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      (code.nextInput input).localState := by
  exact Circuit.ReinitializedAt.nextInput_jointSeeded code
    (checkedSectionSeed E fieldTail sameWidth fits problem seed) fixed input

/-- The first real completed section supplies the following reused section's
fixed quantum input seed for every original local input and reference. -/
theorem firstCheckedSection_nextInput_seeded
    {Reference : Register}
    (input : OracleInput .empty _ Reference) :
    checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).nextInput input).localState :=
  nextInput_seeded E fieldTail sameWidth fits problem seed _
    (firstCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial) input

/-- Every reused nonterminal section also supplies the identical quantum
input seed to its real successor, without another initial reset. -/
theorem reusedCheckedSection_nextInput_seeded
    {Reference : Register}
    (input : OracleInput .empty _ Reference) :
    checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      ((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).nextInput input).localState :=
  nextInput_seeded E fieldTail sameWidth fits problem seed _
    (reusedCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial) input

/-- The actual first completed section admits a bounded selected word to its
successor, after grouping every execution path into the next local state. -/
theorem firstCheckedSection_nextInput_selectedBound
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < (((firstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).nextInput input).localState.block record).mass) :
    SelectedWithinOrder E problem record.1 :=
  checkedSection_nextInput_selectedBound E problem _
    (firstCheckedSection_retainsSelectedBound E fieldTail sameWidth fits odd problem
      points seed nontrivial) input valid record positive

/-- The actual reused completed section admits the same selected-word range
to the next checked section. -/
theorem reusedCheckedSection_nextInput_selectedBound
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < (((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).nextInput input).localState.block record).mass) :
    SelectedWithinOrder E problem record.1 :=
  checkedSection_nextInput_selectedBound E problem _
    (reusedCheckedSection_retainsSelectedBound E fieldTail sameWidth fits odd problem
      points seed nontrivial) input valid record positive

/-- The first real completed section admits both public point values to its
successor after forgetting its concrete execution path. -/
theorem firstCheckedSection_nextInput_publicPoints
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < (((firstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).nextInput input).localState.block record).mass) :
    checkedSectionPublicPoints E problem record.1 :=
  checkedSection_nextInput_publicPoints E problem _ input valid record positive

/-- Every real reused completed section admits the same two public points to
its successor. -/
theorem reusedCheckedSection_nextInput_publicPoints
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < (((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).nextInput input).localState.block record).mass) :
    checkedSectionPublicPoints E problem record.1 :=
  checkedSection_nextInput_publicPoints E problem _ input valid record positive

omit [Fact p.Prime] in
private theorem nextInput_empty_caller_positive_joint
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    {Reference : Register} (input : OracleInput .empty _ Reference)
    (store : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    (positive : 0 < ((code.nextInput input).caller.localState.block store).mass) :
    0 < ((code.nextInput input).localState.block (store, ())).mass := by
  rw [Input.localState_block_mass] at positive
  change 0 < (((code.nextInput input).state.mapClassical Prod.fst).block store).mass
    at positive
  obtain ⟨record, same, present⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff
      (code.nextInput input).state Prod.fst store).mp positive
  rcases record with ⟨previousStore, hidden⟩
  cases hidden
  cases same
  simpa only [OracleInput.oracleInput_localState_block,
    DensityOperator.marginalLeft_mass] using present

/-- The first complete checked section hands every clause of the independent
classical input domain to the next reused section on its actual `nextInput`. -/
theorem firstCheckedSection_nextInput_domain
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState) :
    checkedSectionInputDomain E problem
      ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).nextInput input).caller.localState := by
  intro store positive
  let code := firstCheckedSectionCode E fieldTail sameWidth fits odd problem points
    seed nontrivial
  let record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState := (store, ())
  have jointPositive : 0 < ((code.nextInput input).localState.block record).mass := by
    exact nextInput_empty_caller_positive_joint E problem code input store positive
  have current := checkedSection_nextInput_validity E problem code
    (firstCheckedSection_retainsValidity E fieldTail sameWidth fits odd problem points
      seed nontrivial) input valid record jointPositive
  have bounded := firstCheckedSection_nextInput_selectedBound E fieldTail sameWidth fits
    odd problem points seed nontrivial input valid record jointPositive
  exact ⟨current.1, current.2.1, bounded, current.2.2⟩

/-- Every reused complete checked section hands the same full classical
domain to its next real successor. -/
theorem reusedCheckedSection_nextInput_domain
    {Reference : Register}
    (input : OracleInput .empty _ Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState) :
    checkedSectionInputDomain E problem
      ((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).nextInput input).caller.localState := by
  intro store positive
  let code := reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points
    seed nontrivial
  let record : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) ×
      ClassicalOracleModel.empty.HiddenState := (store, ())
  have jointPositive : 0 < ((code.nextInput input).localState.block record).mass := by
    exact nextInput_empty_caller_positive_joint E problem code input store positive
  have current := checkedSection_nextInput_validity E problem code
    (reusedCheckedSection_retainsValidity E fieldTail sameWidth fits odd problem points
      seed nontrivial) input valid record jointPositive
  have bounded := reusedCheckedSection_nextInput_selectedBound E fieldTail sameWidth fits
    odd problem points seed nontrivial input valid record jointPositive
  exact ⟨current.1, current.2.1, bounded, current.2.2⟩


end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
