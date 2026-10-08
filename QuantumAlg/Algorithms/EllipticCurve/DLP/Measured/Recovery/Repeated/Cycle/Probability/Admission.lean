/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Admission

/-!
# Admitted public points in an actual checked ECC attempt

The independent persistent input invariant preserves the two borrowed public
point interpretations through physical sampling. Together with the source-
scoped secret witness, this discharges the actual checked-attempt failure bound
without an extra sampled-point or secret premise at the protocol boundary.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- Every sampled block of the real checked attempt retains the admitted
public generator and target interpretations. -/
theorem sampledPublicPoints_of_validity
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (valid : ∀ entry, 0 < (state.block entry).mass →
      CheckedSelectionValid E problem entry.1) :
    SampledPublicPoints E fieldTail sameWidth fits odd problem points seed state := by
  intro entry positive
  have noQuantum :
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  exact PublicInput.persistentProgram_preserves_represents E (orderWidth problem)
    problem (persistentSamplingRound E fieldTail sameWidth fits odd problem points seed)
    noQuantum state
    (fun previous present => ⟨(valid previous present).1, (valid previous present).2.1⟩)
    entry positive

/-- One actual checked attempt contracts unaccepted mass from the independent
point and selected-scalar domain, with no separately supplied secret or
post-sampling point premise. -/
theorem persistentCheckedAttempt_failureWeight_of_validity
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (valid : ∀ entry, 0 < (state.block entry).mass →
      CheckedSelectionValid E problem entry.1) :
    CheckedFailureContracts E fieldTail sameWidth fits odd problem points seed nontrivial
      state :=
  persistentCheckedAttempt_failureWeight_from_knownOrder E fieldTail sameWidth fits odd
    problem points seed nontrivial addends state
    (sampledPublicPoints_of_validity E fieldTail sameWidth fits odd problem points seed
      state valid)

/-- The independent local input domain also holds on every supported joint
store, service and unit-history block of the actual entered state. -/
theorem checkedSection_entered_validity
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (entry : Store
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) × (Unit × Unit))
    (positive : 0 < ((State.skip input.state).block entry).mass) :
    CheckedSelectionValid E problem entry.1 := by
  rcases entry with ⟨store, hidden, history⟩
  cases history
  have sourcePositive : 0 < (input.state.block (store, hidden)).mass :=
    (State.skip_block_mass_pos_iff input.state store hidden).mp positive
  have callerPositive := input.caller_local_mass_pos_of_joint
    (store, hidden) sourcePositive
  obtain ⟨base, target, _bound, sound⟩ := valid store callerPositive
  exact ⟨base, target, sound⟩

/-- A caller admitted by the independently specified checked-section domain
has the source-derived one-attempt contraction on its actual entered state. -/
theorem persistentCheckedAttempt_failureWeight_on_admittedInput
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState) :
    CheckedFailureContracts E fieldTail sameWidth fits odd problem points seed nontrivial
      (State.skip input.state) := by
  apply persistentCheckedAttempt_failureWeight_of_validity E fieldTail sameWidth fits odd
    problem points seed nontrivial addends (State.skip input.state)
  intro entry positive
  exact checkedSection_entered_validity E problem input valid entry positive

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
