/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Correctness
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Support
import all QuantumAlg.Core.Execution.CycleSchedule.InputDistribution
import all QuantumAlg.Core.Execution.CycleSchedule.InputDistribution.Sequence

/-!
# Original caller admission through the actual ECDLP allocation and first round

Original public-point stores are admitted by the existing caller domain.
Actual retention sets the first-success latches to false and zero. Full
borrowed restoration and supported original records prove the complete live
round domain. Real successor inputs retain their service correlations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem prefix_original (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (Sampling.pre I) Reference
      ((Sampling.executionModel I A).HiddenState × History))
    (admitted : ∀ entry, 0 < (initial.block entry).mass →
      entry.1 = Runtime.Context.inputStore I)
    (prefixCode : Circuit (Sampling.executionModel I A) (Sampling.pre I) (context I))
    (result : Store (context I) ×
      ((Sampling.executionModel I A).HiddenState × (History × prefixCode.Path)))
    (positive : 0 < ((prefixCode.execute Reference initial).block result).mass) :
    roundOriginalStore I result.1 = Runtime.Context.inputStore I := by
  have restored := prefixCode.borrowedRestored_of_noBorrowedQuantum (by rfl) Reference initial
  obtain ⟨previous, present, same⟩ := prefixCode.borrowedRestored_supported_initial
    Reference initial _ restored result positive
  rw [admitted previous present] at same
  have original := (heq_of_eq same).trans
    ((borrowed_transport_heq prefixCode result.1.readBorrowedClassical).trans
      (original_borrowed I result.1))
  exact inputStore_eq_of_borrowed I (roundOriginalStore I result.1) (eq_of_heq original.symm)

private theorem allocation_domain (I : ECDLPInstance E) (A : Access I)
    (nontrivial : 2 ≤ (problem I).order)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (Sampling.pre I) Reference
      ((Sampling.executionModel I A).HiddenState × History))
    (admitted : ∀ entry, 0 < (initial.block entry).mass →
      entry.1 = Runtime.Context.inputStore I)
    (result : Store (context I) ×
      ((Sampling.executionModel I A).HiddenState × (History × (allocationCode I A).Path)))
    (positive : 0 < (((allocationCode I A).execute Reference initial).block result).mass) :
    roundStoreDomain I result.1 := by
  let : Fact p.Prime := ⟨E.prime⟩
  have original := prefix_original I A initial admitted (allocationCode I A) result positive
  have selected := allocation_selected_initialized (Sampling.Reuse.initialCode I A)
    (curve E) (modulus I nontrivial) I.basePoint.toMathlib I.targetPoint.toMathlib
    initial result positive
  exact ⟨original, selected.1, selected.2⟩

/-- Actual one-time initialization admits every live joint input of the complete round. -/
public theorem ecdlpRecovery_allocation_nextInput_admitted (I : ECDLPInstance E) (A : Access I)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    roundInputDomain I A ((allocationCode I A).nextInput original).localState := by
  intro record positive
  obtain ⟨result, storeEq, _serviceEq, present⟩ :=
    Circuit.nextInput_local_supported_execution (allocationCode I A) original record positive
  have admitted : ∀ previous, 0 < ((original.state.mapClassical
      (fun entry => (entry.1, (entry.2, ())))).block previous).mass →
      previous.1 = Runtime.Context.inputStore I := by
    intro previous supported
    obtain ⟨source, same, sourcePositive⟩ :=
      (ExecutionState.mapClassical_block_mass_pos_iff original.state
        (fun entry => (entry.1, (entry.2, ()))) previous).mp supported
    exact (congrArg Prod.fst same).symm.trans
      (valid source.1 (original.caller_local_mass_pos_of_joint source sourcePositive))
  exact storeEq ▸ allocation_domain I A nontrivial
    (original.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))
    admitted result present

/-- The actual first complete cycle admits another round without initializing any service. -/
public theorem ecdlpRecovery_firstRound_nextInput_admitted (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    roundInputDomain I A ((firstRound I A expansion nontrivial).nextInput original).localState := by
  rw [firstRound, Circuit.nextInput_seq]
  exact ecdlpRecovery_round_nextInput_admitted I A expansion nontrivial
    ((allocationCode I A).nextInput original)
    (ecdlpRecovery_allocation_nextInput_admitted I A nontrivial original valid)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
