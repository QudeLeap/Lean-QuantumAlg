/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Retention
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Validity
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Spec
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Actual accepted-flag meaning of a complete checked ECC section

The independent output relation is evaluated on the real selected bit and
word of the same execution record. Its input-dependent retention clause is
supplied by the original-Store support theorem, while boundedness and the
public group equation follow from admitted input validity through the
unchanged circuit. No acceptance event is replaced by a separate model.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (problem : KnownOrderProblem E.GroupPoint)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

private theorem entered_validity_and_bound {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (entry : Store (sectionCtx E problem) ×
      (ClassicalOracleModel.empty.HiddenState × Store (sectionCtx E problem)))
    (positive : 0 < ((input.state.mapClassical
      (fun source => (source.1, (source.2, source.1)))).block entry).mass) :
    CheckedSelectionValid E problem entry.1 ∧
      SelectedWithinOrder E problem entry.1 := by
  obtain ⟨source, same, sourcePositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff input.state
      (fun original => (original.1, (original.2, original.1))) entry).mp positive
  have sourceStore : source.1 = entry.1 := congrArg Prod.fst same
  have callerPositive := input.caller_local_mass_pos_of_joint source sourcePositive
  have admitted := valid source.1 callerPositive
  rw [← sourceStore]
  exact ⟨⟨admitted.1, admitted.2.1, admitted.2.2.2⟩,
    admitted.2.2.1⟩

/-- On every supported record of the actual checked run, the independent
input/output relation agrees exactly with the stored final acceptance bit. -/
theorem checkedSection_accepts_iff_finalAccepted
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
    (record : run.Record) (supported : record ∈ (run.executionDistribution input).support) :
    checkedSectionAccepts E problem record.2.2.1 (run.result record) ↔
      (checkedSectionLatches E problem record.1).1 = true := by
  have positive : 0 < ((run.execute Reference input.state).block record).mass :=
    (ExecutionState.mem_support_toPMF_iff _ _ _).mp supported
  let entered : State (sectionCtx E problem) Reference
      (ClassicalOracleModel.empty.HiddenState × Store (sectionCtx E problem)) :=
    input.state.mapClassical (fun source => (source.1, (source.2, source.1)))
  have sameExecution : run.execute Reference input.state =
      run.code.execute Reference entered := by
    unfold AlgorithmRun.execute
    exact congrArg (run.code.execute Reference)
      (ExecutionState.executionState_mapClassical_congr_decision input.state
        (fun value => (value.1, (value.2, value.1)))
        (fun source => (source.1, (source.2, source.1))) (by intro; rfl) _ _)
  rw [sameExecution] at positive
  have enteredDomain : ∀ entry, 0 < (entered.block entry).mass →
      CheckedSelectionValid E problem entry.1 ∧
        SelectedWithinOrder E problem entry.1 :=
    fun entry present => entered_validity_and_bound E problem input valid entry present
  have finalValid : CheckedSelectionValid E problem record.1 :=
    retainsValidity entered (fun entry present => (enteredDomain entry present).1)
      record positive
  have finalBound : SelectedWithinOrder E problem record.1 :=
    retainsBound entered (fun entry present => (enteredDomain entry present).2)
      record positive
  have resultEq : run.result record = .product
      (record.1.read (.storage (persistentAccepted _ _ _).toCStorageRef))
      (record.1.read (.storage (persistentSelected _ _ _).toCStorageRef)) := by
    unfold AlgorithmRun.result
    rw [readout]
    rfl
  rw [resultEq]
  change ((checkedSectionLatches E problem record.1).1 = true ∧
      (checkedSectionLatches E problem record.1).2.toNat < problem.order ∧
      (checkedSectionLatches E problem record.1).2.toNat •
        problem.generator.toMathlib = problem.target.toMathlib ∧
      ((checkedSectionLatches E problem record.2.2.1).1 = true →
        (checkedSectionLatches E problem record.1).2 =
          (checkedSectionLatches E problem record.2.2.1).2)) ↔
    (checkedSectionLatches E problem record.1).1 = true
  constructor
  · intro accepted
    exact accepted.1
  · intro accepted
    exact ⟨accepted, finalBound, finalValid.2.2 accepted,
      fun originalAccepted => checkedSection_retainsOriginal_on_support
        E problem run retainsFirst input record supported originalAccepted⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
