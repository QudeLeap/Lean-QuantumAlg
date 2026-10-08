/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Selection
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# First accepted ECC word on the actual input-history fibers

The public section result is related to its own original Store, even when
different positive input blocks carry different accepted words. We partition
the actual effect by the original acceptance bit and selected word, retain
each complete density block, and use the existing first-selection law only
on the accepted fibers. No concrete group element or bit table is enumerated.
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

/-- The two existing latches used by the independent section relation. -/
def checkedSectionLatches (store : Store (sectionCtx E problem)) :
    Bool × (CShape.unsignedWord (orderWidth problem)).Value :=
  ((store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool,
    store.read (.storage (persistentSelected _ _ _).toCStorageRef))

private theorem selected_positive {C D : Type} [Fintype C] [DecidableEq D]
    {R : Register} (state : ExecutionState C R) (read : C → D) (label : D)
    (entry : C) (positive : 0 < ((state.selectClassical read label).block entry).mass) :
    read entry = label ∧ 0 < (state.block entry).mass := by
  by_cases selected : read entry = label
  · exact ⟨selected, by simpa only [ExecutionState.selectClassical_block,
      selected, if_true] using positive⟩
  · simp [ExecutionState.selectClassical_block, selected] at positive

private theorem indicator_zero_of_support {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (bad : C → Prop) [DecidablePred bad]
    (excluded : ∀ entry, 0 < (state.block entry).mass → ¬ bad entry) :
    state.effectWeight (fun entry => if bad entry then Effect.one R else Effect.zero R) = 0 := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_eq_zero
  intro entry _
  by_cases positive : 0 < (state.block entry).mass
  · simp only [excluded entry positive, if_false, Effect.weight_zero]
  · have zeroMass : (state.block entry).mass = 0 :=
      le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    rw [state.block_eq_zero_of_mass_eq_zero entry zeroMass]
    by_cases active : bad entry
    · simp only [active, if_true, Effect.weight_one, DensityOperator.zero_mass]
    · simp only [active, if_false, Effect.weight_zero]

omit [Fact p.Prime] in
/-- The real section execution assigns zero weight to records that overwrite
the word accepted in their own original input Store. This holds for arbitrary
input mixtures and external reference correlations. -/
theorem checkedSection_retentionViolation_effectWeight_zero
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (retains : RetainsFirst E problem code)
    {Reference : Register}
    (input : ExecutionState
      (Store (sectionCtx E problem) × ClassicalOracleModel.empty.HiddenState)
      ((sectionCtx E problem).register.prod Reference)) :
    let entered : State (sectionCtx E problem) Reference
        (ClassicalOracleModel.empty.HiddenState × Store (sectionCtx E problem)) :=
      input.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
    (code.execute Reference entered).effectWeight
      (fun record => if (checkedSectionLatches E problem record.2.2.1).1 = true ∧
          (checkedSectionLatches E problem record.1).2 ≠
            (checkedSectionLatches E problem record.2.2.1).2 then
          Effect.one ((sectionCtx E problem).register.prod Reference)
        else Effect.zero ((sectionCtx E problem).register.prod Reference)) = 0 := by
  classical
  dsimp only
  let entered : State (sectionCtx E problem) Reference
      (ClassicalOracleModel.empty.HiddenState × Store (sectionCtx E problem)) :=
    input.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  let read : Store (sectionCtx E problem) ×
      (ClassicalOracleModel.empty.HiddenState × Store (sectionCtx E problem)) →
      Bool × (CShape.unsignedWord (orderWidth problem)).Value :=
    fun entry => checkedSectionLatches E problem entry.2.2
  let bad : Store (sectionCtx E problem) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (Store (sectionCtx E problem) × code.Path)) → Prop :=
    fun record => (checkedSectionLatches E problem record.2.2.1).1 = true ∧
      (checkedSectionLatches E problem record.1).2 ≠
        (checkedSectionLatches E problem record.2.2.1).2
  change (code.execute Reference entered).effectWeight
    (fun record => if bad record then Effect.one _ else Effect.zero _) = 0
  rw [Circuit.effectWeight_execute_partition code entered read]
  apply Finset.sum_eq_zero
  rintro ⟨flag, wanted⟩ _
  let fiber := entered.selectClassical read (flag, wanted)
  have fiberHistory : ∀ entry, 0 < (fiber.block entry).mass →
      checkedSectionLatches E problem entry.2.2 = (flag, wanted) := by
    intro entry positive
    exact (selected_positive entered read (flag, wanted) entry positive).1
  have fiberStore : ∀ entry, 0 < (fiber.block entry).mass →
      checkedSectionLatches E problem entry.1 = (flag, wanted) := by
    intro entry positive
    have present := (selected_positive entered read (flag, wanted) entry positive).2
    obtain ⟨original, same, _⟩ :=
      (ExecutionState.mapClassical_block_mass_pos_iff input
        (fun source => (source.1, (source.2, source.1))) entry).mp present
    have storeEq : entry.1 = entry.2.2 :=
      (congrArg Prod.fst same).symm.trans
        (congrArg (fun record => record.2.2) same)
    rw [storeEq]
    exact fiberHistory entry positive
  apply indicator_zero_of_support
  intro result positive
  have originalLabel : checkedSectionLatches E problem result.2.2.1 =
      (flag, wanted) :=
    history_supported code Reference fiber (checkedSectionLatches E problem)
      (flag, wanted) fiberHistory result positive
  intro violation
  by_cases accepted : flag = true
  · have firstInput : ∀ entry, 0 < (fiber.block entry).mass →
        selectedFirstStored E problem wanted entry.1 := by
      intro entry present
      have latches := fiberStore entry present
      unfold checkedSectionLatches at latches
      unfold selectedFirstStored
      rw [accepted] at latches
      exact ⟨congrArg Prod.fst latches, congrArg Prod.snd latches⟩
    have kept := retains wanted fiber firstInput result positive
    have resultWord : (checkedSectionLatches E problem result.1).2 = wanted := kept.2
    have originalWord : (checkedSectionLatches E problem result.2.2.1).2 =
        wanted := congrArg Prod.snd originalLabel
    exact violation.2 (resultWord.trans originalWord.symm)
  · have originalFlag : (checkedSectionLatches E problem result.2.2.1).1 =
        flag := congrArg Prod.fst originalLabel
    exact accepted (originalFlag.symm.trans violation.1)

omit [Fact p.Prime] in
/-- Each supported record of the normalized actual run retains its own
originally accepted word. This converts the zero physical violation weight
into the relation required by the public problem's input/output pair. -/
theorem checkedSection_retainsOriginal_on_support
    {shape : CShape}
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem) shape)
    (retains : RetainsFirst E problem run.code)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (record : run.Record) (supported : record ∈ (run.executionDistribution input).support)
    (accepted : (checkedSectionLatches E problem record.2.2.1).1 = true) :
    (checkedSectionLatches E problem record.1).2 =
      (checkedSectionLatches E problem record.2.2.1).2 := by
  classical
  let bad : run.Record → Prop := fun result =>
    (checkedSectionLatches E problem result.2.2.1).1 = true ∧
      (checkedSectionLatches E problem result.1).2 ≠
        (checkedSectionLatches E problem result.2.2.1).2
  let read : run.Record → Bool := fun result => decide (bad result)
  have zeroWeight := checkedSection_retentionViolation_effectWeight_zero E problem
    run.code retains input.state
  have sameExecution : run.execute Reference input.state =
      run.code.execute Reference
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))) := by
    unfold AlgorithmRun.execute
    exact congrArg (run.code.execute Reference)
      (ExecutionState.executionState_mapClassical_congr_decision input.state
        (fun value => (value.1, (value.2, value.1)))
        (fun entry => (entry.1, (entry.2, entry.1))) (by intro; rfl) _ _)
  have zeroProbability : (run.executionDistribution input).map read true = 0 := by
    rw [run.executionDistribution_map_eq_effectWeight input read true]
    rw [sameExecution]
    simpa only [read, bad, decide_eq_true_eq,
      ENNReal.ofReal_zero] using congrArg ENNReal.ofReal zeroWeight
  by_contra different
  have violation : bad record := ⟨accepted, different⟩
  have mapped : true ∈ ((run.executionDistribution input).map read).support :=
    (PMF.mem_support_map_iff read (run.executionDistribution input) true).mpr
      ⟨record, supported, by simp only [read, decide_eq_true_eq]; exact violation⟩
  exact ((PMF.mem_support_iff _ _).mp mapped) zeroProbability

/-- The named first reset/readout/check/reset section retains each input's
own previously accepted scalar, including mixed inputs with distinct words. -/
theorem firstCheckedSection_retentionViolation_effectWeight_zero
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) {shape : CShape}
    (read : OutputRead (sectionCtx E problem) shape) {Reference : Register}
    (input : ExecutionState
      (Store (sectionCtx E problem) × ClassicalOracleModel.empty.HiddenState)
      ((sectionCtx E problem).register.prod Reference)) :
    let code := (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial read).code
    let entered : State (sectionCtx E problem) Reference
        (ClassicalOracleModel.empty.HiddenState × Store (sectionCtx E problem)) :=
      input.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
    (code.execute Reference entered).effectWeight
      (fun record => if (checkedSectionLatches E problem record.2.2.1).1 = true ∧
          (checkedSectionLatches E problem record.1).2 ≠
            (checkedSectionLatches E problem record.2.2.1).2 then
          Effect.one ((sectionCtx E problem).register.prod Reference)
        else Effect.zero ((sectionCtx E problem).register.prod Reference)) = 0 := by
  dsimp only
  exact checkedSection_retentionViolation_effectWeight_zero E problem _
    (firstCheckedSection_retainsFirst E fieldTail sameWidth fits odd problem points seed
      nontrivial read) input

/-- The named reused readout/check/reset section obeys the same original
input-to-output retention relation on its actual execution records. -/
theorem reusedCheckedSection_retentionViolation_effectWeight_zero
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) {shape : CShape}
    (read : OutputRead (sectionCtx E problem) shape) {Reference : Register}
    (input : ExecutionState
      (Store (sectionCtx E problem) × ClassicalOracleModel.empty.HiddenState)
      ((sectionCtx E problem).register.prod Reference)) :
    let code := (reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial read).code
    let entered : State (sectionCtx E problem) Reference
        (ClassicalOracleModel.empty.HiddenState × Store (sectionCtx E problem)) :=
      input.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
    (code.execute Reference entered).effectWeight
      (fun record => if (checkedSectionLatches E problem record.2.2.1).1 = true ∧
          (checkedSectionLatches E problem record.1).2 ≠
            (checkedSectionLatches E problem record.2.2.1).2 then
          Effect.one ((sectionCtx E problem).register.prod Reference)
        else Effect.zero ((sectionCtx E problem).register.prod Reference)) = 0 := by
  dsimp only
  exact checkedSection_retentionViolation_effectWeight_zero E problem _
    (reusedCheckedSection_retainsFirst E fieldTail sameWidth fits odd problem points seed
      nontrivial read) input

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
