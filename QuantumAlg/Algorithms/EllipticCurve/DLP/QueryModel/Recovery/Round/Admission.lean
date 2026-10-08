/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Restart
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Support
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Loop
import all QuantumAlg.Core.Execution.CycleSchedule.InputDistribution

/-!
# Admission supplied by actual complete ECDLP rounds

The independent domain retains the original public points, a bounded selected
word and the soundness of an already accepted word. It admits arbitrary live
scratch values, quantum states and external references. The real predecessor,
including its complete checked feedback, supplies that same domain after only
mathematical path histories are forgotten.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local instance] Classical.decEq Classical.propDecidable
attribute [local irreducible] underPersistent

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Project the unchanged original point cells from the live bank and seven retained cells. -/
public def roundOriginalStore (I : ECDLPInstance E) (store : Store (context I)) :
    Store (Sampling.pre I) := samplingOriginal I (persistentOriginal I store)

private def selectionRead {kind : ProblemKind} (ctx : RuntimeCtx kind) (width scalar : Nat)
    (store : Store (persistentCtx ctx width scalar)) :
    Bool × (CShape.unsignedWord scalar).Value :=
  ((store.read (.storage (persistentAccepted ctx width scalar).toCStorageRef)).toBool,
    store.read (.storage (persistentSelected ctx width scalar).toCStorageRef))

/-- Read the two actual retained selection cells without an unrelated execution-model parameter. -/
public def roundSelectedPair (I : ECDLPInstance E) (store : Store (context I)) :
    Bool × (CShape.unsignedWord (scalarWidth I)).Value :=
  selectionRead (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I) store

/-- Independent admission of original public points and a sound, bounded persistent selection. -/
public def roundStoreDomain (I : ECDLPInstance E) (store : Store (context I)) : Prop := by
  letI : Fact p.Prime := ⟨E.prime⟩
  exact roundOriginalStore I store = Runtime.Context.inputStore I ∧
    (roundSelectedPair I store).2.toNat < I.subgroupOrder ∧
      ((roundSelectedPair I store).1 = true →
        (roundSelectedPair I store).2.toNat • I.basePoint.toMathlib = I.targetPoint.toMathlib)

/-- The domain quantifies every positive local joint block, retaining correlated service state. -/
public def roundInputDomain (I : ECDLPInstance E) (A : Access I)
    (state : ExecutionState (Store (context I) × (Sampling.executionModel I A).HiddenState)
      (context I).register) : Prop :=
  ∀ record, 0 < (state.block record).mass → roundStoreDomain I record.1

private theorem original_borrowed (I : ECDLPInstance E) (store : Store (context I)) :
    HEq store.readBorrowedClassical (roundOriginalStore I store).readBorrowedClassical :=
  (persistentTail_borrowed (fieldWidth E) (scalarWidth I) store).trans
    (samplingOriginal_borrowed I (persistentOriginal I store))

private theorem original_borrowed_injective (I : ECDLPInstance E)
    (left right : Store (Sampling.pre I))
    (same : left.readBorrowedClassical = right.readBorrowedClassical) : left = right := by
  obtain ⟨⟨leftTarget, leftBase, leftUnit⟩⟩ := left
  obtain ⟨⟨rightTarget, rightBase, rightUnit⟩⟩ := right
  cases leftUnit
  cases rightUnit
  change CShape.Value.product leftTarget (.product leftBase .unit) =
    CShape.Value.product rightTarget (.product rightBase .unit) at same
  cases same
  rfl

private theorem original_read (I : ECDLPInstance E) (store : Store (context I))
    {shape : CShape} (input : CInputRef (Sampling.pre I) shape) :
    (roundOriginalStore I store).read input =
      store.read (persistentInput (fieldWidth E) (scalarWidth I) (originalInput I input)) :=
  (samplingOriginal_read I (persistentOriginal I store) input).trans
    (persistentOriginal_read I store (originalInput I input))

private theorem original_preserved (I : ECDLPInstance E) (A : Access I)
    (prefixCode : Circuit (Sampling.executionModel I A) (context I) (context I))
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (context I) Reference ((Sampling.executionModel I A).HiddenState × History))
    (admitted : ∀ record, 0 < (initial.block record).mass →
      roundOriginalStore I record.1 = Runtime.Context.inputStore I)
    (result : Store (context I) ×
      ((Sampling.executionModel I A).HiddenState × (History × prefixCode.Path)))
    (positive : 0 < ((prefixCode.execute Reference initial).block result).mass) :
    roundOriginalStore I result.1 = Runtime.Context.inputStore I := by
  have noBorrowed : (context I).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires (Sampling.Reuse.context I) (fieldWidth E)
      (scalarWidth I)).trans (Sampling.Reuse.ecdlpReuse_noBorrowedQuantum I)
  have restored := prefixCode.borrowedRestored_of_noBorrowedQuantum noBorrowed Reference initial
  obtain ⟨previous, present, same⟩ := prefixCode.borrowedRestored_supported_initial
    Reference initial _ restored result positive
  have beforeAfter : HEq previous.1.readBorrowedClassical result.1.readBorrowedClassical :=
    (heq_of_eq same).trans (borrowed_transport_heq prefixCode result.1.readBorrowedClassical)
  have originals : (roundOriginalStore I previous.1).readBorrowedClassical =
      (roundOriginalStore I result.1).readBorrowedClassical :=
    eq_of_heq ((original_borrowed I previous.1).symm.trans
      (beforeAfter.trans (original_borrowed I result.1)))
  exact (original_borrowed_injective I _ _ originals).symm.trans (admitted previous present)

/-- Original point interpretations hold on any actual prefix from the admitted live context. -/
theorem ecdlpRecovery_round_prefix_represents (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (context I) Reference ((Sampling.executionModel I A).HiddenState × History))
    (admitted : ∀ record, 0 < (initial.block record).mass →
      roundOriginalStore I record.1 = Runtime.Context.inputStore I)
    (prefixCode : Circuit (Sampling.executionModel I A) (context I) (context I))
    (result : Store (context I) ×
      ((Sampling.executionModel I A).HiddenState × (History × prefixCode.Path)))
    (positive : 0 < ((prefixCode.execute Reference initial).block result).mass) :
    ClassicalRoutines.EllipticCurve.PointRepresents (curve E)
        (result.1.read (persistentInput (fieldWidth E) (scalarWidth I) (baseInput I)))
        I.basePoint.toMathlib ∧
      ClassicalRoutines.EllipticCurve.PointRepresents (curve E)
        (result.1.read (persistentInput (fieldWidth E) (scalarWidth I) (targetInput I)))
        I.targetPoint.toMathlib := by
  have same := original_preserved I A prefixCode initial admitted result positive
  have base := original_read I result.1 (Runtime.Context.baseRef I)
  have target := original_read I result.1 (Runtime.Context.targetRef I)
  rw [same, Runtime.Context.inputStore_base] at base
  rw [same, Runtime.Context.inputStore_target] at target
  change Runtime.Context.baseValue I = result.1.read
    (persistentInput (fieldWidth E) (scalarWidth I) (baseInput I)) at base
  change Runtime.Context.targetValue I = result.1.read
    (persistentInput (fieldWidth E) (scalarWidth I) (targetInput I)) at target
  constructor
  · exact base ▸ ClassicalRoutines.EllipticCurve.encodePoint_represents
      (curve E) I.basePoint.toMathlib
  · exact target ▸ ClassicalRoutines.EllipticCurve.encodePoint_represents
      (curve E) I.targetPoint.toMathlib

variable [Fact p.Prime]

/-- The same actual complete round preserves the independently admitted point and latch domain. -/
theorem ecdlpRecovery_round_preserves_domain (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (context I) Reference ((Sampling.executionModel I A).HiddenState × History))
    (admitted : ∀ record, 0 < (state.block record).mass → roundStoreDomain I record.1)
    (result : Store (context I) ×
      ((Sampling.executionModel I A).HiddenState ×
        (History × (round I A expansion nontrivial).Path)))
    (positive : 0 < (((round I A expansion nontrivial).execute
      Reference state).block result).mass) :
    roundStoreDomain I result.1 := by
  have original := original_preserved I A (round I A expansion nontrivial) state
    (fun record present => (admitted record present).1) result positive
  have bounded := sampledAttempt_preserves_selected_lt (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) state
    (fun record present => (admitted record present).2.1) result positive
  have points := ecdlpRecovery_round_prefix_represents I A state
    (fun record present => (admitted record present).1)
  have initialValid : ∀ record, 0 < (state.block record).mass →
      ClassicalRoutines.EllipticCurve.PointRepresents (curve E)
        (record.1.read (persistentInput (fieldWidth E) (scalarWidth I) (baseInput I)))
        I.basePoint.toMathlib ∧
      ClassicalRoutines.EllipticCurve.PointRepresents (curve E)
        (record.1.read (persistentInput (fieldWidth E) (scalarWidth I) (targetInput I)))
        I.targetPoint.toMathlib ∧
      ((roundSelectedPair I record.1).1 = true →
        (roundSelectedPair I record.1).2.toNat • I.basePoint.toMathlib =
          I.targetPoint.toMathlib) := by
    intro record present
    have prior := admitted record present
    have base := original_read I record.1 (Runtime.Context.baseRef I)
    have target := original_read I record.1 (Runtime.Context.targetRef I)
    rw [prior.1, Runtime.Context.inputStore_base] at base
    rw [prior.1, Runtime.Context.inputStore_target] at target
    change Runtime.Context.baseValue I = record.1.read
      (persistentInput (fieldWidth E) (scalarWidth I) (baseInput I)) at base
    change Runtime.Context.targetValue I = record.1.read
      (persistentInput (fieldWidth E) (scalarWidth I) (targetInput I)) at target
    exact ⟨base ▸ ClassicalRoutines.EllipticCurve.encodePoint_represents
        (curve E) I.basePoint.toMathlib,
      target ▸ ClassicalRoutines.EllipticCurve.encodePoint_represents
        (curve E) I.targetPoint.toMathlib, prior.2.2⟩
  have checked := sampledAttempt_preserves_validity (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    I.basePoint.toMathlib I.targetPoint.toMathlib state initialValid
    (points (underPersistent (Sampling.Reuse.code I A expansion)
      (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (fieldWidth E) (scalarWidth I)))
    result positive
  exact ⟨original, bounded, checked.2.2⟩

omit [Fact p.Prime] in
/-- The actual normalized predecessor, without service initialization, admits the next round. -/
public theorem ecdlpRecovery_round_nextInput_admitted (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles (context I) Reference)
    (admitted : roundInputDomain I A original.localState) :
    roundInputDomain I A ((round I A expansion nontrivial).nextInput original).localState := by
  let : Fact p.Prime := ⟨E.prime⟩
  intro record positive
  obtain ⟨result, storeEq, _serviceEq, present⟩ :=
    Circuit.nextInput_local_supported_execution (round I A expansion nontrivial)
      original record positive
  have initialDomain : ∀ previous, 0 < ((original.state.mapClassical
      (fun entry => (entry.1, (entry.2, ())))).block previous).mass →
        roundStoreDomain I previous.1 := by
    intro previous positive
    obtain ⟨source, same, sourcePositive⟩ :=
      (ExecutionState.mapClassical_block_mass_pos_iff original.state
        (fun entry => (entry.1, (entry.2, ()))) previous).mp positive
    have localPositive : 0 < (original.localState.block source).mass := by
      simpa only [OracleInput.oracleInput_localState_block,
        DensityOperator.marginalLeft_mass] using sourcePositive
    exact (congrArg Prod.fst same) ▸ admitted source localPositive
  have domain := ecdlpRecovery_round_preserves_domain I A expansion nontrivial
    (original.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))
    initialDomain result present
  exact storeEq ▸ domain

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
