/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Reuse
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Probability
import all QuantumAlg.Primitives.ZReset.Bank.Scope.Semantics

/-!
# Conditional Born law after a paid reset of the same bank

The actual reset establishes its zero support internally for every incoming
store and arbitrary reference operator. Store-weighted reference observations
are preserved. Composing the actual subsequent member therefore gives the
same source outcome law on the current stored parameter, without an incoming
zero, purity or independence promise. The state equation keeps the actual
reset and sampling paths and the original history.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem scopedReset_seeded {ctx : RuntimeCtx .quantum}
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds ctx.quantumLayout.zeroLabel
      ((ZReset.BankScope.code qubits).execute Reference state) := by
  intro original left right leftRef rightRef
  have zero := ZReset.BankScope.zResetBankScope_complete_store_entry qubits state original
    ctx.quantumLayout.zeroLabel ctx.quantumLayout.zeroLabel leftRef rightRef
  simp only [and_self] at zero
  exact (ZReset.BankScope.zResetBankScope_complete_store_entry qubits state original
    left right leftRef rightRef).trans
      (congrArg (fun coefficient : ℂ =>
        if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
          coefficient else 0) zero.symm)

private theorem scopedReset_reference {ctx : RuntimeCtx .quantum}
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store ctx → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((ZReset.BankScope.code qubits).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) leftRef rightRef := by
  refine (BasisSeeded.referenceFiberSum_seed ctx.quantumLayout.zeroLabel _
    (scopedReset_seeded qubits state) weight leftRef rightRef).trans ?_
  refine Eq.trans ?_ (BasisSeeded.fiber_store_blocks state
    (fun original _ => weight original) leftRef rightRef).symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [← Finset.mul_sum]
  apply congrArg (fun coefficient : ℂ => weight original * coefficient)
  simpa only [and_self, if_true] using
    ZReset.BankScope.zResetBankScope_complete_store_entry qubits state original
      ctx.quantumLayout.zeroLabel ctx.quantumLayout.zeroLabel leftRef rightRef

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Actual reset supplies the seed on the same bank for arbitrary complete input states. -/
theorem nativeOracle_resetBank_seeded
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel
      ((resetBank base noQuantum N).execute Reference state) :=
  scopedReset_seeded _ state

/-- Every complete-store reference weight survives the actual reset and scratch scope. -/
theorem nativeOracle_resetBank_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : Store (context base noQuantum N) → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((resetBank base noQuantum N).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) leftRef rightRef :=
  scopedReset_reference _ state weight leftRef rightRef

/-- The existing interpreter retains the complete actual reset and member paths in order. -/
theorem nativeOracle_reuse_execute (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    (reuse base noQuantum N input parameter).execute Reference state =
      ((body base noQuantum N input parameter).execute Reference
        ((resetBank base noQuantum N).execute Reference state)).mapHistory
          (fun history => (history.1.1, (history.1.2, history.2))) :=
  Circuit.execute_seq (resetBank base noQuantum N) (body base noQuantum N input parameter) state

/-- The reused actual output has the source Born law on its real current parameter and Ref. -/
theorem nativeOracle_reuse_outcome_reference (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (outcome : Fin (measurementBits N) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N input parameter).execute Reference state)
      (fun entry _ => if entry.1.read (.storage (resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ =>
          ((selectedOutcomePMF (entry.1.read (liftInput base noQuantum N parameter))
            outcome).toReal : ℂ)) leftRef rightRef := by
  let reset := (resetBank base noQuantum N).execute Reference state
  let weight := fun store : Store (context base noQuantum N) =>
    ((selectedOutcomePMF (store.read (liftInput base noQuantum N parameter)) outcome).toReal : ℂ)
  have first := Circuit.referenceFiberSum_execute_seq (resetBank base noQuantum N)
    (body base noQuantum N input parameter) state
    (fun store => if store.read (.storage (resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits outcome then 1 else 0) leftRef rightRef
  have born := nativeOracle_body_outcome_reference base noQuantum N input parameter reset
    (nativeOracle_resetBank_seeded base noQuantum N state) outcome leftRef rightRef
  have fibers := BasisSeeded.referenceFiberSum_seed _ reset
    (nativeOracle_resetBank_seeded base noQuantum N state) weight leftRef rightRef
  exact first.trans (born.trans (fibers.symm.trans
    (nativeOracle_resetBank_reference base noQuantum N state weight leftRef rightRef)))

/-- The actual reused run's PMF is the trace of those same current-input reference weights. -/
theorem nativeOracle_reuse_outputDistribution (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) {Reference : Register}
    (original : Execution.Input (context base noQuantum N) Reference)
    (outcome : Fin (measurementBits N) → Bool) :
    (reuseRun base noQuantum N input parameter).outputDistribution original (.bits outcome) =
      ENNReal.ofReal (∑ reference : Reference.Index,
        ExecutionState.referenceFiberSum original.state
          (fun store _ =>
            ((selectedOutcomePMF (store.read (liftInput base noQuantum N parameter))
              outcome).toReal : ℂ)) reference reference).re := by
  let actual := reuseRun base noQuantum N input parameter
  let read := fun record : actual.Record => actual.result record
  have mapped := congrArg (fun probability : PMF (CShape.Value (.bits (measurementBits N))) =>
    probability (.bits outcome)) (ExecutionState.toPMF_mapClassical
      (actual.execute Reference original.state) (actual.execute_normalized original) read).symm
  refine mapped.trans ?_
  rw [ExecutionState.toPMF_apply, ExecutionState.mapClassical_block_mass_referenceFiberSum]
  apply congrArg ENNReal.ofReal
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro reference _
  exact (nativeOracle_reuse_outcome_reference base noQuantum N input parameter
    (original.state.mapClassical (fun store => (store, store))) outcome reference reference).trans
      (ExecutionState.referenceFiberSum_mapClassical original.state
        (fun store => (store, store)) _ reference reference)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
