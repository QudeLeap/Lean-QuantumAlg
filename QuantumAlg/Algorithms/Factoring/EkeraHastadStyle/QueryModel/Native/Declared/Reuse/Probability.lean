/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Selected.Law
import all QuantumAlg.Primitives.ZReset.Bank.Scope.Observation
import all QuantumAlg.Primitives.ZReset.Bank.Scope.OperationModel
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# Conditional Born law after paid reuse of the declared EH bank

The actual scoped reset establishes the member's physical zero from every
incoming complete store-reference state and preserves that state's reference
weights. The next selected query, measurement and packing therefore obey the
same conditional source law on the current stored parameter.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- Actual paid reset establishes the same physical seed for every input block. -/
theorem reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History)) :
    BasisSeeded.Holds (Native.context base noQuantum N).quantumLayout.zeroLabel
      ((resetBank base noQuantum N input).execute Reference state) := by
  let qubits := Native.nativeOracle_context_qubits N
    (Native.nativeOracle_context_wires base noQuantum N)
  have previous := ZReset.BankScope.seeded
    (oracles := ShortDLP.declaredModel (Native.encoding input)) qubits state
  have erasedPrevious := BasisSeeded.mapHistory
    (Native.context base noQuantum N).quantumLayout.zeroLabel
    ((ZReset.BankScope.code
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      qubits).execute Reference state) previous
    (fun record => (record.1, record.2.1))
  have erasedActual : BasisSeeded.Holds
      (Native.context base noQuantum N).quantumLayout.zeroLabel
      (((resetBank base noQuantum N input).execute Reference state).mapHistory
        (fun record => (record.1, record.2.1))) := by
    rw [resetBank, ZReset.BankScope.code_execute_operationModel]
    exact erasedPrevious
  exact BasisSeeded.of_mapHistory _ _ _ erasedActual

/-- The scratch-scoped reset preserves every store-weighted reference entry. -/
theorem reset_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : Store (Native.context base noQuantum N) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((resetBank base noQuantum N input).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight entry.1) leftRef rightRef := by
  let qubits := Native.nativeOracle_context_qubits N
    (Native.nativeOracle_context_wires base noQuantum N)
  exact (ZReset.BankScope.referenceFiberSum_operationModel
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    qubits BitWord.model state weight leftRef rightRef).trans
    (ZReset.BankScope.referenceFiberSum_preserved
      (oracles := ShortDLP.declaredModel (Native.encoding input))
      qubits state weight leftRef rightRef)

/-- The paid bank reset and next actual observation retain any stable old
classical weight jointly with the conditional source Born law. -/
theorem reuse_outcome_weighted_reference
    (parameter : CInputRef base (ParameterShape N))
    (readWeight : Store (Native.context base noQuantum N) → ℂ)
    (readWeight_stable : ∀ store basis,
      readWeight ((measuredStore base noQuantum N input store basis).applyOp
        (packing base noQuantum N)) = readWeight store)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N input parameter).execute Reference state)
      (fun entry _ => readWeight entry.1 * (if entry.1.read
        (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => readWeight entry.1 * sourceWeight N input
          (entry.1.read (Native.liftInput base noQuantum N parameter)) outcome)
        leftRef rightRef := by
  let reset := (resetBank base noQuantum N input).execute Reference state
  let weight := fun store : Store (Native.context base noQuantum N) =>
    readWeight store * sourceWeight N input
      (store.read (Native.liftInput base noQuantum N parameter)) outcome
  have first := Circuit.referenceFiberSum_execute_seq
    (resetBank base noQuantum N input)
    (body base noQuantum N input parameter) state
    (fun store => readWeight store * (if store.read
      (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits outcome then 1 else 0)) leftRef rightRef
  have born := body_outcome_weighted_reference base noQuantum N input parameter
    readWeight readWeight_stable reset (reset_seeded base noQuantum N input state)
    outcome leftRef rightRef
  have fibers := BasisSeeded.referenceFiberSum_seed _ reset
    (reset_seeded base noQuantum N input state) weight leftRef rightRef
  exact first.trans (born.trans (fibers.symm.trans
    (reset_reference base noQuantum N input state weight leftRef rightRef)))

/-- A subsequent paid sample has the same source Born law on its current
stored parameter, arbitrary reference and persistent hidden state. -/
theorem reuse_outcome_reference (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N input parameter).execute Reference state)
      (fun entry _ => if entry.1.read
        (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => sourceWeight N input
          (entry.1.read (Native.liftInput base noQuantum N parameter)) outcome)
        leftRef rightRef := by
  simpa only [one_mul] using
    (reuse_outcome_weighted_reference base noQuantum N input parameter
      (fun _ => (1 : ℂ)) (by intro _ _; rfl) state outcome leftRef rightRef)

/-- Store observations agreeing after the next actual measurement and pack
also agree after the paid reset and the complete reused body. -/
theorem reuse_reference_congr (parameter : CInputRef base (ParameterShape N))
    (left right : Store (Native.context base noQuantum N) → ℂ)
    (agree : ∀ store basis,
      left ((measuredStore base noQuantum N input store basis).applyOp
        (packing base noQuantum N)) =
      right ((measuredStore base noQuantum N input store basis).applyOp
        (packing base noQuantum N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N input parameter).execute Reference state)
      (fun entry _ => left entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N input parameter).execute Reference state)
      (fun entry _ => right entry.1) leftRef rightRef := by
  let reset := (resetBank base noQuantum N input).execute Reference state
  have leftSeq := Circuit.referenceFiberSum_execute_seq
    (resetBank base noQuantum N input) (body base noQuantum N input parameter)
    state left leftRef rightRef
  have rightSeq := Circuit.referenceFiberSum_execute_seq
    (resetBank base noQuantum N input) (body base noQuantum N input parameter)
    state right leftRef rightRef
  exact leftSeq.trans ((body_reference_congr base noQuantum N input parameter
    left right agree reset leftRef rightRef).trans rightSeq.symm)

/-- The reused sample also has the original selected mathematical law. -/
theorem reuse_outcome_reference_selected
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N input parameter).execute Reference state)
      (fun entry _ => if entry.1.read
        (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ =>
          ((selectedOutcomePMF
            (entry.1.read (Native.liftInput base noQuantum N parameter))
            outcome).toReal : ℂ)) leftRef rightRef := by
  simpa only [sourceWeight_eq_selected] using
    reuse_outcome_reference base noQuantum N input parameter state
      outcome leftRef rightRef

/-- The actual reused run reads that same selected law from its overwritten
packed result cell for arbitrary correlated current input. -/
theorem reuse_outputDistribution (parameter : CInputRef base (ParameterShape N))
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles
      (Native.context base noQuantum N) Reference)
    (outcome : Fin (measurementBits N) → Bool) :
    (reuseRun base noQuantum N input parameter).outputDistribution
      original (.bits outcome) =
      ENNReal.ofReal (∑ reference : Reference.Index,
        ExecutionState.referenceFiberSum original.state
          (fun entry _ =>
            ((selectedOutcomePMF
              (entry.1.read (Native.liftInput base noQuantum N parameter))
              outcome).toReal : ℂ)) reference reference).re := by
  let actual := reuseRun base noQuantum N input parameter
  let read := fun record : actual.Record => actual.result record
  have mapped := congrArg
    (fun probability : PMF (CShape.Value (.bits (measurementBits N))) =>
      probability (.bits outcome))
    (ExecutionState.toPMF_mapClassical
      (actual.execute Reference original.state)
      (actual.execute_normalized original) read).symm
  refine mapped.trans ?_
  rw [ExecutionState.toPMF_apply,
    ExecutionState.mapClassical_block_mass_referenceFiberSum]
  apply congrArg ENNReal.ofReal
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro reference _
  exact (reuse_outcome_reference_selected base noQuantum N input parameter
    (original.state.mapClassical
      (fun entry => (entry.1, (entry.2, entry.1))))
    outcome reference reference).trans
    (ExecutionState.referenceFiberSum_mapClassical original.state
      (fun entry => (entry.1, (entry.2, entry.1))) _ reference reference)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
