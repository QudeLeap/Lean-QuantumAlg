/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Selected.Law
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Observation
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

variable {environment : (model N).Environment}

/-- Actual paid reset establishes the same physical seed for every input block. -/
lemma reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History)) :
    BasisSeeded.Holds (Native.context base noQuantum N).quantumLayout.zeroLabel
      ((resetBank base noQuantum N).execute environment Reference state) := by
  exact ZReset.BankParallel.seeded (environment := environment) (services := .empty)
    (operations := BitWord.model)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N)) state

/-- The scratch-scoped reset preserves every store-weighted reference entry. -/
lemma reset_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : Store (Native.context base noQuantum N) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((resetBank base noQuantum N).execute environment Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight entry.1) leftRef rightRef := by
  exact ZReset.BankParallel.referenceFiberSum_preserved (environment := environment)
    (services := .empty) (operations := BitWord.model)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N)) state weight leftRef rightRef

/-- The paid bank reset and next actual observation retain any stable old
classical weight jointly with the conditional source Born law. -/
lemma reuse_outcome_weighted_reference
    (parameter : CInputRef base (ParameterShape N))
    (readWeight : Store (Native.context base noQuantum N) → ℂ)
    (readWeight_stable : ∀ store basis,
      readWeight ((measuredStore base noQuantum N store basis).applyOp
        (packing base noQuantum N)) = readWeight store)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N parameter).execute (sourceEnvironment input) Reference state)
      (fun entry _ => readWeight entry.1 * (if entry.1.read
        (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => readWeight entry.1 * sourceWeight N input
          (entry.1.read (Native.liftInput base noQuantum N parameter)) outcome)
        leftRef rightRef := by
  let reset := (resetBank base noQuantum N).execute (sourceEnvironment input) Reference state
  let weight := fun store : Store (Native.context base noQuantum N) =>
    readWeight store * sourceWeight N input
      (store.read (Native.liftInput base noQuantum N parameter)) outcome
  have first := Circuit.referenceFiberSum_execute_seq (environment := (sourceEnvironment input))
    (resetBank base noQuantum N)
    (body base noQuantum N parameter) state
    (fun store => readWeight store * (if store.read
      (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits outcome then 1 else 0)) leftRef rightRef
  have born := body_outcome_weighted_reference base noQuantum N input parameter
    readWeight readWeight_stable reset (reset_seeded base noQuantum N (environment :=
      sourceEnvironment input) state)
    outcome leftRef rightRef
  have fibers := BasisSeeded.referenceFiberSum_seed _ reset
    (reset_seeded base noQuantum N (environment := sourceEnvironment input) state) weight
      leftRef rightRef
  exact first.trans (born.trans (fibers.symm.trans
    (reset_reference base noQuantum N (environment := sourceEnvironment input) state weight
      leftRef rightRef)))

/-- A subsequent paid sample has the same source Born law on its current
stored parameter, arbitrary reference and persistent hidden state. -/
lemma reuse_outcome_reference (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N parameter).execute (sourceEnvironment input) Reference state)
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
lemma reuse_reference_congr (parameter : CInputRef base (ParameterShape N))
    (left right : Store (Native.context base noQuantum N) → ℂ)
    (agree : ∀ store basis,
      left ((measuredStore base noQuantum N store basis).applyOp
        (packing base noQuantum N)) =
      right ((measuredStore base noQuantum N store basis).applyOp
        (packing base noQuantum N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N parameter).execute environment Reference state)
      (fun entry _ => left entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N parameter).execute environment Reference state)
      (fun entry _ => right entry.1) leftRef rightRef := by
  let reset := (resetBank base noQuantum N).execute environment Reference state
  have leftSeq := Circuit.referenceFiberSum_execute_seq (environment := environment)
    (resetBank base noQuantum N) (body base noQuantum N parameter)
    state left leftRef rightRef
  have rightSeq := Circuit.referenceFiberSum_execute_seq (environment := environment)
    (resetBank base noQuantum N) (body base noQuantum N parameter)
    state right leftRef rightRef
  exact leftSeq.trans ((body_reference_congr base noQuantum N (environment := environment) parameter
    left right agree reset leftRef rightRef).trans rightSeq.symm)

/-- The reused sample also has the original selected mathematical law. -/
lemma reuse_outcome_reference_selected
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reuse base noQuantum N parameter).execute (sourceEnvironment input) Reference state)
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
lemma reuse_outputDistribution (parameter : CInputRef base (ParameterShape N))
    {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles
      (Native.context base noQuantum N) Reference)
    (outcome : Fin (measurementBits N) → Bool) :
    (reuseRun base noQuantum N parameter).outputDistribution (sourceEnvironment input) original
      (.bits outcome) =
      ENNReal.ofReal (∑ reference : Reference.Index,
        ExecutionState.referenceFiberSum original.state
          (fun entry _ =>
            ((selectedOutcomePMF
              (entry.1.read (Native.liftInput base noQuantum N parameter))
              outcome).toReal : ℂ)) reference reference).re := by
  let actual := reuseRun base noQuantum N parameter
  let read := fun record : actual.Record => actual.result record
  have mapped := congrArg
    (fun probability : PMF (CShape.Value (.bits (measurementBits N))) =>
      probability (.bits outcome))
    (ExecutionState.toPMF_mapClassical
      (actual.execute (sourceEnvironment input) Reference original.state)
      (actual.execute_normalized (sourceEnvironment input) original) read).symm
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
