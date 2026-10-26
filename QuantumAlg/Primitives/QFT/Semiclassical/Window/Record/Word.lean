/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Feedback
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Word

/-!
# Complete actual records of the earlier-window feedback word

Both list inductions follow the literal same-cell branch syntax. The second
component receives the first component's actual Store, and proved unchanged
Store projections identify the exact same causal native operator word. No
finite window size is expanded, and every branch selection remains in Path.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

private lemma empty_record_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × Unit))) :
    (((Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ _outcome : Unit,
        if (original.1, (original.2.1, (original.2.2, ()))) = result then
          (1 : HilbertOperator (ctx.register.prod Reference)) * (state.block original).matrix *
            (1 : HilbertOperator (ctx.register.prod Reference)).conjTranspose
        else 0 := by
  refine (identity_record_matrix environment Reference state result).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases recorded : (original.1, (original.2.1, (original.2.2, ()))) = result
  · simp only [if_pos recorded, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · simp only [if_neg recorded]

/-- Chronological actual branch records for all previous positions of one current wire. -/
def atStoreRecord (ports : Ports ctx totalBits active) (current : Fin active) :
    (previous : List (BitPosition totalBits)) → Store ctx → Unit →
      Store ctx × (feedbackAt (operations := operations) (services := services)
        ports current previous).Path
  | [], store, _ => (store, ())
  | previous :: rest, store, _ =>
      let head := oneStoreRecord (operations := operations) (services := services)
        ports previous current store ()
      let tail := atStoreRecord ports current rest head.1 ()
      (tail.1, (head.2, tail.2))

lemma atStoreRecord_store (ports : Ports ctx totalBits active) (current : Fin active)
    (previous : List (BitPosition totalBits)) (store : Store ctx) (outcome : Unit) :
    (atStoreRecord (operations := operations) (services := services) ports current previous
      store outcome).1 = store := by
  induction previous generalizing store with
  | nil => rfl
  | cons previous rest ih =>
      exact (ih _).trans (oneStoreRecord_store (operations := operations) (services := services)
        ports previous current store ())

/-- The same actual feedback list has the exact full retained-record operator product. -/
lemma at_record_matrix (ports : Ports ctx totalBits active) (current : Fin active)
    (previous : List (BitPosition totalBits))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (feedbackAt (operations := operations) (services := services)
        ports current previous).Path))) :
    (((feedbackAt ports current previous).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Unit,
        if Execution.Instrument.retainedRecord
            (atStoreRecord (operations := operations) (services := services)
              ports current previous) original outcome = result then
          atOperator ports current environment.quantum Reference original.1 previous *
            (state.block original).matrix *
              (atOperator ports current environment.quantum Reference original.1
                previous).conjTranspose
        else 0 := by
  induction previous generalizing Reference History with
  | nil =>
      refine (empty_record_matrix environment Reference state result).trans ?_
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      cases outcome
      dsimp only [atOperator, atStoreRecord, Execution.Instrument.retainedRecord]
      exact conditional_values _ _ _ _
  | cons previous rest ih =>
      have composed := Execution.Instrument.execute_sequenceRetainedBlocks
        (one (oracles := .empty) (operations := operations) (services := services)
          ports previous current)
        (feedbackAt (operations := operations) (services := services) ports current rest)
        (oneStoreRecord (operations := operations) (services := services)
          ports previous current)
        (atStoreRecord (operations := operations) (services := services) ports current rest)
        (fun reference store _ =>
          oneOperator ports previous current environment.quantum reference store)
        (fun reference store _ =>
          atOperator ports current environment.quantum reference store rest)
        environment
        (fun reference {_} _ input selected =>
          one_record_matrix ports previous current environment reference input selected)
        (fun reference {_} _ input selected => ih reference input selected)
        Reference state result
      refine composed.trans ?_
      simp only [Fintype.sum_unique, atStoreRecord, atOperator,
        Execution.Instrument.retainedRecord,
        Execution.Instrument.sequenceRetainedRecord, oneStoreRecord_store]
      apply Finset.sum_congr rfl
      intro original _
      exact conditional_values _ _ _ _

/-- Actual branch Paths for every current wire are retained in their literal list order. -/
def wordStoreRecord (ports : Ports ctx totalBits active) : (current : List (Fin active)) →
    Store ctx → Unit → Store ctx ×
      (priorFeedback (operations := operations) (services := services) ports current).Path
  | [], store, _ => (store, ())
  | current :: rest, store, _ =>
      let head := atStoreRecord (operations := operations) (services := services)
        ports current (previousPositions totalBits) store ()
      let tail := wordStoreRecord ports rest head.1 ()
      (tail.1, (head.2, tail.2))

lemma wordStoreRecord_store (ports : Ports ctx totalBits active) (current : List (Fin active))
    (store : Store ctx) (outcome : Unit) :
    (wordStoreRecord (operations := operations) (services := services) ports current
      store outcome).1 = store := by
  induction current generalizing store with
  | nil => rfl
  | cons current rest ih =>
      exact (ih _).trans (atStoreRecord_store (operations := operations) (services := services)
        ports current (previousPositions totalBits) store ())

/-- The full real prior-window feedback has the native word on every original complete block. -/
lemma word_record_matrix (ports : Ports ctx totalBits active) (current : List (Fin active))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (priorFeedback (operations := operations) (services := services) ports current).Path))) :
    (((priorFeedback ports current).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Unit,
        if Execution.Instrument.retainedRecord
            (wordStoreRecord (operations := operations) (services := services) ports current)
              original outcome = result then
          wordOperator ports environment.quantum Reference original.1 current *
            (state.block original).matrix *
              (wordOperator ports environment.quantum Reference original.1 current).conjTranspose
        else 0 := by
  induction current generalizing Reference History with
  | nil =>
      refine (empty_record_matrix environment Reference state result).trans ?_
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      cases outcome
      dsimp only [wordOperator, wordStoreRecord, Execution.Instrument.retainedRecord]
      exact conditional_values _ _ _ _
  | cons current rest ih =>
      have composed := Execution.Instrument.execute_sequenceRetainedBlocks
        (feedbackAt (operations := operations) (services := services)
          ports current (previousPositions totalBits))
        (priorFeedback (operations := operations) (services := services) ports rest)
        (atStoreRecord (operations := operations) (services := services)
          ports current (previousPositions totalBits))
        (wordStoreRecord (operations := operations) (services := services) ports rest)
        (fun reference store _ => atOperator ports current environment.quantum reference
          store (previousPositions totalBits))
        (fun reference store _ => wordOperator ports environment.quantum reference store rest)
        environment
        (fun reference {_} _ input selected => at_record_matrix ports current
          (previousPositions totalBits) environment reference input selected)
        (fun reference {_} _ input selected => ih reference input selected)
        Reference state result
      refine composed.trans ?_
      simp only [Fintype.sum_unique, wordStoreRecord, wordOperator,
        Execution.Instrument.retainedRecord,
        Execution.Instrument.sequenceRetainedRecord, atStoreRecord_store]
      apply Finset.sum_congr rfl
      intro original _
      exact conditional_values _ _ _ _

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
