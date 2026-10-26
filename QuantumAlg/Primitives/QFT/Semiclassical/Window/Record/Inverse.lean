/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Word
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Readout
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Rows.Feedback

/-!
# Full source-row instrument of the actual recycled inverse-Fourier window

The actual original-cell feedback word is followed by the same measured and
reset readout. Its complete recorded Path, persistent hidden state and incoming
history are retained, including all original Store overwrite collisions and
arbitrary external reference coherences. The independently specified source row
is a theorem about this executed syntax, not an instrument premise.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- The complete readout record returns exactly its actual ordered MZ writes. -/
lemma readoutStoreRecord_store (count : Nat) (ports : Ports ctx totalBits count)
    (store : Store ctx) (outcome : Bits count) :
    (readoutStoreRecord (operations := operations) (services := services)
      count ports store outcome).1 = outcomeStore count ports store outcome := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      rcases outcome with ⟨head, tail⟩
      exact ih ports.tail _ tail

/-- The true earlier-cell branch record precedes the actual measured-bank record. -/
def inverseStoreRecord (ports : Ports ctx totalBits active) (store : Store ctx)
    (outcome : Bits active) :
    Store ctx × (inverseCode (operations := operations) (services := services) ports).Path :=
  let feedback := Feedback.wordStoreRecord (operations := operations) (services := services)
    ports (List.finRange active) store ()
  let measured := readoutStoreRecord (operations := operations) (services := services)
    active ports feedback.1 outcome
  (measured.1, (feedback.2, measured.2))

lemma inverseStoreRecord_store (ports : Ports ctx totalBits active) (store : Store ctx)
    (outcome : Bits active) :
    (inverseStoreRecord (operations := operations) (services := services)
      ports store outcome).1 = outcomeStore active ports store outcome := by
  unfold inverseStoreRecord
  rw [readoutStoreRecord_store, Feedback.wordStoreRecord_store]

/-- Every full actual inverse-window record has precisely its native feedback/readout product. -/
lemma window_inverseCode_record_matrix (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (inverseCode (operations := operations) (services := services) ports).Path))) :
    (((inverseCode ports).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Bits active,
        if Execution.Instrument.retainedRecord
            (inverseStoreRecord (operations := operations) (services := services) ports)
              original outcome = result then
          (outcomeKraus environment.quantum Reference active ports outcome *
              Feedback.wordOperator ports environment.quantum Reference original.1
                (List.finRange active)) * (state.block original).matrix *
            (outcomeKraus environment.quantum Reference active ports outcome *
              Feedback.wordOperator ports environment.quantum Reference original.1
                (List.finRange active)).conjTranspose
        else 0 := by
  have composed := Execution.Instrument.execute_sequenceRetainedBlocks
    (priorFeedback (operations := operations) (services := services) ports (List.finRange active))
    (readout (operations := operations) (services := services) active ports)
    (Feedback.wordStoreRecord (operations := operations) (services := services)
      ports (List.finRange active))
    (readoutStoreRecord (operations := operations) (services := services) active ports)
    (fun reference store _ =>
      Feedback.wordOperator ports environment.quantum reference store (List.finRange active))
    (fun reference _ outcome => outcomeKraus environment.quantum reference active ports outcome)
    environment
    (fun reference {_} _ input selected => Feedback.word_record_matrix
      ports (List.finRange active) environment reference input selected)
    (fun reference {_} _ input selected =>
      window_readout_record_matrix environment active ports reference input selected)
    Reference state result
  refine composed.trans ?_
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  simp only [Execution.Instrument.retainedRecord,
    Execution.Instrument.sequenceRetainedRecord, inverseStoreRecord]
  split_ifs <;> rfl

/-- Exact independently specified source rows on complete actual records, including HiddenState. -/
lemma window_inverseCode_source_record_matrix (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (inverseCode (operations := operations) (services := services) ports).Path))) :
    (((inverseCode ports).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Bits active,
        if Execution.Instrument.retainedRecord
            (inverseStoreRecord (operations := operations) (services := services) ports)
              original outcome = result then
          sourceWindowKraus ports Reference original.1 outcome * (state.block original).matrix *
            (sourceWindowKraus ports Reference original.1 outcome).conjTranspose
        else 0 := by
  refine (window_inverseCode_record_matrix ports environment Reference state result).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases recorded : Execution.Instrument.retainedRecord
      (inverseStoreRecord (operations := operations) (services := services) ports)
        original outcome = result
  · simp only [if_pos recorded]
    rw [window_feedbackKraus_eq_source]
  · simp only [if_neg recorded]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
