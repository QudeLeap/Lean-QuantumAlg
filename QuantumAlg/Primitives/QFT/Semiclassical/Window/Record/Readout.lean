/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Instrument
import all QuantumAlg.Core.Execution.Instrument.Execution

/-!
# Full retained records of the real corrected window recursion

The structural active-count induction composes the proved blocks of the same
actual measured stages. Its nested Path retains every measured value and
selected native branch, with the real intermediate Store passed to the next
stage. Persistent service state, incoming history and every external reference
entry remain in the original fibers.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

private lemma conditional_record_values {Value : Type} {first second : Prop}
    (same : first ↔ second) (firstDecision : Decidable first)
    (secondDecision : Decidable second) (yes no : Value) :
    @ite Value first firstDecision yes no = @ite Value second secondDecision yes no := by
  cases firstDecision with
  | isTrue selected =>
      cases secondDecision with
      | isTrue _ => rfl
      | isFalse absent => exact False.elim (absent (same.mp selected))
  | isFalse absent =>
      cases secondDecision with
      | isTrue selected => exact False.elim (absent (same.mpr selected))
      | isFalse _ => rfl

private lemma identity_block_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × Unit))) :
    (((Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        if (original.1, (original.2.1, (original.2.2, ()))) = result then
          (state.block original).matrix else 0 := by
  rcases result with ⟨store, hidden, history, emptyPath⟩
  cases emptyPath
  rw [Circuit.execute_id_block]
  symm
  rw [Finset.sum_eq_single (store, (hidden, history))]
  · simp
  · intro original _ different
    have excluded : (original.1, (original.2.1, (original.2.2, ()))) ≠
        (store, (hidden, (history, ()))) := by
      intro same
      exact different (Prod.ext (congrArg (fun entry => entry.1) same)
        (Prod.ext (congrArg (fun entry => entry.2.1) same)
          (congrArg (fun entry => entry.2.2.1) same)))
    exact if_neg excluded
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

/-- A binary head outcome is cast only through the actual selected wire's qubit dimension. -/
def stageBinaryRecord (ports : Ports ctx totalBits (active + 1))
    (store : Store ctx) (outcome : Fin 2) :
    Store ctx × (stage (operations := operations) (services := services) ports).Path :=
  stageStoreRecord (operations := operations) (services := services) ports store
    (headOutcome ports outcome)

/-- The binary index is a reindexing of the actual measurement, with no outcome discarded. -/
lemma window_stage_binary_record_matrix (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (stage (operations := operations) (services := services) ports).Path))) :
    (((stage ports).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Fin 2,
        if Execution.Instrument.retainedRecord
            (stageBinaryRecord (operations := operations) (services := services) ports)
              original outcome = result then
          nativeStageKraus ports environment.quantum Reference (headOutcome ports outcome) *
            (state.block original).matrix *
              (nativeStageKraus ports environment.quantum Reference
                (headOutcome ports outcome)).conjTranspose
        else 0 := by
  apply Matrix.ext
  intro left right
  refine (window_stage_record_block_matrix ports environment state result left right).trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_congr rfl
  intro original _
  exact (Equiv.sum_comp
    (finCongr (congrArg (fun size : ℕ+ => (size : Nat)) (ports.qubits 0))).symm _).symm

/-- The actual MZ and selected-branch Paths are paired in their executed chronological order. -/
def readoutStoreRecord : (count : Nat) → (ports : Ports ctx totalBits count) → Store ctx →
    Bits count → Store ctx × (readout (operations := operations) (services := services)
      count ports).Path
  | 0, _, store, _ => (store, ())
  | count + 1, ports, store, (head, tail) =>
      let first := stageBinaryRecord (operations := operations) (services := services) ports
        store head
      let rest := readoutStoreRecord count ports.tail first.1 tail
      (rest.1, (first.2, rest.2))

/-- The full real window instrument retains complete original records and actual measured Paths. -/
lemma window_readout_record_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (count : Nat) (ports : Ports ctx totalBits count)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (readout (operations := operations) (services := services) count ports).Path))) :
    (((readout count ports).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Bits count,
        if Execution.Instrument.retainedRecord
            (readoutStoreRecord (operations := operations) (services := services) count ports)
              original outcome = result then
          outcomeKraus environment.quantum Reference count ports outcome *
            (state.block original).matrix *
              (outcomeKraus environment.quantum Reference count ports outcome).conjTranspose
        else 0 := by
  induction count generalizing History Reference with
  | zero =>
      let _ : Unique (Bits 0) := inferInstanceAs (Unique Unit)
      dsimp only [readout, Circuit.Path] at result
      refine (identity_block_matrix environment Reference state result).trans ?_
      simp only [Fintype.sum_unique, readoutStoreRecord, outcomeKraus,
        Execution.Instrument.retainedRecord,
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      apply Finset.sum_congr rfl
      intro original _
      exact conditional_record_values Iff.rfl _ _ _ _
  | succ count ih =>
      have composed := Execution.Instrument.execute_sequenceRetainedBlocks
        (stage (operations := operations) (services := services) ports)
        (readout (operations := operations) (services := services) count ports.tail)
        (stageBinaryRecord (operations := operations) (services := services) ports)
        (readoutStoreRecord (operations := operations) (services := services) count ports.tail)
        (fun reference _ outcome =>
          nativeStageKraus ports environment.quantum reference (headOutcome ports outcome))
        (fun reference _ outcome =>
          outcomeKraus environment.quantum reference count ports.tail outcome)
        environment
        (fun reference {_} _ input selected =>
          window_stage_binary_record_matrix ports environment reference input selected)
        (fun reference {_} _ input selected => ih ports.tail reference input selected)
        Reference state result
      refine composed.trans ?_
      change _ = ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Fin 2 × Bits count,
          if Execution.Instrument.retainedRecord
              (readoutStoreRecord (operations := operations) (services := services)
                (count + 1) ports) original outcome = result then
            outcomeKraus environment.quantum Reference (count + 1) ports outcome *
              (state.block original).matrix *
                (outcomeKraus environment.quantum Reference
                  (count + 1) ports outcome).conjTranspose
          else 0
      simp only [Fintype.sum_prod_type]
      rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
