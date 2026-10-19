/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Physical restart beside the original seven persistent classical cells

The same original child remains one embedded circuit. Its complete output
records include every existing frame cell, hidden service state, history and
path. The classical-only complement changes no physical quantum coordinate,
so the child's predetermined owned seed remains the caller's same seed.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}

private lemma persistentEmbedding_position (width scalarWidth : Nat)
    (index : Fin ctx.systemCount) :
    (persistentEmbedding ctx width scalarWidth).position index = index := by
  apply ctx.quantumLayout.identityInjective
  exact congrArg QuantumWire.identity
    ((persistentEmbedding ctx width scalarWidth).contextEmbedding_position_wire index)

private lemma persistentEmbedding_referenceBasis_first (width scalarWidth : Nat)
    (Reference : Register)
    (input : (Register.prod (persistentCtx ctx width scalarWidth).register Reference).Index) :
    ((persistentEmbedding ctx width scalarWidth).referenceBasis Reference input).1 = input.1 := by
  change ((persistentEmbedding ctx width scalarWidth).basis input.1).1 = input.1
  funext index
  apply Fin.ext
  have preserved := (persistentEmbedding ctx width scalarWidth).contextEmbedding_join_local_value
    ((persistentEmbedding ctx width scalarWidth).basis input.1).1
    ((persistentEmbedding ctx width scalarWidth).basis input.1).2 index
  rw [persistentEmbedding_position (ctx := ctx) width scalarWidth] at preserved
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using preserved.symm

private def sampleExecutionRecords (code : Circuit model ctx ctx false)
    (width scalarWidth : Nat) (H : Type) :
    (Store ctx × (model.HiddenState ×
      ((Store (persistentEmbedding ctx width scalarWidth).frame × H) × code.Path))) ≃
    (Store ctx × (Store (persistentEmbedding ctx width scalarWidth).frame ×
      (model.HiddenState × (H × code.Path)))) where
  toFun record := (record.1, (record.2.2.1.1,
    (record.2.1, (record.2.2.1.2, record.2.2.2))))
  invFun record := (record.1, (record.2.2.1,
    ((record.2.1, record.2.2.2.1), record.2.2.2.2)))
  left_inv := by
    rintro ⟨store, hidden, ⟨frame, history⟩, path⟩
    rfl
  right_inv := by
    rintro ⟨store, frame, hidden, history, path⟩
    rfl

private lemma sampleUnderPersistent_split_block (code : Circuit model ctx ctx false)
    (width scalarWidth : Nat) (Reference : Register) {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (label : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × code.Path))) :
    ((persistentEmbedding ctx width scalarWidth).split
      ((sampleUnderPersistent code width scalarWidth).execute environment Reference state)).block
        ((persistentEmbedding ctx width scalarWidth).record
          (model.HiddenState × (H × code.Path)) label) =
    (code.execute environment
      (Register.prod (persistentEmbedding ctx width scalarWidth).frame.register Reference)
      (((persistentEmbedding ctx width scalarWidth).split state).mapClassical (fun record =>
        (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))).block
      ((sampleExecutionRecords code width scalarWidth H).symm
        ((persistentEmbedding ctx width scalarWidth).record
          (model.HiddenState × (H × code.Path)) label)) := by
  let placement := persistentEmbedding ctx width scalarWidth
  let output := code.execute environment (Register.prod placement.frame.register Reference)
    ((placement.split state).mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))
  have executed :
      (sampleUnderPersistent code width scalarWidth).execute environment Reference state =
        placement.join
          (output.mapClassical (sampleExecutionRecords code width scalarWidth H)) :=
    candidateCheck_sampleUnderPersistent_execute code width scalarWidth Reference state
  have splitEq :
      placement.split
          ((sampleUnderPersistent code width scalarWidth).execute environment Reference state) =
        output.mapClassical (sampleExecutionRecords code width scalarWidth H) :=
    (congrArg
      (fun value : State (persistentCtx ctx width scalarWidth) Reference
          (model.HiddenState × (H × code.Path)) => placement.split value)
      executed).trans (placement.contextEmbedding_split_join _)
  exact (congrArg
      (fun value => value.block
        (placement.record (model.HiddenState × (H × code.Path)) label)) splitEq).trans
    (ExecutionState.coordinate_mapClassical_block output
      (sampleExecutionRecords code width scalarWidth H) _)

private lemma pureKet_fullSelection_of_reindex_first_at {count : Nat}
    (layout : QuantumLayout count) {Reference EncodedReference : Register}
    (state : DensityOperator (Register.prod layout.register Reference))
    (basis : (Register.prod layout.register Reference).Index ≃
      (Register.prod layout.register EncodedReference).Index)
    (first : ∀ input, (basis input).1 = input.1)
    (selection : Finset (Fin count)) (fullSelection : selection = Finset.univ)
    (seed : layout.SelectedBasis selection)
    (promised : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection layout selection EncodedReference
        (state.reindex basis))) :
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection layout selection Reference state) := by
  cases fullSelection
  exact StatePromise.pureKet_fullSelection_of_reindex_first
    layout state basis first seed promised

/-- The same predetermined owned seed survives the actual seven-cell embedding on every record. -/
lemma candidateCheck_sampleUnderPersistent_reinitializedAt
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat)
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt code environment seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (sampleUnderPersistent code width scalarWidth) environment seed := by
  unfold Circuit.ReinitializedAt at fixed ⊢
  intro Reference H _ state label
  let placement := persistentEmbedding ctx width scalarWidth
  let extended := sampleUnderPersistent code width scalarWidth
  let sourceInput := (placement.split state).mapClassical (fun record =>
    (record.1, (record.2.2.1, (record.2.1, record.2.2.2))))
  let sourceRecord := (sampleExecutionRecords code width scalarWidth H).symm
    (placement.record (model.HiddenState × (H × code.Path)) label)
  have sourcePromise := fixed (Register.prod placement.frame.register Reference)
    sourceInput sourceRecord
  have blockEq :
      ((extended.execute environment Reference state).block label).reindex
          (placement.referenceBasis Reference) =
        (code.execute environment (Register.prod placement.frame.register Reference)
          sourceInput).block sourceRecord := by
    calc
      _ = (placement.split (extended.execute environment Reference state)).block
          (placement.record (model.HiddenState × (H × code.Path)) label) := by
        apply DensityOperator.ext
        ext row column
        let output : State (persistentCtx ctx width scalarWidth) Reference
            (model.HiddenState × (H × code.Path)) := extended.execute environment Reference state
        change (output.block label).matrix ((placement.referenceBasis Reference).symm row)
            ((placement.referenceBasis Reference).symm column) =
          ((placement.split output).block
            (placement.record (model.HiddenState × (H × code.Path)) label)).matrix row column
        have actual := placement.contextEmbedding_split_entry
          (History := model.HiddenState × (H × code.Path)) output
          (placement.record (model.HiddenState × (H × code.Path)) label) row column
        have recordEq :
            (placement.record (model.HiddenState × (H × code.Path))).symm
              (placement.record (model.HiddenState × (H × code.Path)) label) = label :=
          (placement.record (model.HiddenState × (H × code.Path))).symm_apply_apply label
        have entryEq := congrArg
          (fun record => (output.block record).matrix
            ((placement.referenceBasis Reference).symm row)
            ((placement.referenceBasis Reference).symm column)) recordEq
        exact entryEq.symm.trans actual.symm
      _ = _ := sampleUnderPersistent_split_block code width scalarWidth Reference state label
  rw [← blockEq] at sourcePromise
  have fullSelection : ctx.borrowedSelectionᶜ = Finset.univ := by
    simp [RuntimeCtx.borrowedSelection, noBorrowed]
  exact pureKet_fullSelection_of_reindex_first_at ctx.quantumLayout
    ((extended.execute environment Reference state).block label) (placement.referenceBasis
      Reference)
    (persistentEmbedding_referenceBasis_first (ctx := ctx) width scalarWidth Reference)
    ctx.borrowedSelectionᶜ fullSelection seed sourcePromise

/-- Measurement, full borrowed restoration and the same fixed seed hold for the actual embed. -/
lemma candidateCheck_sampleUnderPersistent_restartCleanup
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat)
    (cleanup : Circuit.RestartCleanup code environment) (noBorrowed : ctx.borrowedQuantumWires =
      []) :
    Circuit.RestartCleanup (sampleUnderPersistent code width scalarWidth) environment := by
  refine ⟨?_, ?_, ?_⟩
  · intro path
    exact cleanup.measured path
  · intro Reference H _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (sampleUnderPersistent code width scalarWidth) environment
      ((persistentCtx_borrowedQuantumWires ctx width scalarWidth).trans noBorrowed) Reference state
  · obtain ⟨seed, fixed⟩ := cleanup.reinitialized
    exact ⟨seed, candidateCheck_sampleUnderPersistent_reinitializedAt
      code width scalarWidth seed fixed noBorrowed⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
