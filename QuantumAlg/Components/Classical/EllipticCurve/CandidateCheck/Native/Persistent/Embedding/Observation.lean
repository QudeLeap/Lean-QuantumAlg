/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding
import all QuantumAlg.Core.Execution.Context.Embedding.Union
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Supported reads of the actual persistent frame

The original child is embedded once. Its complete frame-reference observation
retains every existing classical cell and old history. Positive output records
therefore inherit predicates on that frame without requiring independent input
blocks or discarding hidden service, path or external-reference coordinates.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma mapped_positive {A B : Type} [Fintype A] [Fintype B] {R : Register}
    (decision : DecidableEq B) (state : ExecutionState A R) (update : A → B) (value : B) :
    0 < ((@ExecutionState.mapClassical A B _ _ R decision state update).block value).mass ↔
      ∃ original, update original = value ∧ 0 < (state.block original).mass := by
  cases Subsingleton.elim decision (Classical.decEq B)
  exact ExecutionState.mapClassical_block_mass_pos_iff state update value

section FrameReads

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private def frameAccepted (width scalarWidth : Nat) :
    CStorageRef (persistentFrame ctx width scalarWidth) .bit where
  key := (persistentAccepted ctx width scalarWidth).key
  role := .retained
  slot := .there (.there (.there (.there (.there (.there .here)))))

private def frameSelected (width scalarWidth : Nat) :
    CStorageRef (persistentFrame ctx width scalarWidth) (.unsignedWord scalarWidth) where
  key := (persistentSelected ctx width scalarWidth).key
  role := .retained
  slot := .there (.there (.there (.there (.there .here))))

private lemma frameAccepted_read (width scalarWidth : Nat)
    (store : Store (persistentCtx ctx width scalarWidth)) :
    ((persistentEmbedding ctx width scalarWidth).store store).2.read
        (.storage (frameAccepted width scalarWidth)) =
      store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef) := by
  let placement := persistentEmbedding ctx width scalarWidth
  have placed : placement.unionFrameInput (.storage (frameAccepted width scalarWidth)) =
      .storage (persistentAccepted ctx width scalarWidth).toCStorageRef := by
    change CInputRef.storage _ = CInputRef.storage _
    exact congrArg CInputRef.storage (CStorageRef.storageRef_eq_of_key _ _ rfl)
  exact (placement.split_frame_read store (.storage (frameAccepted width scalarWidth))).symm.trans
    (congrArg store.read placed)

private lemma frameSelected_read (width scalarWidth : Nat)
    (store : Store (persistentCtx ctx width scalarWidth)) :
    ((persistentEmbedding ctx width scalarWidth).store store).2.read
        (.storage (frameSelected width scalarWidth)) =
      store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) := by
  let placement := persistentEmbedding ctx width scalarWidth
  have placed : placement.unionFrameInput (.storage (frameSelected width scalarWidth)) =
      .storage (persistentSelected ctx width scalarWidth).toCStorageRef := by
    change CInputRef.storage _ = CInputRef.storage _
    exact congrArg CInputRef.storage (CStorageRef.storageRef_eq_of_key _ _ rfl)
  exact (placement.split_frame_read store (.storage (frameSelected width scalarWidth))).symm.trans
    (congrArg store.read placed)

end FrameReads

variable {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}

/-- Every supported record keeps predicates on the entire original seven-cell frame. -/
lemma candidateCheck_sampleUnderPersistent_frame_supported
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (predicate : Store (persistentFrame ctx width scalarWidth) → Prop)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      predicate ((persistentEmbedding ctx width scalarWidth).store entry.1).2)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × code.Path)))
    (positive : 0 < (((sampleUnderPersistent code width scalarWidth).execute environment
      Reference state).block result).mass) :
    predicate ((persistentEmbedding ctx width scalarWidth).store result.1).2 := by
  let placement := persistentEmbedding ctx width scalarWidth
  let output : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × (H × code.Path)) :=
    (sampleUnderPersistent code width scalarWidth).execute environment Reference state
  let outputRecord := placement.record (model.HiddenState × (H × code.Path)) result
  have splitPositive : 0 < ((placement.split output).block outputRecord).mass := by
    have splitBlock : (placement.split output).block outputRecord =
        (output.block result).reindex (placement.referenceBasis Reference) := by
      apply DensityOperator.ext
      ext row column
      change ((placement.split output).block outputRecord).matrix row column =
        (output.block result).matrix ((placement.referenceBasis Reference).symm row)
          ((placement.referenceBasis Reference).symm column)
      simpa only [outputRecord, Equiv.symm_apply_apply] using
        placement.contextEmbedding_split_entry output outputRecord row column
    have sameMass := (congrArg DensityOperator.mass splitBlock).trans
      (DensityOperator.reindex_mass (output.block result) (placement.referenceBasis Reference))
    exact Eq.mpr (congrArg (fun mass : ℝ => 0 < mass) sameMass) positive
  have observedPositive : 0 < ((ExecutionState.referenceObservation
      (placement.split output) (fun record => (record.2.1, record.2.2.2.1))).block
        (outputRecord.2.1, outputRecord.2.2.2.1)).mass := by
    rw [ExecutionState.referenceObservation, ExecutionState.executionState_marginalLeft_block_mass,
      ExecutionState.reindex_block_mass]
    exact (mapped_positive _ _ _ _).mpr
      ⟨outputRecord, rfl, splitPositive⟩
  have observationEq :
      ExecutionState.referenceObservation (placement.split output)
          (fun record => (record.2.1, record.2.2.2.1)) =
        ExecutionState.referenceObservation (placement.split state)
          (fun record => (record.2.1, record.2.2.2)) :=
    candidateCheck_sampleUnderPersistent_frameObservation code width scalarWidth Reference state
  have observationMass := congrArg
    (fun value : ExecutionState (Store placement.frame × H)
        (placement.frame.register.prod Reference) =>
      (value.block (outputRecord.2.1, outputRecord.2.2.2.1)).mass) observationEq
  have observedPositive : 0 < ((ExecutionState.referenceObservation
      (placement.split state) (fun record => (record.2.1, record.2.2.2))).block
        (outputRecord.2.1, outputRecord.2.2.2.1)).mass :=
    Eq.mp (congrArg (fun mass : ℝ => 0 < mass) observationMass) observedPositive
  rw [ExecutionState.referenceObservation, ExecutionState.executionState_marginalLeft_block_mass,
    ExecutionState.reindex_block_mass] at observedPositive
  obtain ⟨original, same, present⟩ :=
    (mapped_positive _ _ _ _).mp observedPositive
  have sourcePositive :
      0 < (state.block ((placement.record (model.HiddenState × H)).symm original)).mass := by
    simpa only [ContextEmbedding.split, ExecutionState.reindex_block_mass,
      ExecutionState.coordinate_mapClassical_block] using present
  have kept := holds ((placement.record (model.HiddenState × H)).symm original) sourcePositive
  have sourceFrame := congrArg (fun record => record.2.1)
    ((placement.record (model.HiddenState × H)).apply_symm_apply original)
  change (placement.store ((placement.record (model.HiddenState × H)).symm original).1).2 =
    original.2.1 at sourceFrame
  rw [sourceFrame] at kept
  have sameFrame := congrArg Prod.fst same
  change original.2.1 = (placement.store result.1).2 at sameFrame
  rwa [sameFrame] at kept

/-- The real accepted and selected reads retain every predicate on positive execution records. -/
lemma candidateCheck_sampleUnderPersistent_latches_property
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (property : Bool × (CShape.unsignedWord scalarWidth).Value → Prop)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      property
        ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
          entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × code.Path)))
    (positive : 0 < (((sampleUnderPersistent code width scalarWidth).execute environment
      Reference state).block result).mass) :
    property
      ((result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
        result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) := by
  have readPair (store : Store (persistentCtx ctx width scalarWidth)) :
      ((((persistentEmbedding ctx width scalarWidth).store store).2.read
          (.storage (frameAccepted (ctx := ctx) width scalarWidth))).toBool,
        ((persistentEmbedding ctx width scalarWidth).store store).2.read
          (.storage (frameSelected (ctx := ctx) width scalarWidth))) =
      ((store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
        store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) := by
    exact Prod.ext
      (congrArg CShape.Value.toBool (frameAccepted_read (ctx := ctx) width scalarWidth store))
      (frameSelected_read (ctx := ctx) width scalarWidth store)
  have kept := candidateCheck_sampleUnderPersistent_frame_supported (environment := environment)
    code width scalarWidth state
    (fun frame => property
      ((frame.read (.storage (frameAccepted (ctx := ctx) width scalarWidth))).toBool,
        frame.read (.storage (frameSelected (ctx := ctx) width scalarWidth))))
    (by
      intro entry present
      exact Eq.mpr (congrArg property (readPair entry.1)) (holds entry present)) result positive
  exact Eq.mp (congrArg property (readPair result.1)) kept

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
