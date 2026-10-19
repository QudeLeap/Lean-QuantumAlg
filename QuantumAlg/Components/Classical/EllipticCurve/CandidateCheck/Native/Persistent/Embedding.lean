/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Context.Embedding.References
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Circuit.Reference.Frame
import all QuantumAlg.Core.Execution.Borrowed.Embedding.Restoration

/-!
# Original fixed-context sampling beside seven persistent recovery cells

The embedding names exactly the seven existing destinations, with their
original keys, retained roles and shapes. It retains the original fixed child
as one Circuit node. No instruction is recompiled, no cell is initialized or
allocated, and no classical or quantum coordinate is discarded.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

/-- The actual seven persistent entries, in their existing head-to-tail order. -/
private def persistentFrameEntries (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    List (RuntimeEntry kind) :=
  [.storage (persistentScalar ctx width scalarWidth).key .retained (PointShape width),
    .storage (persistentTargetAccepted ctx width scalarWidth).key .retained .bit,
    .storage (persistentReconstruction ctx width scalarWidth).key .retained .bit,
    .storage (persistentCandidate ctx width scalarWidth).key .retained (.unsignedWord scalarWidth),
    .storage (persistentInverseSuccess ctx width scalarWidth).key .retained .bit,
    .storage (persistentSelected ctx width scalarWidth).key .retained (.unsignedWord scalarWidth),
    .storage (persistentAccepted ctx width scalarWidth).key .retained .bit]

/-- The frame is derived from the real retained context, without selecting fresh replacement keys.
-/
def persistentFrame (ctx : RuntimeCtx kind) (width scalarWidth : Nat) : RuntimeCtx kind :=
  RuntimeCtx.ofEntries (persistentFrameEntries ctx width scalarWidth)
    (by
      change (persistentKeys ctx width scalarWidth).Nodup
      exact persistentKeys_distinct ctx width scalarWidth)
    (by
      change ([] : List Nat).Nodup
      exact List.nodup_nil)

/-- The original persistent context consists of exactly this frame and the original entries. -/
lemma candidateCheck_persistentFrame_entries (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentCtx ctx width scalarWidth).entries =
      (persistentFrame ctx width scalarWidth).entries ++ ctx.entries := rfl

/-- Every resident frame entry has its actual original persistent key. -/
lemma candidateCheck_persistentFrame_keys (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentFrame ctx width scalarWidth).keys = persistentKeys ctx width scalarWidth := rfl

/-- The seven classical entries add no physical quantum wire. -/
lemma candidateCheck_persistentFrame_quantumWires
    (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentFrame ctx width scalarWidth).quantumWires = [] := rfl

private lemma persistentFrame_keyDisjoint (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    List.Disjoint (persistentKeys ctx width scalarWidth) ctx.keys := by
  have unique := (persistentCtx ctx width scalarWidth).keysNodup
  change (persistentCtx ctx width scalarWidth).keys.Nodup at unique
  rw [persistentCtx_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

private lemma persistentFrame_separate (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    RuntimeCtx.StorageDisjoint ctx (persistentFrame ctx width scalarWidth) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    rw [candidateCheck_persistentFrame_keys]
    exact (persistentFrame_keyDisjoint ctx width scalarWidth).symm
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint ctx.physicalIdx []
    exact List.disjoint_nil_right _

/-- Identity key and physical placement retains the complete real seven-cell complement. -/
def persistentEmbedding (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    ContextEmbedding ctx (persistentCtx ctx width scalarWidth) where
  keys := Function.Embedding.refl _
  physical := Function.Embedding.refl _
  frame := persistentFrame ctx width scalarWidth
  separate := by
    rw [runtimeCtx_relabel_refl]
    exact persistentFrame_separate ctx width scalarWidth
  covers := by
    change ((ctx.relabel _ _).entries ++ (persistentFrame ctx width scalarWidth).entries).Perm
      (persistentCtx ctx width scalarWidth).entries
    rw [runtimeCtx_relabel_refl, candidateCheck_persistentFrame_entries]
    exact List.perm_append_comm

/-- No original storage key is renamed by the retained-cell embedding. -/
lemma candidateCheck_persistentEmbedding_keys
    (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentEmbedding ctx width scalarWidth).keys = Function.Embedding.refl _ := rfl

/-- No original physical identity is renamed by the retained-cell embedding. -/
lemma candidateCheck_persistentEmbedding_physical
    (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (persistentEmbedding ctx width scalarWidth).physical = Function.Embedding.refl _ := rfl

/-- The placed structural input is exactly the original seven-cell reference lift. -/
lemma candidateCheck_persistentEmbedding_input
    (ctx : RuntimeCtx kind) (width scalarWidth : Nat) {shape : CShape}
    (input : CInputRef ctx shape) :
    (persistentEmbedding ctx width scalarWidth).input input =
      persistentInput width scalarWidth input := by
  induction input with
  | storage ref =>
      change CInputRef.storage _ = CInputRef.storage _
      apply congrArg CInputRef.storage
      exact CStorageRef.storageRef_eq_of_key _ _ rfl
  | product first second firstIH secondIH => exact congrArg₂ CInputRef.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CInputRef.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CInputRef.first sourceIH
  | second source sourceIH => exact congrArg CInputRef.second sourceIH
  | vectorGet source index sourceIH =>
      exact congrArg (fun value => CInputRef.vectorGet value index) sourceIH
  | bitsGet source index sourceIH =>
      exact congrArg (fun value => CInputRef.bitsGet value index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => CInputRef.wordBitGet value index) sourceIH

variable {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}

/-- Interpret the original allocation-free child once inside the complete persistent caller. -/
def sampleUnderPersistent (code : Circuit model ctx ctx false) (width scalarWidth : Nat) :
    Circuit model (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  Circuit.embed (persistentEmbedding ctx width scalarWidth) code

/-- Physical placement adds no path choice or outcome to the original sampling child. -/
def sampleUnderPersistentPath (code : Circuit model ctx ctx false) (width scalarWidth : Nat) :
    code.Path ≃ (sampleUnderPersistent code width scalarWidth).Path := Equiv.refl _

/-- The complete chronological event list remains the original child's exact list. -/
lemma candidateCheck_sampleUnderPersistent_eventTrace
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat) (path : code.Path) :
    (sampleUnderPersistent code width scalarWidth).eventTrace path = code.eventTrace path := rfl

/-- Native event multiplicities come from that same unchanged original child path. -/
lemma candidateCheck_sampleUnderPersistent_resourcePool
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat) (path : code.Path) :
    (sampleUnderPersistent code width scalarWidth).resourcePool path = code.resourcePool path :=
  Circuit.resourcePool_embed (persistentEmbedding ctx width scalarWidth) code path

/-- Placement preserves every native-duration assignment on every original path. -/
lemma candidateCheck_sampleUnderPersistent_depth
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat)
    (duration : Resource.Event model → Nat) (path : code.Path) :
    (sampleUnderPersistent code width scalarWidth).depth duration path =
      code.depth duration path := rfl

/-- Quantum time is evaluated on the same original child path. -/
lemma candidateCheck_sampleUnderPersistent_quantumTime
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat) (path : code.Path) :
    (sampleUnderPersistent code width scalarWidth).quantumTime path = code.quantumTime path :=
  Circuit.quantumTime_embed (persistentEmbedding ctx width scalarWidth) code path

/-- Every persistent cell stays resident even while the child touches only its original context. -/
lemma candidateCheck_sampleUnderPersistent_resident
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat) (path : code.Path) :
    (sampleUnderPersistent code width scalarWidth).peakResidentSpace path =
      (persistentCtx ctx width scalarWidth).residentSpace :=
  Circuit.peakResidentSpace_embed (persistentEmbedding ctx width scalarWidth) code path

/-- All seven retained roles are charged in the complete caller's auxiliary space. -/
lemma candidateCheck_sampleUnderPersistent_auxiliary
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat) (path : code.Path) :
    (sampleUnderPersistent code width scalarWidth).peakAuxiliarySpace path =
      (persistentCtx ctx width scalarWidth).auxiliarySpace :=
  Circuit.peakAuxiliarySpace_embed (persistentEmbedding ctx width scalarWidth) code path

open scoped Classical in
/-- Split and rejoin the complete Store, service, history and arbitrary-reference state. -/
lemma candidateCheck_sampleUnderPersistent_execute
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat) (Reference : Register)
    {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H)) :
    (sampleUnderPersistent code width scalarWidth).execute environment Reference state =
      (persistentEmbedding ctx width scalarWidth).join
        ((code.execute environment
          (Register.prod (persistentEmbedding ctx width scalarWidth).frame.register Reference)
          (((persistentEmbedding ctx width scalarWidth).split state).mapClassical (fun record =>
            (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))).mapClassical
          (fun record =>
            (record.1, (record.2.2.1.1,
              (record.2.1, (record.2.2.1.2, record.2.2.2)))))) :=
  Circuit.circuit_execute_embed (persistentEmbedding ctx width scalarWidth) code Reference state

/-- All seven actual cell Stores remain jointly correlated with spectator history and reference. -/
lemma candidateCheck_sampleUnderPersistent_frameObservation
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat) (Reference : Register)
    {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H)) :
    ExecutionState.referenceObservation
      ((persistentEmbedding ctx width scalarWidth).split
        ((sampleUnderPersistent code width scalarWidth).execute environment Reference state))
      (fun record => (record.2.1, record.2.2.2.1)) =
      ((persistentEmbedding ctx width scalarWidth).split state).referenceObservation
        (fun record => (record.2.1, record.2.2.2)) :=
  Circuit.execute_embed_frameObservation
    (persistentEmbedding ctx width scalarWidth) code environment Reference state

/-- A universally restoring child retains the full caller's borrowed correlations under placement.
-/
lemma candidateCheck_sampleUnderPersistent_borrowed
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat)
    (restores : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : State ctx Reference (model.HiddenState × H)),
      code.BorrowedRestored Reference state (code.execute environment Reference state))
    (Reference : Register) {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H)) :
    (sampleUnderPersistent code width scalarWidth).BorrowedRestored Reference state
      ((sampleUnderPersistent code width scalarWidth).execute environment Reference state) :=
  Circuit.borrowedRestored_embed
    (persistentEmbedding ctx width scalarWidth) code environment restores Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
