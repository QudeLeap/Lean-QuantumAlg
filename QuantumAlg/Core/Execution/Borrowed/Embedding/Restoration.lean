/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.Embedding.State
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Encoding
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.State.History

/-!
# Transfer of complete borrowed restoration through physical embedding

The actual frame store remains a classical spectator jointly with all local
borrowed systems and the complete quantum frame. Encoding that spectator in
the external reference permits one restoration hypothesis on the unchanged
joint input. Decoding and physical reassembly then recover the caller's whole
borrowed CQ state. No conditional admission or independence premise is used.
-/

namespace QuantumAlg

noncomputable section

attribute [local instance] Classical.decEq

open Execution

namespace Circuit

/-- One restoration statement on the encoded joint input retains the entire spectator label. -/
lemma borrowedRestored_tagged_of_encoded
    {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (body : Circuit model ctx ctx false) (environment : model.Environment)
    {Reference Tag : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × (History × Tag.Index)))
    (restores : body.BorrowedRestored (Tag.prod Reference) (State.encodeOracleTag state)
      (body.execute environment (Tag.prod Reference) (State.encodeOracleTag state))) :
    observeBorrowedTagged (Tag := Tag) (fun record => record.2.1.2)
        (body.execute environment Reference state) =
      observeBorrowedTagged (Tag := Tag) (fun record => record.2.2) state := by
  change observeBorrowed (Tag.prod Reference)
      (body.execute environment (Tag.prod Reference) (State.encodeOracleTag state)) =
    observeBorrowed (Tag.prod Reference) (State.encodeOracleTag state) at restores
  have decoded := congrArg
    (decodeBorrowedTag (ctx := ctx) (Tag := Tag) (Reference := Reference)) restores
  rw [← observeBorrowedTagged_decodeReferenceTag,
    ← observeBorrowedTagged_decodeReferenceTag] at decoded
  rw [body.execute_encodedClassicalTag environment (Tag := Tag) state]
  calc
    _ = observeBorrowedTagged Prod.snd
        (State.decodeReferenceTag
          (body.execute environment (Tag.prod Reference) (State.encodeOracleTag state))) := by
      rw [State.decodeExecutionTag, observeBorrowedTagged_mapHistory,
        State.decodeOracleTag, observeBorrowedTagged_mapHistory]
      rfl
    _ = observeBorrowedTagged Prod.snd
        (State.decodeReferenceTag (State.encodeOracleTag state)) := decoded
    _ = observeBorrowedTagged (fun record => record.2.2) state := by
      have original := congrArg
        (observeBorrowedTagged (Tag := Tag) (fun record => record.2.2))
        (State.decode_encodeOracleTag state)
      rw [State.decodeOracleTag, observeBorrowedTagged_mapHistory] at original
      exact original

end Circuit

namespace ContextEmbedding

variable {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
  (placement : ContextEmbedding localCtx caller)

/-- The complete framed input with its unchanged frame store in the spectator coordinate. -/
def borrowedTaggedInput {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History)) :
    State localCtx (placement.frame.register.prod Reference)
      (model.HiddenState × (History × placement.frameStoreTag.Index)) :=
  (placement.split state).mapHistory fun record =>
    (record.2.1, (record.2.2, record.1))

/-- The actual embedded execution retains precisely the tagged original child observation. -/
lemma contextEmbedding_observeBorrowedTagged_execute
    {allowAllocation : Bool} (body : Circuit model localCtx localCtx false)
    (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History)) :
    observeBorrowedTagged (Tag := placement.frameStoreTag) Prod.fst
        (placement.split
          ((Circuit.embed (allowAllocation := allowAllocation) placement body).execute
            environment Reference state)) =
      observeBorrowedTagged (Tag := placement.frameStoreTag) (fun record => record.2.1.2)
        (body.execute environment (placement.frame.register.prod Reference)
          (placement.borrowedTaggedInput (model := model) state)) := by
  let swap : History × placement.frameStoreTag.Index → Store placement.frame × History :=
    fun record => (record.2, record.1)
  have arranged :
      (placement.split state).mapHistory (fun record =>
        (record.2.1, (record.1, record.2.2))) =
      (placement.borrowedTaggedInput (model := model) state).mapHistory (fun record =>
        (record.1, swap record.2)) := by
    simp only [borrowedTaggedInput, State.mapHistory_comp, Function.comp_def, swap]
  rw [Circuit.circuit_execute_embed, placement.contextEmbedding_split_join]
  have initial :
      (placement.split state).mapClassical (fun record =>
        (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))) =
      (placement.split state).mapHistory (fun record =>
        (record.2.1, (record.1, record.2.2))) :=
    ExecutionState.executionState_mapClassical_congr _ rfl
  rw [initial]
  calc
    _ = observeBorrowedTagged (Tag := placement.frameStoreTag) Prod.fst
        ((body.execute environment (placement.frame.register.prod Reference)
          ((placement.split state).mapHistory (fun record =>
            (record.2.1, (record.1, record.2.2))))).mapHistory
          (fun record => (record.2.1.1, (record.1, (record.2.1.2, record.2.2))))) := by
      apply congrArg (observeBorrowedTagged (Tag := placement.frameStoreTag) Prod.fst)
      exact ExecutionState.executionState_mapClassical_congr _ rfl
    _ = _ := by
      rw [arranged, body.execute_mapHistory environment
          (placement.frame.register.prod Reference)
          (placement.borrowedTaggedInput (model := model) state) swap,
        observeBorrowedTagged_mapHistory, observeBorrowedTagged_mapHistory]
      rfl

end ContextEmbedding

namespace Circuit

/-- Restoration on the encoded framed input restores the complete physical caller interface. -/
lemma borrowedRestored_embed_of_encoded
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false)
    (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History))
    (restores : body.BorrowedRestored
      (placement.frameStoreTag.prod (placement.frame.register.prod Reference))
      (State.encodeOracleTag (placement.borrowedTaggedInput (model := model) state))
      (body.execute environment
        (placement.frameStoreTag.prod (placement.frame.register.prod Reference))
        (State.encodeOracleTag (placement.borrowedTaggedInput (model := model) state)))) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).BorrowedRestored
      Reference state
      ((Circuit.embed (allowAllocation := allowAllocation) placement body).execute
        environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext,
    placement.contextEmbedding_observeBorrowed_split,
    placement.contextEmbedding_observeBorrowed_split]
  apply congrArg (placement.reassembleBorrowed Reference)
  rw [placement.contextEmbedding_observeBorrowedTagged_execute,
    borrowedRestored_tagged_of_encoded body environment
      (placement.borrowedTaggedInput (model := model) state) restores]
  simp only [ContextEmbedding.borrowedTaggedInput,
    observeBorrowedTagged_mapHistory, Function.comp_def]
  rfl

/-- A child restoring every complete input remains restoring in every certified physical frame. -/
lemma borrowedRestored_embed
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false)
    (environment : model.Environment)
    (restores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State localCtx Reference (model.HiddenState × History)),
      body.BorrowedRestored Reference state (body.execute environment Reference state))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History)) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).BorrowedRestored
      Reference state
      ((Circuit.embed (allowAllocation := allowAllocation) placement body).execute
        environment Reference state) :=
  borrowedRestored_embed_of_encoded placement body environment Reference state (restores _ _)

end Circuit

end

end QuantumAlg
