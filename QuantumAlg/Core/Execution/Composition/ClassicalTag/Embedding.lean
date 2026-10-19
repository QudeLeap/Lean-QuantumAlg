/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.ClassicalTag
import all QuantumAlg.Core.Execution.Composition.Reference
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Embedding

/-!
# Complete tag slices through a recursive physical embedding

The helper uses the actual interpreter's split and join. The untouched frame
remains jointly correlated with the original reference, service state and
history. Reference naturality only reorders the frame beside the external tag;
tag naturality then recovers each complete classical spectator slice.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference Tag : Register}
  {Hidden H Path : Type} [Fintype Hidden] [Fintype H] [Fintype Path]

/-- The recursive embedding's exact input coordinates, including its full frame store. -/
def tagFrameInput (state : State caller Reference (Hidden × H)) :
    State localCtx (placement.frame.register.prod Reference)
      (Hidden × (Store placement.frame × H)) :=
  (placement.split state).mapHistory fun history =>
    (history.2.1, (history.1, history.2.2))

/-- The recursive embedding's exact output coordinates, with the complete caller restored. -/
def tagFrameOutput
    (state : State localCtx (placement.frame.register.prod Reference)
      (Hidden × ((Store placement.frame × H) × Path))) :
    State caller Reference (Hidden × (H × Path)) :=
  placement.join (state.mapHistory fun history =>
    (history.2.1.1, (history.1, (history.2.1.2, history.2.2))))

/-- Decoding the caller retains the complete frame store as a separate input coordinate. -/
lemma tagFrameInput_decodeOracleTag
    (state : State caller (Tag.prod Reference) (Hidden × H)) :
    tagFrameInput placement (State.decodeOracleTag state) =
      (State.decodeOracleTag
        ((placement.splitReferenceTag state).mapHistory fun history =>
          (history.2.1, (history.1, history.2.2)))).mapHistory
            (fun record => (record.1,
              Equiv.prodAssoc (Store placement.frame) H Tag.Index record.2)) := by
  simp only [tagFrameInput, State.decodeOracleTag, placement.split_mapHistory,
    State.decodeReferenceTag_mapHistory, placement.decodeReferenceTag_split,
    State.mapHistory_comp, Function.comp_def]
  rfl

/-- Decoding a framed result retains its tag alongside the original caller history. -/
lemma tagFrameOutput_decodeExecutionTag
    (state : State localCtx (Tag.prod (placement.frame.register.prod Reference))
      (Hidden × ((Store placement.frame × H) × Path))) :
    tagFrameOutput placement ((State.decodeExecutionTag state).mapHistory
      (fun record => (record.1,
        (Equiv.prodAssoc (Store placement.frame) H Tag.Index record.2.1, record.2.2)))) =
      State.decodeExecutionTag (placement.joinReferenceTag (state.mapHistory
        (fun history => (history.2.1.1, (history.1, (history.2.1.2, history.2.2)))))) := by
  simp only [tagFrameOutput, State.decodeExecutionTag, State.decodeOracleTag,
    placement.decodeReferenceTag_join, State.decodeReferenceTag_mapHistory,
    ← placement.join_mapHistory, State.mapHistory_comp, Function.comp_def]
  rfl

/-- Undoing only the frame/tag reference permutation gives the actual interpreter output. -/
lemma tagFrameOutput_reference
    (state : State localCtx (placement.frame.register.prod (Tag.prod Reference))
      (Hidden × ((Store placement.frame × H) × Path))) :
    placement.joinReferenceTag
      (State.mapHistory (ctx := localCtx)
        (Reference := Tag.prod (placement.frame.register.prod Reference))
        (state.reindex
          (S := localCtx.register.prod (Tag.prod (placement.frame.register.prod Reference)))
          ((Equiv.refl localCtx.register.Index).prodCongr
            (State.referenceTagBasis (ctx := placement.frame)
              (Reference := Reference) (Tag := Tag))))
        (fun history => (history.2.1.1, (history.1, (history.2.1.2, history.2.2))))) =
      tagFrameOutput placement state := by
  rw [State.composition_reindex_mapHistory]
  dsimp only [ContextEmbedding.joinReferenceTag, tagFrameOutput]
  apply congrArg placement.join
  exact ExecutionState.coordinate_reindex_inverse _ _

/-- Complete recursive physical framing preserves every external classical tag slice. -/
lemma embedPreserving_tagNatural
    (body : (Reference : Register) → Preserving Hidden localCtx localCtx Reference Path)
    (natural : TagNatural body) (history : ∀ Reference, HistoryNatural (body Reference))
    (reference : ReferenceNatural body) :
    TagNatural (fun Reference => embedPreserving placement Reference
      (body (placement.frame.register.prod Reference))) := by
  intro Reference Tag H _ state
  let original := tagFrameInput placement state
  let tagged := (placement.splitReferenceTag state).mapHistory fun history =>
    (history.2.1, (history.1, history.2.2))
  have tagCoordinates : tagged = original.reindex
      (S := localCtx.register.prod (Tag.prod (placement.frame.register.prod Reference)))
      ((Equiv.refl localCtx.register.Index).prodCongr
        (State.referenceTagBasis (ctx := placement.frame)
          (Reference := Reference) (Tag := Tag))) := by
    dsimp only [tagged, original, tagFrameInput, ContextEmbedding.splitReferenceTag]
    exact State.composition_reindex_mapHistory _ _ _
  change tagFrameOutput placement
      (body (placement.frame.register.prod Reference)
        (tagFrameInput placement (State.decodeOracleTag state))).val =
    State.decodeExecutionTag (tagFrameOutput placement
      (body (placement.frame.register.prod (Tag.prod Reference)) original).val)
  rw [tagFrameInput_decodeOracleTag,
    history (placement.frame.register.prod Reference) (State.decodeOracleTag tagged)
      (Equiv.prodAssoc (Store placement.frame) H Tag.Index),
    natural tagged, tagFrameOutput_decodeExecutionTag]
  rw [tagCoordinates,
    reference (State.referenceTagBasis (ctx := placement.frame)
      (Reference := Reference) (Tag := Tag)) original,
    tagFrameOutput_reference]

end

end QuantumAlg.Execution
