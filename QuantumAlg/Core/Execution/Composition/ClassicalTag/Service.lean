/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.ClassicalTag
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Record

/-!
# Reference-tag slices through persistent service composition

The inactive service state remains a separate history coordinate. Moving the
external tag into that history neither initializes nor conditions either
service, and the exact coordinate laws apply to arbitrary correlated blocks.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {H Path : Type} [Fintype H] [Fintype Path]

/-- Left-service selection retains the same tag and the complete inactive right state. -/
lemma serviceInputLeft_decodeOracleTag
    (state : State ctx (Tag.prod Reference) (parent.HiddenState × H)) :
    serviceInputLeft join (State.decodeOracleTag state) =
      (State.decodeOracleTag (serviceInputLeft join state)).mapHistory
        (fun record => (record.1,
          Equiv.prodAssoc right.HiddenState H Tag.Index record.2)) := by
  simp only [serviceInputLeft, State.decodeOracleTag]
  rw [State.decodeReferenceTag_mapRecord_decisions (afterMap := inferInstance)
    (ctx := ctx) (Reference := Reference) (Tag := Tag)
    state ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryLeft join H))]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr (State.decodeReferenceTag state) rfl

/-- Right-service selection retains the same tag and the complete inactive left state. -/
lemma serviceInputRight_decodeOracleTag
    (state : State ctx (Tag.prod Reference) (parent.HiddenState × H)) :
    serviceInputRight join (State.decodeOracleTag state) =
      (State.decodeOracleTag (serviceInputRight join state)).mapHistory
        (fun record => (record.1,
          Equiv.prodAssoc left.HiddenState H Tag.Index record.2)) := by
  simp only [serviceInputRight, State.decodeOracleTag]
  rw [State.decodeReferenceTag_mapRecord_decisions (afterMap := inferInstance)
    (ctx := ctx) (Reference := Reference) (Tag := Tag)
    state ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryRight join H))]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr (State.decodeReferenceTag state) rfl

/-- Rejoining a left result restores both services and the tag beside the original history. -/
lemma serviceOutputLeft_decodeExecutionTag
    (state : State ctx (Tag.prod Reference)
      (left.HiddenState × ((right.HiddenState × H) × Path))) :
    serviceOutputLeft join ((State.decodeExecutionTag state).mapHistory
      (fun record => (record.1,
        (Equiv.prodAssoc right.HiddenState H Tag.Index record.2.1, record.2.2)))) =
      State.decodeExecutionTag (serviceOutputLeft join state) := by
  simp only [serviceOutputLeft, State.decodeExecutionTag, State.decodeOracleTag]
  rw [State.decodeReferenceTag_mapRecord_decisions (afterMap := inferInstance)
    (ctx := ctx) (Reference := Reference) (Tag := Tag)
    state ((Equiv.refl (Store ctx)).prodCongr (serviceResultLeft join H Path).symm)]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr (State.decodeReferenceTag state) rfl

/-- Rejoining a right result restores both services and all original tag correlations. -/
lemma serviceOutputRight_decodeExecutionTag
    (state : State ctx (Tag.prod Reference)
      (right.HiddenState × ((left.HiddenState × H) × Path))) :
    serviceOutputRight join ((State.decodeExecutionTag state).mapHistory
      (fun record => (record.1,
        (Equiv.prodAssoc left.HiddenState H Tag.Index record.2.1, record.2.2)))) =
      State.decodeExecutionTag (serviceOutputRight join state) := by
  simp only [serviceOutputRight, State.decodeExecutionTag, State.decodeOracleTag]
  rw [State.decodeReferenceTag_mapRecord_decisions (afterMap := inferInstance)
    (ctx := ctx) (Reference := Reference) (Tag := Tag)
    state ((Equiv.refl (Store ctx)).prodCongr (serviceResultRight join H Path).symm)]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr (State.decodeReferenceTag state) rfl

/-- The actual left-service interpreter preserves every external tag slice. -/
lemma serviceLeftPreserving_tagNatural
    (body : (Reference : Register) → Preserving left.HiddenState ctx ctx Reference Path)
    (natural : TagNatural body) (history : ∀ Reference, HistoryNatural (body Reference)) :
    TagNatural (fun Reference => serviceLeftPreserving join (body Reference)) := by
  intro Reference Tag H _ state
  change serviceOutputLeft join (body Reference
      (serviceInputLeft join (State.decodeOracleTag state))).val =
    State.decodeExecutionTag
      (serviceOutputLeft join (body (Tag.prod Reference) (serviceInputLeft join state)).val)
  rw [serviceInputLeft_decodeOracleTag,
    history Reference (State.decodeOracleTag (serviceInputLeft join state))
      (Equiv.prodAssoc right.HiddenState H Tag.Index),
    natural (serviceInputLeft join state)]
  exact serviceOutputLeft_decodeExecutionTag join _

/-- The actual right-service interpreter preserves every external tag slice. -/
lemma serviceRightPreserving_tagNatural
    (body : (Reference : Register) → Preserving right.HiddenState ctx ctx Reference Path)
    (natural : TagNatural body) (history : ∀ Reference, HistoryNatural (body Reference)) :
    TagNatural (fun Reference => serviceRightPreserving join (body Reference)) := by
  intro Reference Tag H _ state
  change serviceOutputRight join (body Reference
      (serviceInputRight join (State.decodeOracleTag state))).val =
    State.decodeExecutionTag
      (serviceOutputRight join (body (Tag.prod Reference) (serviceInputRight join state)).val)
  rw [serviceInputRight_decodeOracleTag,
    history Reference (State.decodeOracleTag (serviceInputRight join state))
      (Equiv.prodAssoc left.HiddenState H Tag.Index),
    natural (serviceInputRight join state)]
  exact serviceOutputRight_decodeExecutionTag join _

end

end QuantumAlg.Execution
