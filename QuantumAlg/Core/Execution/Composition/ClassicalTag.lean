/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Operations
import all QuantumAlg.Core.Execution.Composition.History
import all QuantumAlg.Core.Execution.Interpret.Preserving
import all QuantumAlg.Core.Execution.State.History

/-!
# Reference-tag naturality for the recursive interpreter's actual state maps

The tag is a mathematical spectator. Its classical representation is kept
separate from the persistent service state and every newly recorded path.
These are internal proof statements about existing recursive interpretations.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace State

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {Hidden H K Path : Type} [Fintype Hidden] [Fintype H] [Fintype K] [Fintype Path]

/-- Decode a reference tag into history while retaining the original service coordinate. -/
def decodeOracleTag (state : State ctx (Tag.prod Reference) (Hidden × H)) :
    State ctx Reference (Hidden × (H × Tag.Index)) :=
  (decodeReferenceTag state).mapHistory (Equiv.prodAssoc Hidden H Tag.Index)

/-- Decode the unchanged tag beside the original input history and retain the actual path. -/
def decodeExecutionTag (state : State ctx (Tag.prod Reference) (Hidden × (H × Path))) :
    State ctx Reference (Hidden × ((H × Tag.Index) × Path)) :=
  (decodeOracleTag state).mapHistory fun record =>
    (record.1, (tagOutcomeExchange H Tag.Index Path).symm record.2)

/-- The decoded service and input-history record retain their original complete tag slice. -/
lemma decodeOracleTag_entry (state : State ctx (Tag.prod Reference) (Hidden × H))
    (store : Store ctx) (hidden : Hidden) (history : H) (tag : Tag.Index)
    (row column : (ctx.register.prod Reference).Index) :
    ((decodeOracleTag state).block (store, (hidden, (history, tag)))).matrix row column =
      (state.block (store, (hidden, history))).matrix
        (row.1, (tag, row.2)) (column.1, (tag, column.2)) := by
  rw [decodeOracleTag, mapHistory_equiv_entry, decodeReferenceTag_entry]
  rfl

/-- Arbitrary input-history maps commute with tag decoding and retain the service state. -/
lemma decodeOracleTag_mapHistory
    (state : State ctx (Tag.prod Reference) (Hidden × H)) (update : H → K) :
    decodeOracleTag (state.mapHistory (fun record => (record.1, update record.2))) =
      (decodeOracleTag state).mapHistory
        (fun record => (record.1, (update record.2.1, record.2.2))) := by
  simp only [decodeOracleTag, decodeReferenceTag_mapHistory, mapHistory_comp,
    Function.comp_def]
  rfl

end State

/-- The actual recursive result preserves every diagonal block of an arbitrary external tag. -/
abbrev TagNatural {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (body : (Reference : Register) → Preserving Hidden ctx ctx Reference Path) : Prop :=
  ∀ {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State ctx (Tag.prod Reference) (Hidden × H)),
    (body Reference (State.decodeOracleTag state)).val =
      State.decodeExecutionTag (body (Tag.prod Reference) state).val

/-- Sequential recursive execution preserves the same tag and records both actual paths. -/
lemma sequence_tagNatural {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Hidden LeftPath RightPath : Type} [Fintype Hidden]
    [Fintype LeftPath] [Fintype RightPath]
    (first : (Reference : Register) → Preserving Hidden ctx ctx Reference LeftPath)
    (second : (Reference : Register) → Preserving Hidden ctx ctx Reference RightPath)
    (firstTag : TagNatural first) (secondTag : TagNatural second)
    (secondHistory : ∀ Reference, HistoryNatural (second Reference))
    {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State ctx (Tag.prod Reference) (Hidden × H)) :
    ((second Reference (first Reference (State.decodeOracleTag state)).val).val.mapHistory
      (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))) =
      State.decodeExecutionTag
        ((second (Tag.prod Reference) (first (Tag.prod Reference) state).val).val.mapHistory
          (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))) := by
  rw [firstTag (Reference := Reference) (Tag := Tag) state]
  simp only [State.decodeExecutionTag]
  rw [secondHistory Reference
    (State.decodeOracleTag (first (Tag.prod Reference) state).val)
    (State.tagOutcomeExchange H Tag.Index LeftPath).symm]
  rw [secondTag (Reference := Reference) (Tag := Tag)
    (first (Tag.prod Reference) state).val]
  rw [State.decodeOracleTag_mapHistory
    (second (Tag.prod Reference) (first (Tag.prod Reference) state).val).val
    (fun history : (H × LeftPath) × RightPath =>
      (history.1.1, (history.1.2, history.2)))]
  simp only [State.decodeExecutionTag,
    State.mapHistory_comp, State.tagOutcomeExchange, Function.comp_def,
    Equiv.coe_fn_symm_mk]

end

end QuantumAlg.Execution
