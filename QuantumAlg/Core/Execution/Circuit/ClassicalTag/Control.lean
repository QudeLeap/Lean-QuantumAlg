/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Primitive
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Complete reference-tag slices through actual control flow

Classical branches select their real input-store fibers before executing the
chosen child. Iteration passes the same persistent service state and records
each actual child path. Neither operation inspects or conditions the external
tag, and the old history remains present throughout.
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution.State

/-- Selecting an actual store fiber retains precisely the same complete tag slices. -/
lemma decodeOracleTag_selectClassical {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference Tag : Register} {Hidden H Value : Type}
    [Fintype Hidden] [Fintype H] [DecidableEq Value]
    (state : State ctx (Tag.prod Reference) (Hidden × H))
    (read : Store ctx → Value) (value : Value) :
    decodeOracleTag (state.selectClassical (fun record => read record.1) value) =
      (decodeOracleTag state).selectClassical (fun record => read record.1) value := by
  apply ExecutionState.ext
  rintro ⟨store, hidden, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeOracleTag_entry]
  by_cases selected : read store = value
  · simp only [ExecutionState.selectClassical_block, selected, if_true,
      decodeOracleTag_entry]
  · simp only [ExecutionState.selectClassical_block, selected, if_false,
      DensityOperator.zero_matrix, Matrix.zero_apply]

/-- Relabeling an actual output path retains the separate original history and tag. -/
lemma decodeExecutionTag_mapPath {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference Tag : Register} {Hidden H Path Result : Type}
    [Fintype Hidden] [Fintype H] [Fintype Path] [Fintype Result]
    (state : State ctx (Tag.prod Reference) (Hidden × (H × Path))) (update : Path → Result) :
    decodeExecutionTag
        (state.mapHistory (fun record => (record.1, (record.2.1, update record.2.2)))) =
      (decodeExecutionTag state).mapHistory
        (fun record => (record.1, (record.2.1, update record.2.2))) := by
  simp only [decodeExecutionTag, decodeOracleTag, decodeReferenceTag_mapHistory,
    mapHistory_comp, Function.comp_def]
  rfl

end Execution.State

namespace Circuit

/-- A real classical branch preserves the tag and records its selected dependent path. -/
lemma branch_decodeReferenceTag
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (environment : model.Environment)
    {shape : CShape} (input : CInputRef pre shape)
    (body : shape.Value → Circuit model pre post allowAllocation)
    (natural : ∀ value {Reference Tag : Register} {H : Type} [Fintype H]
      (state : State pre (Tag.prod Reference) (model.HiddenState × H)),
      (body value).execute environment Reference (State.decodeOracleTag state) =
        State.decodeExecutionTag ((body value).execute environment (Tag.prod Reference) state))
    {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State pre (Tag.prod Reference) (model.HiddenState × H)) :
    (Circuit.branch input body).execute environment Reference (State.decodeOracleTag state) =
      State.decodeExecutionTag
        ((Circuit.branch input body).execute environment (Tag.prod Reference) state) := by
  have component (selected : shape.Value) :
      ((body selected).execute environment Reference
        ((State.decodeOracleTag state).selectClassical
          (fun record => record.1.read input) selected)).mapHistory
            (fun record => (record.1, (record.2.1,
              (⟨selected, record.2.2⟩ : (Circuit.branch input body).Path)))) =
        State.decodeExecutionTag
          (((body selected).execute environment (Tag.prod Reference)
            (state.selectClassical (fun record => record.1.read input) selected)).mapHistory
              (fun record => (record.1, (record.2.1,
                (⟨selected, record.2.2⟩ : (Circuit.branch input body).Path))))) := by
    have selectedNatural := natural selected
      (state.selectClassical (fun record => record.1.read input) selected)
    rw [State.decodeOracleTag_selectClassical state
      (fun store => store.read input) selected] at selectedNatural
    have recorded := congrArg
      (fun current : State post Reference
          (model.HiddenState × ((H × Tag.Index) × (body selected).Path)) =>
        current.mapHistory (fun record => (record.1, (record.2.1,
          (⟨selected, record.2.2⟩ : (Circuit.branch input body).Path))))) selectedNatural
    exact recorded.trans (State.decodeExecutionTag_mapPath
      ((body selected).execute environment (Tag.prod Reference)
        (state.selectClassical (fun record => record.1.read input) selected))
      (fun result => (⟨selected, result⟩ : (Circuit.branch input body).Path))).symm
  apply ExecutionState.ext
  rintro ⟨store, hidden, ⟨history, tag⟩, path⟩
  apply DensityOperator.ext
  ext row column
  rw [execute_branch_block_matrix, State.decodeExecutionTag_entry, execute_branch_block_matrix]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro selected _
  have entry := congrArg
    (fun current : State post Reference
        (model.HiddenState × ((H × Tag.Index) × (Circuit.branch input body).Path)) =>
      (current.block (store, (hidden, ((history, tag), path)))).matrix row column)
    (component selected)
  exact entry.trans (State.decodeExecutionTag_entry _
    store hidden history tag path row column)

/-- Actual finite iteration retains every tag slice through the full dependent path vector. -/
lemma iterate_decodeReferenceTag
    {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
    (environment : model.Environment)
    (body : Circuit model ctx ctx allowAllocation)
    (natural : ∀ {Reference Tag : Register} {H : Type} [Fintype H]
      (state : State ctx (Tag.prod Reference) (model.HiddenState × H)),
      body.execute environment Reference (State.decodeOracleTag state) =
        State.decodeExecutionTag (body.execute environment (Tag.prod Reference) state))
    (count : Nat) {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State ctx (Tag.prod Reference) (model.HiddenState × H)) :
    (Circuit.iterate count body).execute environment Reference (State.decodeOracleTag state) =
      State.decodeExecutionTag
        ((Circuit.iterate count body).execute environment (Tag.prod Reference) state) := by
  induction count generalizing H with
  | zero =>
      rw [execute_iterate_zero, execute_iterate_zero]
      simp only [State.decodeExecutionTag, State.decodeOracleTag,
        State.decodeReferenceTag_mapHistory, State.mapHistory_comp, Function.comp_def]
      rfl
  | succ count ih =>
      rw [execute_iterate_succ, natural state]
      simp only [State.decodeExecutionTag]
      rw [(Circuit.iterate count body).execute_mapHistory environment Reference
        (State.decodeOracleTag (body.execute environment (Tag.prod Reference) state))
        (State.tagOutcomeExchange H Tag.Index body.Path).symm]
      rw [ih (body.execute environment (Tag.prod Reference) state), execute_iterate_succ]
      have regroup := State.decodeOracleTag_mapHistory
        ((Circuit.iterate count body).execute environment (Tag.prod Reference)
          (body.execute environment (Tag.prod Reference) state))
        (fun history : (H × body.Path) × (Fin count → body.Path) =>
          (history.1.1, Fin.cons (α := fun _ : Fin (count + 1) => body.Path)
            history.1.2 history.2))
      rw [regroup]
      simp only [State.decodeExecutionTag, State.mapHistory_comp, State.tagOutcomeExchange,
        Function.comp_def, Equiv.coe_fn_symm_mk]

end Circuit

end

end QuantumAlg
