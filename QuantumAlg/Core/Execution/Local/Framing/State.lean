/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Core.Execution.Context.Union.State.Laws
import all QuantumAlg.Core.Execution.Context.Union.Unitary.State
import all QuantumAlg.Core.Execution.Context.Union.Measurement.State
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Complete execution correctness of local circuit framing

The emitted circuit is interpreted by the existing interpreter. Exact
coordinates retain the full right classical store, every actual path, and
the complete quantum/reference matrix. Sequential composition and iteration
reassociate records; a stored-value branch selects and sums its actual
input fibers. No independence assumption on either frame is used
[dW19, qcnotes.tex:389,5381,5394,5405,5409].
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The complete-state diagram for an existing local circuit and its actual compilation. -/
def FramingNatural {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) : Prop :=
  ∀ (frame : RuntimeCtx model.kind) (separate : RuntimeCtx.StorageDisjoint pre frame)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State (pre.disjointUnion frame separate) Reference (model.HiddenState × H)),
    splitServiceState post frame (localPostDisjoint code supported frame separate)
        ((frameLocal code supported frame separate).execute Reference state) =
      (code.execute (Register.prod frame.register Reference)
        (splitServiceState pre frame separate state)).mapHistory
          (fun record => (record.1, (record.2.1.1,
            (record.2.1.2, frameLocalPathEquiv code supported frame separate record.2.2))))

private theorem framing_seq {model : ExecutionModel} {pre mid post : RuntimeCtx model.kind}
    (first : Circuit model pre mid) (second : Circuit model mid post)
    (supported : (first.seq second).IsLocal)
    (firstNatural : FramingNatural first supported.1)
    (secondNatural : FramingNatural second supported.2) :
    FramingNatural (first.seq second) supported := by
  intro frame separate Reference H _ state
  let middleSeparate := localPostDisjoint first supported.1 frame separate
  let finalSeparate := localPostDisjoint second supported.2 frame middleSeparate
  let compiledFirst := frameLocal first supported.1 frame separate
  let compiledSecond := frameLocal second supported.2 frame middleSeparate
  change splitServiceState post frame finalSeparate
      ((compiledSecond.execute Reference (compiledFirst.execute Reference state)).mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))) =
    ((first.seq second).execute (Register.prod frame.register Reference)
      (splitServiceState pre frame separate state)).mapHistory _
  erw [contextUnion_splitServiceState_mapHistory post frame finalSeparate
    (compiledSecond.execute Reference (compiledFirst.execute Reference state))
    (fun record : (H × compiledFirst.Path) × compiledSecond.Path =>
      (record.1.1, (record.1.2, record.2)))]
  erw [secondNatural frame middleSeparate Reference, firstNatural frame separate Reference]
  erw [Circuit.execute_mapHistory second (Register.prod frame.register Reference)
    (first.execute (Register.prod frame.register Reference)
      (splitServiceState pre frame separate state))
    (fun record : (Store frame × H) × first.Path =>
      (record.1.1, (record.1.2, frameLocalPathEquiv first supported.1 frame separate record.2)))]
  conv_rhs => rw [Circuit.execute_seq]
  simp only [State.mapHistory_comp, Function.comp_def, frameLocalPathEquiv]
  erw [State.mapHistory_comp]
  rfl

private theorem framing_branch {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {shape : CShape} (input : CInputRef pre shape) (body : shape.Value → Circuit model pre post)
    (supported : (Circuit.branch input body).IsLocal)
    (natural : ∀ value, FramingNatural (body value) (supported value)) :
    FramingNatural (.branch input body) supported := by
  intro frame separate Reference H _ state
  let code := Circuit.branch input body
  let compiled := frameLocal code supported frame separate
  let finalSeparate := localPostDisjoint code supported frame separate
  let localState := splitServiceState pre frame separate state
  let parts (value : shape.Value) :
      State (post.disjointUnion frame finalSeparate) Reference
        (model.HiddenState × (H × compiled.Path)) :=
    ((frameLocal (body value) (supported value) frame separate).execute Reference
      (state.selectClassical
        (fun record => record.1.read (inputLeft separate input)) value)).mapHistory
        (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
  let localParts (value : shape.Value) :
      State post (Register.prod frame.register Reference)
        (model.HiddenState × ((Store frame × H) × code.Path)) :=
    ((body value).execute (Register.prod frame.register Reference)
      (localState.selectClassical (fun record => record.1.read input) value)).mapHistory
        (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
  let historyMap : (model.HiddenState × ((Store frame × H) × code.Path)) →
      model.HiddenState × (Store frame × (H × compiled.Path)) :=
    fun record => (record.1, (record.2.1.1,
      (record.2.1.2, frameLocalPathEquiv code supported frame separate record.2.2)))
  have total : ∑ value, (parts value).mass ≤ 1 := by
    simp only [parts, State.mapHistory_mass, Circuit.execute_mass,
      ExecutionState.sum_selectClassical_mass]
    exact state.mass_le_one
  have localTotal : ∑ value, (localParts value).mass ≤ 1 := by
    simp only [localParts, State.mapHistory_mass, Circuit.execute_mass,
      ExecutionState.sum_selectClassical_mass]
    exact localState.mass_le_one
  have original : compiled.execute Reference state = ExecutionState.finiteSum parts total := by
    rfl
  have localOriginal : code.execute (Register.prod frame.register Reference) localState =
      ExecutionState.finiteSum localParts localTotal := by
    rfl
  have contribution (value : shape.Value) :
      splitServiceState post frame finalSeparate (parts value) =
        (localParts value).mapHistory historyMap := by
    dsimp only [parts, localParts]
    erw [contextUnion_splitServiceState_mapHistory post frame finalSeparate
      ((frameLocal (body value) (supported value) frame separate).execute Reference
        (state.selectClassical
          (fun record => record.1.read (inputLeft separate input)) value))
      (fun record : H × (frameLocal (body value) (supported value) frame separate).Path =>
        (record.1, (⟨value, record.2⟩ : compiled.Path)))]
    erw [natural value frame separate Reference, contextUnion_splitServiceState_selectClassical]
    simp only [State.mapHistory_comp, Function.comp_def]
    rfl
  have splitTotal :
      ∑ value, (splitServiceState post frame finalSeparate (parts value)).mass ≤ 1 := by
    simpa only [contextUnion_splitServiceState_mass] using total
  have mappedTotal : ∑ value, ((localParts value).mapHistory historyMap).mass ≤ 1 := by
    simpa only [State.mapHistory_mass] using localTotal
  calc
    splitServiceState post frame finalSeparate (compiled.execute Reference state) =
        splitServiceState post frame finalSeparate (ExecutionState.finiteSum parts total) :=
      congrArg (splitServiceState post frame finalSeparate) original
    _ = ExecutionState.finiteSum
        (fun value => splitServiceState post frame finalSeparate (parts value)) splitTotal :=
      contextUnion_splitServiceState_finiteSum post frame finalSeparate parts total
    _ = ExecutionState.finiteSum
        (fun value => (localParts value).mapHistory historyMap) mappedTotal := by
      apply ExecutionState.ext
      intro label
      apply DensityOperator.ext
      simp only [ExecutionState.finiteSum_block_matrix]
      exact Finset.sum_congr rfl fun value _ =>
        congrArg (fun output => (output.block label).matrix) (contribution value)
    _ = State.mapHistory (ExecutionState.finiteSum localParts localTotal) historyMap := by
      convert (ExecutionState.mapClassical_finiteSum localParts localTotal
        (fun record => (record.1, historyMap record.2))).symm using 1 <;>
        dsimp only [State.mapHistory] <;>
        congr! 2
      apply ExecutionState.ext
      intro label
      apply DensityOperator.ext
      simp only [ExecutionState.finiteSum, ExecutionState.mapClassical_block_matrix]
      apply Finset.sum_congr rfl
      intro index _
      apply Finset.sum_congr rfl
      intro entry _
      split_ifs <;> rfl
    _ = (code.execute (Register.prod frame.register Reference) localState).mapHistory historyMap :=
      congrArg (fun output => output.mapHistory historyMap) localOriginal.symm

set_option maxHeartbeats 400000 in
-- Normalizing the full frame, service and iteration histories exceeded the default budget.
private theorem framing_iterate {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (body : Circuit model ctx ctx) (supported : body.IsLocal)
    (natural : FramingNatural body supported)
    (count : Nat) : FramingNatural (.iterate count body) supported := by
  intro frame separate Reference H _ state
  induction count generalizing H with
  | zero =>
      change splitServiceState ctx frame separate
          (state.mapHistory (fun history => (history.1, (history.2, Fin.elim0)))) =
        ((splitServiceState ctx frame separate state).mapHistory
          (fun history => (history.1, (history.2, (Fin.elim0 : Fin 0 → body.Path))))).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, fun index =>
              frameLocalPathEquiv body supported frame separate (record.2.2 index)))))
      erw [contextUnion_splitServiceState_mapHistory ctx frame separate state
        (fun history : H =>
          (history, (Fin.elim0 : Fin 0 → (frameLocal body supported frame separate).Path)))]
      simp only [State.mapHistory_comp, Function.comp_def]
      congr 1
      funext record
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      let compiledBody := frameLocal body supported frame separate
      let afterFirst := compiledBody.execute Reference state
      let remaining := (Circuit.iterate count compiledBody).execute Reference afterFirst
      change splitServiceState ctx frame separate
          (remaining.mapHistory (fun record =>
            (record.1, (record.2.1.1, Fin.cons
              (α := fun _ : Fin (count + 1) => compiledBody.Path) record.2.1.2 record.2.2)))) =
        ((Circuit.iterate (count + 1) body).execute (Register.prod frame.register Reference)
          (splitServiceState ctx frame separate state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, fun index =>
              frameLocalPathEquiv body supported frame separate (record.2.2 index)))))
      have splitRemaining := contextUnion_splitServiceState_mapHistory ctx frame separate
        remaining
        (fun record : (H × compiledBody.Path) × (Fin count → compiledBody.Path) =>
          (record.1.1, Fin.cons (α := fun _ : Fin (count + 1) => compiledBody.Path)
            record.1.2 record.2))
      erw [splitRemaining]
      conv_lhs => erw [ih (state := afterFirst), natural frame separate Reference state]
      conv_lhs => erw [Circuit.execute_mapHistory (Circuit.iterate count body)
        (Register.prod frame.register Reference)
        (body.execute (Register.prod frame.register Reference)
          (splitServiceState ctx frame separate state))
        (fun record : (Store frame × H) × body.Path =>
          (record.1.1,
            (record.1.2, frameLocalPathEquiv body supported frame separate record.2)))]
      conv_rhs => erw [Circuit.execute_iterate_succ]
      simp only [State.mapHistory_comp, Function.comp_def]
      erw [State.mapHistory_comp]
      congr 1
      funext record
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext index
      exact Fin.cases rfl (fun tail => rfl) index

/-- The existing interpreter commutes with actual local framing on the complete state. -/
theorem frameLocal_execute {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) : FramingNatural code supported := by
  induction code with
  | id ctx =>
      intro frame separate Reference H _ state
      change splitServiceState ctx frame separate
          (state.skip.mapHistory (fun record => (record.1.1, (record.1.2, record.2)))) =
        ((splitServiceState ctx frame separate state).skip.mapHistory
          (fun record => (record.1.1, (record.1.2, record.2)))).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))
      dsimp only [splitServiceState, State.skip]
      simp only [State.mapHistory_comp, Function.comp_def]
      rw [contextUnion_splitState_mapHistory]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | classical | classicalQuery | retain | prepareZero | workspace =>
      exact False.elim supported
  | @unitary gates oracles ctx operations services program =>
      intro frame separate Reference H _ state
      exact contextUnion_splitServiceState_unitary
        (operations := operations) (services := services) ctx frame separate program state
  | @measureZ gates oracles ctx operations services wire output =>
      intro frame separate Reference H _ state
      exact contextUnion_splitServiceState_measureZ (gates := gates) (oracles := oracles)
        (operations := operations) (services := services) ctx frame separate state wire output
  | seq first second firstIH secondIH =>
      exact framing_seq first second supported (firstIH supported.1) (secondIH supported.2)
  | branch input body bodyIH =>
      exact framing_branch input body supported (fun value => bodyIH value (supported value))
  | iterate count body bodyIH =>
      exact framing_iterate body supported (bodyIH supported) count

end

end QuantumAlg.Execution.ContextUnion
