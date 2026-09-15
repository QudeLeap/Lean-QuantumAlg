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
def FramingNatural {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal) : Prop :=
  ∀ (frame : RuntimeCtx kind) (separate : RuntimeCtx.StorageDisjoint pre frame)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State (pre.disjointUnion frame separate) Reference H),
    splitState post frame (localPostDisjoint code supported frame separate)
        ((frameLocal code supported frame separate).execute Reference state) =
      (code.execute (Register.prod frame.register Reference)
        (splitState pre frame separate state)).mapHistory
          (fun record => (record.1.1,
            (record.1.2, frameLocalPathEquiv code supported frame separate record.2)))

private theorem framing_seq {kind : ProblemKind} {pre mid post : RuntimeCtx kind}
    (first : Circuit pre mid) (second : Circuit mid post)
    (supported : (first.seq second).IsLocal)
    (firstNatural : FramingNatural first supported.1)
    (secondNatural : FramingNatural second supported.2) :
    FramingNatural (first.seq second) supported := by
  intro frame separate Reference H _ state
  let middleSeparate := localPostDisjoint first supported.1 frame separate
  let finalSeparate := localPostDisjoint second supported.2 frame middleSeparate
  let compiledFirst := frameLocal first supported.1 frame separate
  let compiledSecond := frameLocal second supported.2 frame middleSeparate
  change splitState post frame finalSeparate
      ((compiledSecond.execute Reference (compiledFirst.execute Reference state)).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2)))) =
    ((first.seq second).execute (Register.prod frame.register Reference)
      (splitState pre frame separate state)).mapHistory _
  rw [contextUnion_splitState_mapHistory,
    secondNatural frame middleSeparate Reference,
    firstNatural frame separate Reference, Circuit.execute_mapHistory,
    Circuit.execute_seq]
  simp only [State.mapHistory_comp, Function.comp_def, frameLocalPathEquiv]
  erw [State.mapHistory_comp]
  rfl

private theorem framing_branch {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef pre shape) (body : shape.Value → Circuit pre post)
    (supported : (Circuit.branch input body).IsLocal)
    (natural : ∀ value, FramingNatural (body value) (supported value)) :
    FramingNatural (.branch input body) supported := by
  intro frame separate Reference H _ state
  let code := Circuit.branch input body
  let compiled := frameLocal code supported frame separate
  let finalSeparate := localPostDisjoint code supported frame separate
  let localState := splitState pre frame separate state
  let parts (value : shape.Value) :
      State (post.disjointUnion frame finalSeparate) Reference (H × compiled.Path) :=
    ((frameLocal (body value) (supported value) frame separate).execute Reference
      (state.selectClassical
        (fun record => record.1.read (inputLeft separate input)) value)).mapHistory
        (fun record => (record.1, ⟨value, record.2⟩))
  let localParts (value : shape.Value) :
      State post (Register.prod frame.register Reference) ((Store frame × H) × code.Path) :=
    ((body value).execute (Register.prod frame.register Reference)
      (localState.selectClassical (fun record => record.1.read input) value)).mapHistory
        (fun record => (record.1, ⟨value, record.2⟩))
  let historyMap : ((Store frame × H) × code.Path) → Store frame × (H × compiled.Path) :=
    fun record => (record.1.1,
      (record.1.2, frameLocalPathEquiv code supported frame separate record.2))
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
      splitState post frame finalSeparate (parts value) =
        (localParts value).mapHistory historyMap := by
    dsimp only [parts, localParts]
    rw [contextUnion_splitState_mapHistory, natural value frame separate Reference,
      contextUnion_splitState_selectClassical]
    simp only [State.mapHistory_comp, Function.comp_def]
    rfl
  have splitTotal : ∑ value, (splitState post frame finalSeparate (parts value)).mass ≤ 1 := by
    simpa only [contextUnion_splitState_mass] using total
  have mappedTotal : ∑ value, ((localParts value).mapHistory historyMap).mass ≤ 1 := by
    simpa only [State.mapHistory_mass] using localTotal
  calc
    splitState post frame finalSeparate (compiled.execute Reference state) =
        splitState post frame finalSeparate (ExecutionState.finiteSum parts total) :=
      congrArg (splitState post frame finalSeparate) original
    _ = ExecutionState.finiteSum
        (fun value => splitState post frame finalSeparate (parts value)) splitTotal :=
      contextUnion_splitState_finiteSum post frame finalSeparate parts total
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

private theorem framing_iterate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (body : Circuit ctx ctx) (supported : body.IsLocal) (natural : FramingNatural body supported)
    (count : Nat) : FramingNatural (.iterate count body) supported := by
  intro frame separate Reference H _ state
  induction count generalizing H with
  | zero =>
      change splitState ctx frame separate
          (state.mapHistory (fun history => (history, Fin.elim0))) =
        ((splitState ctx frame separate state).mapHistory
          (fun history => (history, Fin.elim0))).mapHistory _
      erw [contextUnion_splitState_mapHistory, State.mapHistory_comp]
      congr 1
      funext record
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      let compiledBody := frameLocal body supported frame separate
      change splitState ctx frame separate
          ((Circuit.iterate (count + 1) compiledBody).execute Reference state) = _
      erw [Circuit.execute_iterate_succ, contextUnion_splitState_mapHistory,
        ih, natural frame separate Reference,
        Circuit.execute_mapHistory, Circuit.execute_iterate_succ]
      simp only [State.mapHistory_comp, Function.comp_def]
      erw [State.mapHistory_comp]
      congr 1
      funext record
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext index
      exact Fin.cases rfl (fun tail => rfl) index

/-- The existing interpreter commutes with actual local framing on the complete state. -/
theorem frameLocal_execute {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal) : FramingNatural code supported := by
  induction code with
  | id ctx =>
      intro frame separate Reference H _ state
      exact contextUnion_splitState_skip ctx frame separate state
  | classical | declaredCall | randomBits | retain | prepare | workspace =>
      exact False.elim supported
  | unitary program placed =>
      intro frame separate Reference H _ state
      exact contextUnion_splitState_unitary _ frame separate program placed state
  | measureZ wire output =>
      intro frame separate Reference H _ state
      exact contextUnion_splitState_measureZ _ frame separate state wire output
  | seq first second firstIH secondIH =>
      exact framing_seq first second supported (firstIH supported.1) (secondIH supported.2)
  | branch input body bodyIH =>
      exact framing_branch input body supported (fun value => bodyIH value (supported value))
  | iterate count body bodyIH =>
      exact framing_iterate body supported (bodyIH supported) count

end

end QuantumAlg.Execution.ContextUnion
