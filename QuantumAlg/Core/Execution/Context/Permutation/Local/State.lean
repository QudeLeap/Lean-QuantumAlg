/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.Measurement
import all QuantumAlg.Core.Execution.Context.Permutation.Unitary.State
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Complete local execution under entry permutation

The actual rebuilt circuit preserves every complete state block under the
original entry bijections and finite path correspondence. Sequential execution,
stored-value selection and finite iteration use the existing interpreter.
All statements allow arbitrary joint inputs and external references.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem history_id {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H : Type} [Fintype H] (original : State ctx Reference H) :
    original.mapHistory id = original := by
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  simp only [State.mapHistory, ExecutionState.mapClassical_block_matrix, id_eq, Prod.eta,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Exact complete-state correspondence for the actual local compiler. -/
def Natural {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) : Prop :=
  ∀ (target : RuntimeCtx model.kind) (same : pre.entries.Perm target.entries)
    (Reference : Register) {H : Type} [Fintype H]
    (original : State pre Reference (model.HiddenState × H)),
    (localCircuit code supported target same).execute Reference (state same original) =
      (state (postPermutation code supported same) (code.execute Reference original)).mapHistory
        (fun record =>
          (record.1, (record.2.1, localPathEquiv code supported target same record.2.2)))

set_option maxHeartbeats 400000 in
-- Composing the model-indexed history transports exceeded the default 200000-step budget.
private theorem natural_seq {model : ExecutionModel} {pre mid post : RuntimeCtx model.kind}
    (first : Circuit model pre mid) (second : Circuit model mid post)
    (supported : (first.seq second).IsLocal)
    (firstNatural : Natural first supported.1) (secondNatural : Natural second supported.2) :
    Natural (first.seq second) supported := by
  intro target same Reference H _ original
  let middleSame := postPermutation first supported.1 same
  let finalSame := postPermutation second supported.2 middleSame
  let compiledFirst := localCircuit first supported.1 target same
  let compiledSecond := localCircuit second supported.2 target middleSame
  change ((compiledSecond.execute Reference
      (compiledFirst.execute Reference (state same original))).mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))) =
    (state finalSame ((first.seq second).execute Reference original)).mapHistory _
  rw [firstNatural target same Reference]
  erw [Circuit.execute_mapHistory compiledSecond Reference
    (state middleSame (first.execute Reference original))
    (fun record : H × first.Path =>
      (record.1, localPathEquiv first supported.1 target same record.2))]
  erw [secondNatural target middleSame Reference]
  conv_rhs => erw [Circuit.execute_seq, state_mapHistory]
  simp only [State.mapHistory_comp, Function.comp_def, localPathEquiv]
  erw [State.mapHistory_comp]
  rfl

private theorem natural_branch {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {shape : CShape} (ref : CInputRef pre shape) (body : shape.Value → Circuit model pre post)
    (supported : (Circuit.branch ref body).IsLocal)
    (natural : ∀ value, Natural (body value) (supported value)) :
    Natural (.branch ref body) supported := by
  intro target same Reference H _ original
  let code := Circuit.branch ref body
  let compiled := localCircuit code supported target same
  let finalSame := postPermutation code supported same
  let parts (value : shape.Value) : State pre Reference (model.HiddenState × H) :=
    original.selectClassical (fun record => record.1.read ref) value
  let originalParts (value : shape.Value) :
      State post Reference (model.HiddenState × (H × code.Path)) :=
    ((body value).execute Reference (parts value)).mapHistory
      (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
  let targetParts (value : shape.Value) :
      State target Reference (model.HiddenState × (H × compiled.Path)) :=
    ((localCircuit (body value) (supported value) target same).execute Reference
      ((state same original).selectClassical
        (fun record => record.1.read (input same ref)) value)).mapHistory
          (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
  let histories := fun record : model.HiddenState × (H × code.Path) =>
    (record.1, (record.2.1, localPathEquiv code supported target same record.2.2))
  have originalTotal : ∑ value, (originalParts value).mass ≤ 1 := by
    simp only [originalParts, parts, State.mapHistory_mass, Circuit.execute_mass,
      ExecutionState.sum_selectClassical_mass]
    exact original.mass_le_one
  have targetTotal : ∑ value, (targetParts value).mass ≤ 1 := by
    simp only [targetParts, State.mapHistory_mass, Circuit.execute_mass,
      ExecutionState.sum_selectClassical_mass]
    exact (state same original).mass_le_one
  have contribution (value : shape.Value) :
      targetParts value = (state finalSame (originalParts value)).mapHistory histories := by
    dsimp only [targetParts, originalParts]
    rw [← state_selectClassical, natural value target same Reference, state_mapHistory]
    simp only [State.mapHistory_comp, Function.comp_def]
    rfl
  change ExecutionState.finiteSum targetParts targetTotal =
    (state finalSame (ExecutionState.finiteSum originalParts originalTotal)).mapHistory histories
  rw [state_finiteSum]
  have transformedTotal : ∑ value, (state finalSame (originalParts value)).mass ≤ 1 := by
    simpa only [state_mass] using originalTotal
  have mappedTotal :
      ∑ value, ((state finalSame (originalParts value)).mapHistory histories).mass ≤ 1 := by
    simpa only [State.mapHistory_mass] using transformedTotal
  calc
    ExecutionState.finiteSum targetParts targetTotal =
        ExecutionState.finiteSum
          (fun value => (state finalSame (originalParts value)).mapHistory histories)
          mappedTotal := by
      apply ExecutionState.ext
      intro label
      apply DensityOperator.ext
      simp only [ExecutionState.finiteSum_block_matrix]
      exact Finset.sum_congr rfl fun value _ =>
        congrArg (fun output => (output.block label).matrix) (contribution value)
    _ = State.mapHistory (ExecutionState.finiteSum
        (fun value => state finalSame (originalParts value)) transformedTotal) histories := by
      convert (ExecutionState.mapClassical_finiteSum
        (fun value => state finalSame (originalParts value)) transformedTotal
        (fun record => (record.1, histories record.2))).symm using 1 <;>
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

private theorem natural_iterate {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (body : Circuit model ctx ctx) (supported : body.IsLocal) (natural : Natural body supported)
    (count : Nat) : Natural (.iterate count body) supported := by
  intro target same Reference H _ original
  induction count generalizing H with
  | zero =>
      change ((state same original).mapHistory
        (fun history => (history.1, (history.2, Fin.elim0)))) =
        (state same (original.mapHistory
          (fun history => (history.1, (history.2, Fin.elim0))))).mapHistory _
      erw [state_mapHistory, State.mapHistory_comp]
      congr 1
      funext history
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      let compiledBody := localCircuit body supported target same
      change ((Circuit.iterate (count + 1) compiledBody).execute Reference
        (state same original)) =
        (state same ((Circuit.iterate (count + 1) body).execute Reference original)).mapHistory
          (fun record => (record.1, (record.2.1, fun index =>
            localPathEquiv body supported target same (record.2.2 index))))
      erw [Circuit.execute_iterate_succ, natural target same Reference]
      erw [Circuit.execute_mapHistory (Circuit.iterate count compiledBody) Reference
        (state same (body.execute Reference original))
        (fun record : H × body.Path =>
          (record.1, localPathEquiv body supported target same record.2))]
      erw [ih]
      conv_rhs => rw [Circuit.execute_iterate_succ]
      have reassociate := state_mapHistory same
        ((Circuit.iterate count body).execute Reference (body.execute Reference original))
        (fun history : model.HiddenState × ((H × body.Path) × (Fin count → body.Path)) =>
          (history.1, (history.2.1.1, Fin.cons (α := fun _ : Fin (count + 1) => body.Path)
            history.2.1.2 history.2.2)))
      erw [reassociate]
      simp only [State.mapHistory_comp, Function.comp_def]
      repeat' erw [State.mapHistory_comp]
      congr 1
      funext record
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext index
      exact Fin.cases rfl (fun tail => rfl) index

/-- The existing interpreter commutes with the actual local entry-permutation compiler. -/
theorem localCircuit_execute {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) : Natural code supported := by
  induction code with
  | id ctx =>
      intro target same Reference H _ original
      change ((state same original).skip.mapHistory
        (fun record => (record.1.1, (record.1.2, record.2)))) =
        (state same (original.skip.mapHistory
          (fun record => (record.1.1, (record.1.2, record.2))))).mapHistory id
      rw [history_id, state_mapHistory]
      change (((state same original).mapHistory (fun history => (history, ()))).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2)))) =
        (state same (original.mapHistory (fun history => (history, ())))).mapHistory _
      rw [state_mapHistory]
  | classical | classicalQuery | retain | prepareZero | workspace =>
      exact False.elim supported
  | @unitary gates oracles ctx operations services program =>
      intro target same Reference H _ original
      change (Circuit.unitary (operations := operations) (classicalOracles := services)
        (unitaryProgram same program)).execute Reference (state same original) =
        (state same ((Circuit.unitary (operations := operations)
          (classicalOracles := services) program).execute Reference original)).mapHistory id
      rw [history_id]
      exact (state_unitary (operations := operations) (services := services)
        same program original).symm
  | measureZ wire output =>
      intro target same Reference H _ original
      exact (state_measureZ same wire original output).symm
  | seq first second firstIH secondIH =>
      exact natural_seq first second supported (firstIH supported.1) (secondIH supported.2)
  | branch ref body bodyIH =>
      exact natural_branch ref body supported (fun value => bodyIH value (supported value))
  | iterate count body bodyIH =>
      exact natural_iterate body supported (bodyIH supported) count

end

end QuantumAlg.Execution.ContextPermutation
