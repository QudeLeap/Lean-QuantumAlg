/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.Measurement
import all QuantumAlg.Core.Execution.Context.Relabeling.Unitary.State
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Complete local execution under injective placement

The actual rebuilt circuit preserves every complete state block under the
complete store and wire bijections and finite path correspondence. Sequential execution,
stored-value selection and finite iteration use the existing interpreter.
All statements allow arbitrary joint inputs and external references.
-/

namespace QuantumAlg.Execution.ContextRelabeling

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
def Natural {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal) : Prop :=
  ∀ (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (Reference : Register) {H : Type} [Fintype H] (original : State pre Reference H),
    (localCircuit code supported keys physical).execute Reference (state keys physical original) =
      (state keys physical (code.execute Reference original)).mapHistory
        (fun record => (record.1, localPathEquiv code supported keys physical record.2))

private theorem natural_seq {kind : ProblemKind} {pre mid post : RuntimeCtx kind}
    (first : Circuit pre mid) (second : Circuit mid post)
    (supported : (first.seq second).IsLocal)
    (firstNatural : Natural first supported.1) (secondNatural : Natural second supported.2) :
    Natural (first.seq second) supported := by
  intro keys physical Reference H _ original
  let compiledFirst := localCircuit first supported.1 keys physical
  let compiledSecond := localCircuit second supported.2 keys physical
  change ((compiledSecond.execute Reference
      (compiledFirst.execute Reference (state keys physical original))).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2)))) =
    (state keys physical ((first.seq second).execute Reference original)).mapHistory _
  rw [firstNatural keys physical Reference, Circuit.execute_mapHistory,
    secondNatural keys physical Reference, Circuit.execute_seq, state_mapHistory]
  simp only [State.mapHistory_comp, Function.comp_def, localPathEquiv]
  erw [State.mapHistory_comp]
  rfl

private theorem natural_branch {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {shape : CShape} (ref : CInputRef pre shape) (body : shape.Value → Circuit pre post)
    (supported : (Circuit.branch ref body).IsLocal)
    (natural : ∀ value, Natural (body value) (supported value)) :
    Natural (.branch ref body) supported := by
  intro keys physical Reference H _ original
  let code := Circuit.branch ref body
  let compiled := localCircuit code supported keys physical
  let parts (value : shape.Value) : State pre Reference H :=
    original.selectClassical (fun record => record.1.read ref) value
  let originalParts (value : shape.Value) : State post Reference (H × code.Path) :=
    ((body value).execute Reference (parts value)).mapHistory
      (fun record => (record.1, ⟨value, record.2⟩))
  let targetParts (value : shape.Value) :
      State (post.relabel keys physical) Reference (H × compiled.Path) :=
    ((localCircuit (body value) (supported value) keys physical).execute Reference
      ((state keys physical original).selectClassical
        (fun record => record.1.read (input keys physical ref)) value)).mapHistory
          (fun record => (record.1, ⟨value, record.2⟩))
  let histories := fun record : H × code.Path =>
    (record.1, localPathEquiv code supported keys physical record.2)
  have originalTotal : ∑ value, (originalParts value).mass ≤ 1 := by
    simp only [originalParts, parts, State.mapHistory_mass, Circuit.execute_mass,
      ExecutionState.sum_selectClassical_mass]
    exact original.mass_le_one
  have targetTotal : ∑ value, (targetParts value).mass ≤ 1 := by
    simp only [targetParts, State.mapHistory_mass, Circuit.execute_mass,
      ExecutionState.sum_selectClassical_mass]
    exact (state keys physical original).mass_le_one
  have contribution (value : shape.Value) :
      targetParts value = (state keys physical (originalParts value)).mapHistory histories := by
    dsimp only [targetParts, originalParts]
    rw [← state_selectClassical, natural value keys physical Reference, state_mapHistory]
    simp only [State.mapHistory_comp, Function.comp_def]
    rfl
  change ExecutionState.finiteSum targetParts targetTotal =
    (state keys physical (ExecutionState.finiteSum originalParts originalTotal)).mapHistory
      histories
  rw [state_finiteSum]
  have transformedTotal : ∑ value, (state keys physical (originalParts value)).mass ≤ 1 := by
    simpa only [state_mass] using originalTotal
  have mappedTotal :
      ∑ value, ((state keys physical (originalParts value)).mapHistory histories).mass ≤ 1 := by
    simpa only [State.mapHistory_mass] using transformedTotal
  calc
    ExecutionState.finiteSum targetParts targetTotal =
        ExecutionState.finiteSum
          (fun value => (state keys physical (originalParts value)).mapHistory histories)
          mappedTotal := by
      apply ExecutionState.ext
      intro label
      apply DensityOperator.ext
      simp only [ExecutionState.finiteSum_block_matrix]
      exact Finset.sum_congr rfl fun value _ =>
        congrArg (fun output => (output.block label).matrix) (contribution value)
    _ = State.mapHistory (ExecutionState.finiteSum
        (fun value => state keys physical (originalParts value)) transformedTotal) histories := by
      convert (ExecutionState.mapClassical_finiteSum
        (fun value => state keys physical (originalParts value)) transformedTotal
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

private theorem natural_iterate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (body : Circuit ctx ctx) (supported : body.IsLocal) (natural : Natural body supported)
    (count : Nat) : Natural (.iterate count body) supported := by
  intro keys physical Reference H _ original
  induction count generalizing H with
  | zero =>
      change ((state keys physical original).mapHistory (fun history => (history, Fin.elim0))) =
        (state keys physical (original.mapHistory
          (fun history => (history, Fin.elim0)))).mapHistory _
      erw [state_mapHistory, State.mapHistory_comp]
      congr 1
      funext history
      apply Prod.ext
      · rfl
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      let compiledBody := localCircuit body supported keys physical
      change ((Circuit.iterate (count + 1) compiledBody).execute Reference
        (state keys physical original)) =
        (state keys physical
          ((Circuit.iterate (count + 1) body).execute Reference original)).mapHistory
          (fun record => (record.1, fun index =>
            localPathEquiv body supported keys physical (record.2 index)))
      erw [Circuit.execute_iterate_succ, natural keys physical Reference,
        Circuit.execute_mapHistory, ih]
      conv_rhs => rw [Circuit.execute_iterate_succ]
      have reassociate := state_mapHistory keys physical
        ((Circuit.iterate count body).execute Reference (body.execute Reference original))
        (fun history : (H × body.Path) × (Fin count → body.Path) =>
          (history.1.1, Fin.cons (α := fun _ : Fin (count + 1) => body.Path)
            history.1.2 history.2))
      erw [reassociate]
      simp only [State.mapHistory_comp, Function.comp_def]
      repeat' erw [State.mapHistory_comp]
      congr 1
      funext record
      apply Prod.ext
      · rfl
      funext index
      exact Fin.cases rfl (fun tail => rfl) index

/-- The existing interpreter commutes with the actual local injective-placement compiler. -/
theorem localCircuit_execute {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal) : Natural code supported := by
  induction code with
  | id ctx =>
      intro keys physical Reference H _ original
      change (state keys physical original).skip = (state keys physical original.skip).mapHistory id
      rw [← state_mapHistory]
      change (state keys physical original).skip =
        state keys physical ((original.mapHistory (fun history => (history, ()))).mapHistory id)
      rw [State.mapHistory_comp]
      exact (state_mapHistory keys physical original (fun history => (history, ()))).symm
  | classical | declaredCall | randomBits | retain | prepare | workspace =>
      exact False.elim supported
  | @unitary ctx program placed =>
      intro keys physical Reference H _ original
      change (state keys physical original).unitary
        (unitaryProgram ctx keys physical program placed) =
        (state keys physical (original.unitary program)).mapHistory id
      rw [history_id]
      exact (state_unitary keys physical program placed original).symm
  | measureZ wire output =>
      intro keys physical Reference H _ original
      exact (state_measureZ _ keys physical wire original output).symm
  | seq first second firstIH secondIH =>
      exact natural_seq first second supported (firstIH supported.1) (secondIH supported.2)
  | branch ref body bodyIH =>
      exact natural_branch ref body supported (fun value => bodyIH value (supported value))
  | iterate count body bodyIH =>
      exact natural_iterate body supported (bodyIH supported) count

end

end QuantumAlg.Execution.ContextRelabeling
