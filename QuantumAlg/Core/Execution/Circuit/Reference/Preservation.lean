/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.OwnedLayoutView.Laws

import all QuantumAlg.Core.Execution.Composition.Reference.Preservation
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# No signalling to the complete external reference

Every fixed-context circuit preserves the original reference density operator
when all actual outcomes are summed. The proof follows the existing closed
interpreter, including actual service transitions, physical embeddings and
parallel composition. It permits arbitrary entanglement and correlations with
classical storage; it does not condition on a successful path
[dW19, qcnotes.tex:5381,5405,5409,6827].
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

attribute [local instance] Classical.decEq

private lemma referenceMarginal_map_decisions
    {C D : Type} [Fintype C] [Fintype D] {R Reference : Register}
    {decision : DecidableEq D} (state : ExecutionState C (R.prod Reference))
    (read : C → D) :
    (@ExecutionState.mapClassical C D _ _ _ decision state read).referenceMarginal =
      state.referenceMarginal :=
  @ExecutionState.mapClassical_referenceMarginal C D _ _ decision R Reference state read

private lemma branch_referenceMarginal {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit model pre post allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (preserves : ∀ value {H : Type} [Fintype H]
      (state : State pre Reference (model.HiddenState × H)),
      ((body value).execute environment Reference state).referenceMarginal =
        state.referenceMarginal)
    {H : Type} [Fintype H] (state : State pre Reference (model.HiddenState × H)) :
    ((Circuit.branch input body).execute environment Reference state).referenceMarginal =
      state.referenceMarginal := by
  let family (value : shape.Value) : State post Reference
      (model.HiddenState × (H × (Circuit.branch input body).Path)) :=
    ((body value).execute environment Reference
      (state.selectClassical (fun record => record.1.read input) value)).mapHistory
        (fun history => (history.1, (history.2.1, ⟨value, history.2.2⟩)))
  have bounded : ∑ value, (family value).mass ≤ 1 := by
    simp only [family, State.mapHistory_mass, execute_mass]
    exact state.sum_selectClassical_mass_le_one (fun record => record.1.read input)
  have actual : (Circuit.branch input body).execute environment Reference state =
      ExecutionState.finiteSum family bounded := by
    rfl
  apply DensityOperator.ext
  ext row column
  rw [actual, ExecutionState.referenceMarginal_finiteSum_entry]
  simp only [family, State.mapHistory_referenceMarginal, preserves]
  exact ExecutionState.sum_referenceMarginal_selectClassical state
    (fun record => record.1.read input) row column

private lemma iterate_referenceMarginal {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
    (body : Circuit model ctx ctx allowAllocation) (environment : model.Environment)
    (Reference : Register)
    (preserves : ∀ {H : Type} [Fintype H]
      (state : State ctx Reference (model.HiddenState × H)),
      (body.execute environment Reference state).referenceMarginal = state.referenceMarginal)
    (count : Nat) {H : Type} [Fintype H]
    (state : State ctx Reference (model.HiddenState × H)) :
    ((Circuit.iterate count body).execute environment Reference state).referenceMarginal =
      state.referenceMarginal := by
  induction count generalizing H with
  | zero =>
      rw [execute_iterate_zero, State.mapHistory_referenceMarginal]
  | succ count ih =>
      rw [execute_iterate_succ, State.mapHistory_referenceMarginal, ih, preserves]

private lemma execute_referenceMarginal_of_fixed {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (environment : model.Environment)
    (fixed : allowAllocation = false)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × H)) :
    (code.execute environment Reference state).referenceMarginal = state.referenceMarginal := by
  induction code generalizing Reference H with
  | id ctx =>
      rw [execute_id, referenceMarginal_map_decisions]
  | classical application =>
      rw [execute_classical, ExecutionState.mapClassical_referenceMarginal,
        ExecutionState.referenceMarginal_kernelChoice]
  | classicalQuery application =>
      rw [execute_classicalQuery]
      dsimp only [queryStep]
      rw [ExecutionState.mapClassical_referenceMarginal,
        ExecutionState.referenceMarginal_kernelChoice]
  | unitary program =>
      rw [execute_unitary, referenceMarginal_map_decisions,
        ExecutionState.referenceMarginal_applyLocalUnitary]
  | measureZ wire output =>
      rw [execute_measureZ, referenceMarginal_map_decisions,
        ExecutionState.referenceMarginal_measureZ]
  | retain | prepareZero | workspace => cases fixed
  | seq first second firstIH secondIH =>
      rw [execute_seq, State.mapHistory_referenceMarginal,
        secondIH environment fixed, firstIH environment fixed]
  | branch input body bodyIH =>
      exact branch_referenceMarginal input body environment Reference
        (fun value {_} _ original => bodyIH value environment fixed original) state
  | iterate count body bodyIH =>
      exact iterate_referenceMarginal body environment Reference
        (fun {_} _ original => bodyIH environment fixed original) count state
  | embed placement body bodyIH =>
      exact embedPreserving_referenceMarginal placement Reference
        (fun {_} _ original => interpret body environment _ original)
        (fun {_} _ original => bodyIH environment rfl original) state
  | ownedLayoutView view body bodyIH =>
      change (view.join
        (body.execute environment Reference (view.split state))).referenceMarginal = _
      rw [view.join_referenceMarginal, bodyIH environment rfl, view.split_referenceMarginal]
  | parallelClassical join separate first second firstIH secondIH =>
      exact parallelPreserving_referenceMarginal join separate
        (fun {_} _ original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun {_} _ original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (fun {_} _ original => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ rfl original)
        (fun {_} _ original => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ rfl original) state
  | parallelQuantum join separate first second firstIH secondIH =>
      exact parallelPreserving_referenceMarginal join separate
        (fun {_} _ original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun {_} _ original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (fun {_} _ original => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ rfl original)
        (fun {_} _ original => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ rfl original) state

/-- Fixed-context execution cannot signal to an arbitrary entangled external reference. -/
lemma execute_referenceMarginal {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post false)
    (environment : model.Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × H)) :
    (code.execute environment Reference state).referenceMarginal = state.referenceMarginal :=
  execute_referenceMarginal_of_fixed code environment rfl state

end

end QuantumAlg.Circuit
