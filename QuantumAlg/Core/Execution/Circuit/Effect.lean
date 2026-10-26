/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Effect
import all QuantumAlg.Core.Execution.Preparation.Effect
import all QuantumAlg.Core.Execution.Classical.Step.Effect
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Composition.Effect
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Interpret.Preserving
import all QuantumAlg.Core.Execution.Context.OwnedLayoutView.Effect

/-!
# Certified observations of the actual finite circuit

Backward observations use the same typed instruction syntax, model-owned
probabilities, real Store updates and finite path records as execution.
The persistent service state remains separate from mathematical history.
Every matrix constructed here is a positive contraction on the complete
live register and reference.
These are mathematical observations, not a second execution state or channel.
-/

namespace QuantumAlg

noncomputable section

namespace Circuit

open Execution

/-- One certified quantum observable for each complete actual classical record. -/
abbrev EffectFamily {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (Reference : Register) (History : Type) :=
  Store ctx × History → Effect (Register.prod ctx.register Reference)

private def repeatEffectPullback {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {Hidden Path : Type}
    (body : ∀ {History : Type},
      EffectFamily ctx Reference (Hidden × (History × Path)) →
        EffectFamily ctx Reference (Hidden × History)) :
    (count : Nat) → {History : Type} →
      EffectFamily ctx Reference (Hidden × (History × (Fin count → Path))) →
        EffectFamily ctx Reference (Hidden × History)
  | 0 => fun effects original => effects (original.1, (original.2.1, (original.2.2, Fin.elim0)))
  | count + 1 => fun effects =>
      body (repeatEffectPullback body count (fun result =>
        effects (result.1,
          (result.2.1, (result.2.2.1.1, Fin.cons result.2.2.1.2 result.2.2.2)))))

/-- Pull the final block observables backward through this same finite circuit syntax. -/
def effectPullback {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (environment : model.Environment)
    (Reference : Register) {History : Type}
    (effects : EffectFamily post Reference (model.HiddenState × (History × code.Path))) :
    EffectFamily pre Reference (model.HiddenState × History) :=
  match code with
  | .id _ => fun original => effects (original.1, (original.2.1, (original.2.2, ())))
  | .classical (model := selected) application => fun original => kernelEffect
      (selected.classicalOperations.evaluate application.token
        (original.1.read application.input))
      (fun result => effects (original.1.write application.output result,
        (original.2.1, (original.2.2, result))))
  | .classicalQuery (model := selected) application => fun original => kernelEffect
      (selected.classicalOracles.transition environment.classical application.query original.2.1
        (original.1.read application.input))
      (fun result => effects (original.1.write application.output result.2,
        (result.1, (original.2.2, result.2))))
  | .unitary program => fun original => Effect.pullbackUnitary
      (UnitaryOperator.prodTensor (program.matrix environment.quantum)
        (1 : UnitaryOperator Reference))
      (effects (original.1, (original.2.1, (original.2.2, ()))))
  | .measureZ wire output => fun original => ZMeasurement.pullbackEffect
      (fun basis => basis.1 wire) (fun outcome =>
        effects (original.1.write output (.finite outcome),
          (original.2.1, (original.2.2, outcome))))
  | .retain _ctx key shape fresh => fun original =>
      effects (original.1.pushRetained key shape fresh, (original.2.1, (original.2.2, ())))
  | .prepareZero _ctx key layout fresh disjoint => fun original =>
      Effect.compress (basisPreparationEmbedding key layout fresh disjoint
        (BasisPreparation.zero layout))
        (basisPreparationEmbedding_injective key layout fresh disjoint
          (BasisPreparation.zero layout))
        (effects (original.1.pushOwnedLayout key layout fresh disjoint,
          (original.2.1, (original.2.2, ()))))
  | .seq first second =>
      effectPullback first environment Reference
        (effectPullback second environment Reference (fun result =>
        effects (result.1, (result.2.1, (result.2.2.1.1, (result.2.2.1.2, result.2.2.2))))))
  | .branch input body => fun original =>
      effectPullback (body (original.1.read input)) environment Reference (fun result =>
        effects (result.1, (result.2.1,
          (result.2.2.1, ⟨original.1.read input, result.2.2.2⟩)))) original
  | .iterate count body =>
      repeatEffectPullback (effectPullback body environment Reference) count effects
  | .workspace _ctx key shape fresh body => fun original =>
      effectPullback body environment Reference (fun result =>
        effects (Store.popWorkspace key shape fresh result.1, result.2))
          (original.1.pushWorkspace key shape fresh, original.2)
  | .embed placement body =>
      embedEffectPullback placement Reference
        (effectPullback body environment (Register.prod placement.frame.register Reference)) effects
  | .ownedLayoutView view body =>
      view.splitEffectPullback Reference
        (effectPullback body environment Reference (view.joinEffectPullback Reference effects))
  | .parallelClassical join separate first second =>
      parallelEffectPullback join separate Reference
        (effectPullback first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _)
        (effectPullback second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _) effects
  | .parallelQuantum join separate first second =>
      parallelEffectPullback join separate Reference
        (effectPullback first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _)
        (effectPullback second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _) effects
termination_by structural code

end Circuit

namespace Execution.State

/-- Mathematical history reindexing pulls back only the observation's history argument. -/
lemma effectWeight_mapHistory {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K)
    (effects : Circuit.EffectFamily ctx Reference K) :
    (state.mapHistory update).effectWeight effects =
      state.effectWeight (fun original => effects (original.1, update original.2)) := by
  unfold mapHistory
  exact ExecutionState.effectWeight_mapClassical_decision _ state _ effects

/-- The actual unitary instruction pulls back the full context-reference observable. -/
lemma effectWeight_unitary {ctx : RuntimeCtx .quantum} {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference H)
    (program : UnitaryOperator ctx.register)
    (effects : Circuit.EffectFamily ctx Reference (H × Unit)) :
    (state.unitary program).effectWeight effects =
      state.effectWeight (fun original => Effect.pullbackUnitary
        (UnitaryOperator.prodTensor program (1 : UnitaryOperator Reference))
        (effects (original.1, (original.2, ())))) := by
  unfold unitary
  rw [ExecutionState.effectWeight_mapClassical_decision,
    ExecutionState.effectWeight_applyUnitary]

/-- Actual random-bit outcomes use the real uniform probability and Store write. -/
lemma effectWeight_randomBits {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (width : Nat) (output : CWriteRef ctx (.bits width))
    (effects : Circuit.EffectFamily ctx Reference (H × Fin (2 ^ width))) :
    (state.randomBits width output).effectWeight effects =
      state.effectWeight (fun original => Effect.uniformAverage
        (fun outcome : Fin (2 ^ width) => effects (original.1.write output
          (.bits fun index => outcome.val.testBit (width - 1 - index.val)),
            (original.2, outcome)))) := by
  unfold randomBits
  rw [ExecutionState.effectWeight_mapClassical_decision]
  erw [ExecutionState.effectWeight_uniformChoice]
  rfl

end Execution.State

namespace Circuit

open Execution

private lemma effectWeight_branch {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    {shape : CShape} (input : CInputRef pre shape)
    (body : shape.Value → Circuit model pre post allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (bodyEquation : ∀ value {H : Type} [Fintype H]
      (state : State pre Reference (model.HiddenState × H))
      (effects : EffectFamily post Reference (model.HiddenState × (H × (body value).Path))),
      ((body value).execute environment Reference state).effectWeight effects =
        state.effectWeight (effectPullback (body value) environment Reference effects))
    {H : Type} [Fintype H] (state : State pre Reference (model.HiddenState × H))
    (effects : EffectFamily post Reference (model.HiddenState ×
      (H × (Circuit.branch input body).Path))) :
    ((Circuit.branch input body).execute environment Reference state).effectWeight effects =
      state.effectWeight
        (effectPullback (Circuit.branch input body) environment Reference effects) := by
  classical
  unfold ExecutionState.effectWeight Effect.weight
  simp only [execute_branch_block_matrix, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  change (∑ value : shape.Value,
    (((body value).execute environment Reference
      (state.selectClassical (fun original => original.1.read input) value)).mapHistory
        (fun history => (history.1, (history.2.1,
          (⟨value, history.2.2⟩ : (Circuit.branch input body).Path))))).effectWeight effects) = _
  simp_rw [State.effectWeight_mapHistory, bodyEquation,
    ExecutionState.effectWeight_selectClassical]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

private lemma effectWeight_iterate {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    (body : Circuit model ctx ctx allowAllocation) (environment : model.Environment)
    (Reference : Register)
    (bodyEquation : ∀ {H : Type} [Fintype H]
      (state : State ctx Reference (model.HiddenState × H))
      (effects : EffectFamily ctx Reference (model.HiddenState × (H × body.Path))),
      (body.execute environment Reference state).effectWeight effects =
        state.effectWeight (effectPullback body environment Reference effects)) :
    ∀ (count : Nat) {H : Type} [Fintype H]
      (state : State ctx Reference (model.HiddenState × H))
      (effects : EffectFamily ctx Reference (model.HiddenState × (H × (Fin count → body.Path)))),
      ((Circuit.iterate count body).execute environment Reference state).effectWeight effects =
        state.effectWeight
          (repeatEffectPullback (effectPullback body environment Reference) count effects) := by
  intro count
  induction count with
  | zero =>
      intro H _ state effects
      rw [execute_iterate_zero, State.effectWeight_mapHistory]
      rfl
  | succ count induction =>
      intro H _ state effects
      rw [execute_iterate_succ, State.effectWeight_mapHistory, induction, bodyEquation]
      rfl

/-- Every final certified block observation has this exact pullback through actual execution.
The statement retains arbitrary initial mixtures and external-reference correlations. -/
lemma effectWeight_execute {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (environment : model.Environment)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × H))
    (effects : EffectFamily post Reference (model.HiddenState × (H × code.Path))) :
    (code.execute environment Reference state).effectWeight effects =
      state.effectWeight (effectPullback code environment Reference effects) := by
  induction code generalizing Reference H with
  | id ctx =>
      rw [execute_id, ExecutionState.effectWeight_mapClassical_decision]
      rfl
  | classical application =>
      rw [execute_classical, ExecutionState.effectWeight_mapClassical_decision,
        ExecutionState.effectWeight_kernelChoice]
      rfl
  | classicalQuery application =>
      rw [execute_classicalQuery, effectWeight_queryStep]
      rfl
  | unitary program =>
      rw [execute_unitary, ExecutionState.effectWeight_mapClassical_decision,
        ExecutionState.effectWeight_applyUnitary]
      rfl
  | measureZ wire output =>
      dsimp only [execute, interpret, preserveService]
      rw [State.effectWeight_mapHistory, State.effectWeight_measureZ]
      rfl
  | retain ctx key shape fresh =>
      rw [execute_retain, ExecutionState.effectWeight_mapClassical_decision]
      rfl
  | prepareZero ctx key layout fresh disjoint =>
      dsimp only [execute, interpret, preserveService]
      rw [State.effectWeight_mapHistory, State.effectWeight_prepare]
      rfl
  | seq first second firstEquation secondEquation =>
      rw [execute_seq, State.effectWeight_mapHistory, secondEquation, firstEquation]
      rfl
  | branch input body bodyEquation =>
      exact effectWeight_branch input body environment Reference
        (fun value => bodyEquation value environment Reference) state effects
  | iterate count body bodyEquation =>
      exact effectWeight_iterate body environment Reference
        (bodyEquation environment Reference) count state effects
  | workspace ctx key shape fresh body bodyEquation =>
      rw [execute_workspace]
      unfold State.popWorkspace
      erw [ExecutionState.effectWeight_mapClassical_decision, bodyEquation]
      unfold State.pushWorkspace
      erw [ExecutionState.effectWeight_mapClassical_decision]
      rfl
  | embed placement body bodyEquation =>
      exact embedPreserving_effect placement Reference
        (fun original => interpret body environment _ original)
        (effectPullback body environment _)
        (fun {_} _ original effects => bodyEquation environment _ original effects)
        state effects
  | ownedLayoutView view body bodyEquation =>
      change (view.join (body.execute environment Reference (view.split state))).effectWeight _ = _
      rw [view.effectWeight_join, bodyEquation, view.effectWeight_split]
      rfl
  | parallelClassical join separate first second firstEquation secondEquation =>
      exact parallelPreserving_effect join separate
        (fun original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (effectPullback first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _)
        (effectPullback second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _)
        (fun {_} _ original effects => firstEquation
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original effects)
        (fun {_} _ original effects => secondEquation
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original effects)
        state effects
  | parallelQuantum join separate first second firstEquation secondEquation =>
      exact parallelPreserving_effect join separate
        (fun original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (effectPullback first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _)
        (effectPullback second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _)
        (fun {_} _ original effects => firstEquation
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original effects)
        (fun {_} _ original effects => secondEquation
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original effects)
        state effects

/-- Partition an actual circuit observation by any finite label on its input
store, service state and earlier history. Each selected execution retains its
original quantum and reference blocks, without normalizing the fiber. -/
lemma effectWeight_execute_partition {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (environment : model.Environment)
    {Reference : Register} {H D : Type}
    [Fintype H] [Fintype D] [DecidableEq D]
    (state : State pre Reference (model.HiddenState × H))
    (read : Store pre × (model.HiddenState × H) → D)
    (effects : EffectFamily post Reference (model.HiddenState × (H × code.Path))) :
    (code.execute environment Reference state).effectWeight effects =
      ∑ label : D,
        (code.execute environment Reference
          (state.selectClassical read label)).effectWeight effects := by
  simp only [effectWeight_execute]
  have partition := congrArg
    (fun current : State pre Reference (model.HiddenState × H) =>
      current.effectWeight (code.effectPullback environment Reference effects))
    (ExecutionState.finiteSum_selectClassical state read)
  rw [ExecutionState.effectWeight_finiteSum] at partition
  exact partition.symm

end Circuit

end

end QuantumAlg
