/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.MapLaws
import all QuantumAlg.Core.Execution.Classical.Step.History
import all QuantumAlg.Core.Execution.Random.Map
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
import all QuantumAlg.Core.Execution.State

/-!
# Mathematical history maps commute with actual state instructions

A history function may identify old records; the existing classical map then
sums their complete density blocks. None of the actual instructions reads
that mathematical history. Their physical storage operations and their newly
recorded paths are unchanged by the map.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H K L : Type} [Fintype H] [Fintype K] [Fintype L]

/-- History functions compose using the actual finite classical fiber sum. -/
lemma mapHistory_comp (state : State ctx Reference H) (first : H → K) (second : K → L) :
    (state.mapHistory first).mapHistory second = state.mapHistory (second ∘ first) := by
  simp only [mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]

/-- The deterministic identity record is independent of the prior history encoding. -/
lemma mapHistory_skip (state : State ctx Reference H) (update : H → K) :
    (state.mapHistory update).skip =
      state.skip.mapHistory (fun record => (update record.1, record.2)) := by
  simp only [skip, mapHistory_comp, Function.comp_def]

/-- Actual atomic classical reads and writes ignore the mathematical history label. -/
lemma mapHistory_classicalStep (state : State ctx Reference H) (update : H → K)
    {input output : CShape} (operation : ClassicalOp input output ctx ctx) :
    (state.mapHistory update).classicalStep operation =
      (state.classicalStep operation).mapHistory (fun record => (update record.1, record.2)) := by
  simp only [classicalStep, mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Retained allocation creates the same real cell and leaves the old history map independent. -/
lemma mapHistory_retain (state : State ctx Reference H) (update : H → K)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (state.mapHistory update).retain key shape fresh =
      (state.retain key shape fresh).mapHistory (fun record => (update record.1, record.2)) := by
  simp only [retain, mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Entering actual lexical storage commutes with arbitrary history relabeling. -/
lemma mapHistory_pushWorkspace (state : State ctx Reference H) (update : H → K)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (state.mapHistory update).pushWorkspace key shape fresh =
      (state.pushWorkspace key shape fresh).mapHistory update := by
  simp only [pushWorkspace, mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  erw [ExecutionState.executionState_mapClassical_comp]
  congr 1

/-- Releasing the exact workspace head retains the same sums of overwritten cells. -/
lemma mapHistory_popWorkspace (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State (ctx.addWorkspace key shape fresh) Reference H) (update : H → K) :
    popWorkspace key shape fresh (state.mapHistory update) =
      (popWorkspace key shape fresh state).mapHistory update := by
  simp only [popWorkspace, mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  erw [ExecutionState.executionState_mapClassical_comp]
  congr 1

/-- The actual random outcome is retained while prior histories are grouped independently. -/
lemma mapHistory_randomBits (state : State ctx Reference H) (update : H → K)
    (width : Nat) (output : CWriteRef ctx (.bits width)) :
    (state.mapHistory update).randomBits width output =
      (state.randomBits width output).mapHistory
        (fun record => (update record.1, record.2)) := by
  dsimp only [randomBits, mapHistory]
  erw [uniformChoice_mapClassical]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Branch selection uses the same actual stored value after any history map. -/
lemma mapHistory_selectClassical (state : State ctx Reference H) (update : H → K)
    {shape : CShape} (input : CInputRef ctx shape) (value : shape.Value) :
    (state.mapHistory update).selectClassical (fun record => record.1.read input) value =
      State.mapHistory
        (state.selectClassical (fun record => record.1.read input) value) update :=
  ExecutionState.mapClassical_selectClassical state
    (fun record => (record.1, update record.2)) (fun record => record.1.read input) value

section Quantum

variable {ctx : RuntimeCtx .quantum}

/-- Actual unitary evolution commutes with every finite mathematical history function. -/
lemma mapHistory_unitary (state : State ctx Reference H) (update : H → K)
    (program : UnitaryOperator ctx.register) :
    (state.mapHistory update).unitary program =
      (state.unitary program).mapHistory (fun record => (update record.1, record.2)) := by
  simp only [unitary, mapHistory, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual Z readout, store write and outcome record commute with grouping the old history. -/
lemma mapHistory_measureZ (state : State ctx Reference H) (update : H → K)
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    measureZ (state.mapHistory update) wire output =
      (measureZ state wire output).mapHistory (fun record => (update record.1, record.2)) := by
  dsimp only [measureZ, mapHistory]
  erw [ExecutionState.mapClassical_measureZ]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private lemma mapClassical_decision {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (first second : DecidableEq D) (state : ExecutionState C R) (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R first state update =
      @ExecutionState.mapClassical C D _ _ R second state update := by
  cases Subsingleton.elim first second
  rfl

private lemma mapHistory_decision (decision : DecidableEq (Store ctx × K))
    (state : State ctx Reference H) (update : H → K) :
    @ExecutionState.mapClassical (Store ctx × H) (Store ctx × K) _ _
        (Register.prod ctx.register Reference) decision state
        (fun record => (record.1, update record.2)) = state.mapHistory update := by
  unfold mapHistory
  exact mapClassical_decision _ _ _ _

private lemma prepareContext_mapClassical_decision {C D : Type}
    [Fintype C] [Fintype D] [decision : DecidableEq D]
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) {count : Nat} (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (update : C → D) :
    prepareContext (state.mapClassical update) key layout fresh disjoint prepared =
      (prepareContext state key layout fresh disjoint prepared).mapClassical update := by
  have before := mapClassical_decision decision (Classical.decEq D) state update
  have after := mapClassical_decision (Classical.decEq D) decision
    (prepareContext state key layout fresh disjoint prepared) update
  have actual := (prepareContext_mapClassical state key layout fresh disjoint prepared update).symm
  exact (congrArg
    (fun original : ExecutionState D (Register.prod ctx.register Reference) =>
      prepareContext original key layout fresh disjoint prepared) before).trans
        (actual.trans after)

/-- Fixed fresh preparation preserves the same full blocks under arbitrary history maps. -/
lemma mapHistory_prepare (state : State ctx Reference H) (update : H → K)
    (key : StorageKey) {count : Nat} (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) :
    (state.mapHistory update).prepare key layout fresh disjoint preparation =
      (state.prepare key layout fresh disjoint preparation).mapHistory
        (fun record => (update record.1, record.2)) := by
  let after := ctx.addOwnedLayout key layout fresh disjoint
  let historyMap : Store ctx × H → Store ctx × K :=
    fun record => (record.1, update record.2)
  let writeOld : Store ctx × H → Store after × (H × Unit) :=
    fun record => (record.1.pushOwnedLayout key layout fresh disjoint, (record.2, ()))
  let writeNew : Store ctx × K → Store after × (K × Unit) :=
    fun record => (record.1.pushOwnedLayout key layout fresh disjoint, (record.2, ()))
  let finish : Store after × (H × Unit) → Store after × (K × Unit) :=
    fun record => (record.1, (update record.2.1, record.2.2))
  let prepared := prepareContext state key layout fresh disjoint preparation.normalized
  have core := prepareContext_mapClassical_decision state key layout fresh disjoint
    preparation.normalized historyMap
  have actual := congrArg
    (fun original : ExecutionState (Store ctx × K) (Register.prod after.register Reference) =>
      original.mapClassical writeNew) core
  have first := ExecutionState.executionState_mapClassical_comp prepared historyMap writeNew
  have second := ExecutionState.executionState_mapClassical_comp prepared writeOld finish
  have diagram : writeNew ∘ historyMap = finish ∘ writeOld := rfl
  have combined := actual.trans (first.trans
    ((congrArg (fun labels => prepared.mapClassical labels) diagram).trans second.symm))
  have finishActual := mapHistory_decision
    (inferInstance : DecidableEq (Store after × (K × Unit)))
    (state.prepare key layout fresh disjoint preparation)
    (fun record => (update record.1, record.2))
  exact combined.trans finishActual

end Quantum

end

end QuantumAlg.Execution.State
