/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.ClassicalTag
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Record
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Random.Kernel.Map
import all QuantumAlg.Core.Execution.Classical.MapLaws

/-!
# Complete external-tag slices of the fixed-context instructions

Each equation uses the actual instruction's execution, declared stochastic
kernel and physical storage writes. Measurement retains its observed outcome
and the complete selected quantum block. The tag remains separate from the
persistent service state and the actual instruction path.
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution.State

/-- The decoded output retains its original input history, tag and actual path separately. -/
lemma decodeExecutionTag_entry {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference Tag : Register} {Hidden H Path : Type}
    [Fintype Hidden] [Fintype H] [Fintype Path]
    (state : State ctx (Tag.prod Reference) (Hidden × (H × Path)))
    (store : Store ctx) (hidden : Hidden) (history : H) (tag : Tag.Index) (path : Path)
    (row column : (ctx.register.prod Reference).Index) :
    ((decodeExecutionTag state).block (store, (hidden, ((history, tag), path)))).matrix
        row column =
      (state.block (store, (hidden, (history, path)))).matrix
        (row.1, (tag, row.2)) (column.1, (tag, column.2)) := by
  change (((decodeOracleTag state).mapHistory
    ((Equiv.refl Hidden).prodCongr (tagOutcomeExchange H Tag.Index Path).symm)).block
      (store, (hidden, ((history, tag), path)))).matrix row column = _
  rw [mapHistory_equiv_entry, decodeOracleTag_entry]
  rfl

end Execution.State

namespace Circuit

private lemma measureZ_map_decisions
    {C D Outcome : Type} [Fintype C] [Fintype D] [Fintype Outcome] {R : Register}
    {beforeMap : DecidableEq D} {outcomeDecision : DecidableEq Outcome}
    {afterMap : DecidableEq (D × Outcome)}
    (state : ExecutionState C R) (update : C → D) (readout : R.Index → Outcome) :
    @ExecutionState.measureZ D Outcome _ _ R outcomeDecision
        (@ExecutionState.mapClassical C D _ _ R beforeMap state update) readout =
      @ExecutionState.mapClassical (C × Outcome) (D × Outcome) _ _ R afterMap
        (@ExecutionState.measureZ C Outcome _ _ R outcomeDecision state readout)
        (fun value => (update value.1, value.2)) :=
  @ExecutionState.mapClassical_measureZ C D Outcome _ _ _ R
    beforeMap outcomeDecision afterMap state update readout

variable {allowAllocation : Bool} {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
  {Reference Tag : Register} {H : Type} [Fintype H]

variable (environment : model.Environment)

/-- Identity retains the exact tag slice and its unique empty path. -/
lemma id_decodeReferenceTag
    (state : State ctx (Tag.prod Reference) (model.HiddenState × H)) :
    (Circuit.id (model := model) (allowAllocation := allowAllocation) ctx).execute
      environment Reference
        (State.decodeOracleTag state) =
      State.decodeExecutionTag
        ((Circuit.id (model := model) (allowAllocation := allowAllocation) ctx).execute
          environment (Tag.prod Reference) state) := by
  apply ExecutionState.ext
  rintro ⟨store, hidden, ⟨history, tag⟩, path⟩
  cases path
  apply DensityOperator.ext
  ext row column
  rw [execute_id_block, State.decodeOracleTag_entry,
    State.decodeExecutionTag_entry, execute_id_block]

/-- The actual native kernel and store write preserve every arbitrary external tag slice. -/
lemma classical_decodeReferenceTag
    (application : model.classicalOperations.Application ctx)
    (state : State ctx (Tag.prod Reference) (model.HiddenState × H)) :
    (Circuit.classical (model := model) (allowAllocation := allowAllocation) application).execute
        environment Reference (State.decodeOracleTag state) =
      State.decodeExecutionTag
        ((Circuit.classical (model := model) (allowAllocation := allowAllocation)
          application).execute environment (Tag.prod Reference) state) := by
  rw [execute_classical, execute_classical]
  simp only [State.decodeExecutionTag, State.decodeOracleTag]
  rw [State.decodeReferenceTag_kernelRecord_decisions (afterMap := inferInstance)
    (ctx := ctx) (Reference := Reference) (Tag := Tag) state]
  dsimp only [State.mapHistory]
  rw [kernelChoice_mapClassical (afterMap := inferInstance)]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual query evolves its persistent state while retaining the complete external tag. -/
lemma classicalQuery_decodeReferenceTag
    (application : model.classicalOracles.Application ctx)
    (state : State ctx (Tag.prod Reference) (model.HiddenState × H)) :
    (Circuit.classicalQuery (model := model) (allowAllocation := allowAllocation)
        application).execute environment Reference (State.decodeOracleTag state) =
      State.decodeExecutionTag
        ((Circuit.classicalQuery (model := model) (allowAllocation := allowAllocation)
          application).execute environment (Tag.prod Reference) state) := by
  rw [execute_classicalQuery, execute_classicalQuery]
  dsimp only [queryStep, State.decodeExecutionTag, State.decodeOracleTag]
  rw [State.decodeReferenceTag_kernelRecord_decisions (afterMap := inferInstance)
    (ctx := ctx) (Reference := Reference) (Tag := Tag) state]
  dsimp only [State.mapHistory]
  rw [kernelChoice_mapClassical (afterMap := inferInstance)]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

section Quantum

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

variable
  (quantumEnvironment : (ExecutionModel.quantum gates oracles operations services).Environment)

/-- A local unitary preserves every tag slice beside the complete original reference. -/
lemma unitary_decodeReferenceTag
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : State ctx (Tag.prod Reference) (services.HiddenState × H)) :
    (Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
        (classicalOracles := services) program).execute quantumEnvironment Reference
        (State.decodeOracleTag state) =
      State.decodeExecutionTag
        ((Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
          (classicalOracles := services) program).execute
            quantumEnvironment (Tag.prod Reference) state) := by
  apply ExecutionState.ext
  rintro ⟨store, hidden, ⟨history, tag⟩, path⟩
  cases path
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, leftRef⟩
  rcases column with ⟨column, rightRef⟩
  rw [execute_unitary_block, State.decodeExecutionTag_entry, execute_unitary_block]
  simp only [DensityOperator.localUnitary_block, Matrix.mul_apply, Matrix.submatrix_apply,
    State.decodeOracleTag_entry]

/-- Actual Z readout and its physical store write retain the tag with the observed path. -/
lemma measureZ_decodeReferenceTag
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (state : State ctx (Tag.prod Reference) (services.HiddenState × H)) :
    (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) wire output).execute
        quantumEnvironment Reference
        (State.decodeOracleTag state) =
      State.decodeExecutionTag
        ((Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates)
          (oracles := oracles) (operations := operations)
          (classicalOracles := services) wire output).execute
          quantumEnvironment (Tag.prod Reference) state) := by
  rw [execute_measureZ, execute_measureZ]
  simp only [State.decodeExecutionTag, State.decodeOracleTag]
  rw [State.decodeReferenceTag_measureRecord_decisions (afterMap := inferInstance)
    (ctx := ctx) (Reference := Reference) (Tag := Tag)
    (Outcome := Fin (ctx.quantumLayout.wire wire).dimension)
    (K := services.HiddenState × (H × Fin (ctx.quantumLayout.wire wire).dimension))
    state (fun basis : ctx.register.Index => basis wire)
    (fun entry =>
      (entry.1.1.write output (.finite entry.2), (entry.1.2.1, (entry.1.2.2, entry.2))))]
  dsimp only [State.mapHistory]
  rw [measureZ_map_decisions (afterMap := inferInstance)]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end Quantum

end Circuit

end

end QuantumAlg
