/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Composition.Parallel
public import QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.State

/-!
# Exact execution of original embedded and parallel children

These equations expose the complete joint state returned by the unique
interpreter. They retain every caller cell, persistent service state, path and
external reference correlation. Parallel execution is the ordered execution
of its two original children with their own independent service components.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

private lemma pushforward_congr {C D : Type} [Fintype C] [Fintype D]
    {R : Register} {first second : DecidableEq D}
    {left right : ExecutionState C R} (equal : left = right) (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R first left update =
      @ExecutionState.mapClassical C D _ _ R second right update := by
  cases equal
  cases Subsingleton.elim first second
  rfl

open scoped Classical in
/-- Split, execute the original child, and rejoin the exact caller coordinates. -/
private lemma circuit_execute_embed_proof {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind} {allowAllocation : Bool}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false)
    {environment : model.Environment} (Reference : Register)
    {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History)) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).execute
      environment Reference state =
      placement.join
        ((body.execute environment (Register.prod placement.frame.register Reference)
          ((placement.split state).mapClassical (fun record =>
            (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))).mapClassical
          (fun record =>
            (record.1, (record.2.2.1.1,
              (record.2.1, (record.2.2.1.2, record.2.2.2)))))) := by
  dsimp only [execute, interpret, embedPreserving, State.mapHistory]
  congr 1
  apply pushforward_congr
  apply congrArg (fun initial : State localCtx
      (Register.prod placement.frame.register Reference)
      (model.HiddenState × (Store placement.frame × History)) =>
    (interpret body environment (Register.prod placement.frame.register Reference) initial).val)
  apply pushforward_congr
  rfl

open scoped Classical in
/-- Split, execute the original child, and rejoin the exact caller coordinates. -/
public lemma circuit_execute_embed {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind} {allowAllocation : Bool}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false)
    {environment : model.Environment} (Reference : Register)
    {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History)) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).execute
      environment Reference state =
      placement.join
        ((body.execute environment (Register.prod placement.frame.register Reference)
          ((placement.split state).mapClassical (fun record =>
            (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))).mapClassical
          (fun record =>
            (record.1, (record.2.2.1.1,
              (record.2.1, (record.2.2.1.2, record.2.2.2)))))) :=
  circuit_execute_embed_proof placement body Reference state

open scoped Classical in
/-- Classical parallel execution uses both actual children and retains their paired paths. -/
private lemma circuit_execute_parallelClassical_proof {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    {environment : (ExecutionModel.classical operations parentService).Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × History)) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).execute environment Reference state =
      let afterLeft := serviceOutputLeft join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnion left right separate) first).execute
            ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
            (serviceInputLeft join state))
      let afterRight := serviceOutputRight join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnionRight left right separate) second).execute
            ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
            (serviceInputRight join afterLeft))
      afterRight.mapClassical (fun record =>
        (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))) := rfl

open scoped Classical in
/-- Classical parallel execution uses both actual children and retains their paired paths. -/
public lemma circuit_execute_parallelClassical {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    {environment : (ExecutionModel.classical operations parentService).Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × History)) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).execute environment Reference state =
      let afterLeft := serviceOutputLeft join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnion left right separate) first).execute
            ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
            (serviceInputLeft join state))
      let afterRight := serviceOutputRight join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnionRight left right separate) second).execute
            ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
            (serviceInputRight join afterLeft))
      afterRight.mapClassical (fun record =>
        (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))) :=
  circuit_execute_parallelClassical_proof join separate first second Reference state

open scoped Classical in
/-- Hybrid parallel execution preserves the same full joint state as the two service-aware calls. -/
private lemma circuit_execute_parallelQuantum_proof {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    {environment : (ExecutionModel.quantum gates oracles operations parentService).Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × History)) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).execute environment Reference state =
      let afterLeft := serviceOutputLeft join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnion left right separate) first).execute
            ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
            (serviceInputLeft join state))
      let afterRight := serviceOutputRight join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnionRight left right separate) second).execute
            ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
            (serviceInputRight join afterLeft))
      afterRight.mapClassical (fun record =>
        (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))) := rfl

open scoped Classical in
/-- Hybrid parallel execution preserves the same full joint state as the two service-aware calls. -/
public lemma circuit_execute_parallelQuantum {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    {environment : (ExecutionModel.quantum gates oracles operations parentService).Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × History)) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).execute environment Reference state =
      let afterLeft := serviceOutputLeft join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnion left right separate) first).execute
            ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
            (serviceInputLeft join state))
      let afterRight := serviceOutputRight join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnionRight left right separate) second).execute
            ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
            (serviceInputRight join afterLeft))
      afterRight.mapClassical (fun record =>
        (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))) :=
  circuit_execute_parallelQuantum_proof join separate first second Reference state

end

end QuantumAlg.Circuit
