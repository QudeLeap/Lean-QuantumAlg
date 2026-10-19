/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem.Parallel.Admission
import all QuantumAlg.Core.Algorithm.Problem.Parallel.Admission
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding

/-!
# Admission of the original local inputs to parallel children

Removing the opposite physical frame from the external reference changes
neither local caller validity nor the joint local service initialization.
These equivalences concern unconditional marginals of the original input.
-/

namespace QuantumAlg.Problem

noncomputable section

/-- Parallel admission is exactly admission of both original inputs with the same reference. -/
public lemma problem_parallelClassical_admits_local_iff
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Problem (.classical operations leftService) left left leftShape)
    (second : Problem (.classical operations rightService) right right rightShape)
    (environment : (ExecutionModel.classical operations parentService).Environment)
    (witness : first.Witness × second.Witness)
    {Reference : Register}
    (input : Execution.OracleInput parentService (left.disjointUnion right separate) Reference) :
    (parallelClassical join separate first second).Admits environment witness input ↔
      first.Admits ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
        ((ContextEmbedding.alongUnion left right separate).localInput
        (join.leftInput input)) ∧
      second.Admits ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
        ((ContextEmbedding.alongUnionRight left right separate).localInput
        (join.rightInput input)) := by
  rw [problem_parallelClassical_admits_framed_iff]
  unfold Admits
  rw [ContextEmbedding.contextEmbedding_localInput_caller_localState,
    ContextEmbedding.contextEmbedding_localInput_localState,
    ContextEmbedding.contextEmbedding_localInput_caller_localState,
    ContextEmbedding.contextEmbedding_localInput_localState]

/-- Parallel admission is exactly admission of both original inputs with the same reference. -/
public lemma problem_parallelQuantum_admits_local_iff
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {leftShape rightShape : CShape}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Problem (.quantum gates oracles operations leftService) left left leftShape)
    (second : Problem (.quantum gates oracles operations rightService) right right rightShape)
    (environment : (ExecutionModel.quantum gates oracles operations parentService).Environment)
    (witness : first.Witness × second.Witness)
    {Reference : Register}
    (input : Execution.OracleInput parentService (left.disjointUnion right separate) Reference) :
    (parallelQuantum join separate first second).Admits environment witness input ↔
      first.Admits ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
        ((ContextEmbedding.alongUnion left right separate).localInput
        (join.leftInput input)) ∧
      second.Admits ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
        ((ContextEmbedding.alongUnionRight left right separate).localInput
        (join.rightInput input)) := by
  rw [problem_parallelQuantum_admits_framed_iff]
  unfold Admits
  rw [ContextEmbedding.contextEmbedding_localInput_caller_localState,
    ContextEmbedding.contextEmbedding_localInput_localState,
    ContextEmbedding.contextEmbedding_localInput_caller_localState,
    ContextEmbedding.contextEmbedding_localInput_localState]

end

end QuantumAlg.Problem

