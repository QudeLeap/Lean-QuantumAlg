/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem.Parallel
public import QuantumAlg.Core.Execution.Input.Oracle.Service.Placement
import all QuantumAlg.Core.Algorithm.Problem.Parallel
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Exact admission for both original parallel children

The parent admits precisely the two original unconditional child inputs. Both
service states are selected from the same actual joint input. The complete
physical complement may remain in the external reference without adding an
independence or conditioning premise.
-/

namespace QuantumAlg.Problem

noncomputable section

/-- Admission of the parallel classical run is exactly admission of its original children. -/
public lemma problem_parallelClassical_admits_framed_iff
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
        ((ContextEmbedding.alongUnion left right separate).framedInput
        (join.leftInput input)) ∧
      second.Admits ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
        ((ContextEmbedding.alongUnionRight left right separate).framedInput
        (join.rightInput input)) := by
  unfold Admits parallelClassical
  simp only [ContextEmbedding.contextEmbedding_framedLeftInput_caller_localState,
    ContextEmbedding.contextEmbedding_framedRightInput_caller_localState,
    ContextEmbedding.contextEmbedding_framedLeftInput_localState,
    ContextEmbedding.contextEmbedding_framedRightInput_localState]
  tauto

/-- Admission of the parallel quantum run is exactly admission of its original children. -/
public lemma problem_parallelQuantum_admits_framed_iff
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
        ((ContextEmbedding.alongUnion left right separate).framedInput
        (join.leftInput input)) ∧
      second.Admits ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
        ((ContextEmbedding.alongUnionRight left right separate).framedInput
        (join.rightInput input)) := by
  unfold Admits parallelQuantum
  simp only [ContextEmbedding.contextEmbedding_framedLeftInput_caller_localState,
    ContextEmbedding.contextEmbedding_framedRightInput_caller_localState,
    ContextEmbedding.contextEmbedding_framedLeftInput_localState,
    ContextEmbedding.contextEmbedding_framedRightInput_localState]
  tauto

end

end QuantumAlg.Problem
