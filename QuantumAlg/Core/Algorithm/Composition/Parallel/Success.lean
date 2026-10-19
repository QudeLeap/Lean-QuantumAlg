/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Algorithm.Composition
public import QuantumAlg.Core.Algorithm.Composition.Parallel.Admission
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Problem.Parallel
import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Admission
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Distribution
import all QuantumAlg.Util.PMF.JointSuccess

/-!
# Joint success of the actual parallel execution

Both marginal bounds apply to the original unconditional admitted child
inputs. Their relational distributions are marginals of the same complete
parallel distribution, so the sum of failure allowances bounds joint failure
even when the initial states, services and resulting outputs are correlated.
-/

namespace QuantumAlg.Algorithm

noncomputable section

open Execution

/-- The original child guarantees give joint success without an independence assumption. -/
public lemma algorithm_parallelClassical_success
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
    {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Algorithm (.classical operations leftService) left left leftShape false)
    (second : Algorithm (.classical operations rightService) right right rightShape false)
    (firstProblem : Problem (.classical operations leftService) left left leftShape)
    (secondProblem : Problem (.classical operations rightService) right right rightShape)
    (firstCorrect : first.Solves firstProblem) (secondCorrect : second.Solves secondProblem)
    (environment : (ExecutionModel.classical operations parentService).Environment)
    (witness : firstProblem.Witness × secondProblem.Witness)
    {Reference : Register}
    (input : OracleInput parentService (left.disjointUnion right separate) Reference)
    (admitted : (Problem.parallelClassical join separate firstProblem secondProblem).Admits
      environment witness input) :
    ((Problem.parallelClassical join separate firstProblem secondProblem).successLB
      environment witness).value ≤
      ((parallelClassical (allowAllocation := allowAllocation)
        join separate first second).relationalDistribution environment input).toOuterMeasure
          {pair | (Problem.parallelClassical join separate firstProblem secondProblem).accepts
            environment witness
            pair.1 pair.2} := by
  let leftEnvironment : (ExecutionModel.classical operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment : (ExecutionModel.classical operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  have localAdmitted := (Problem.problem_parallelClassical_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  have firstSuccess := firstCorrect.success leftEnvironment witness.1 Reference
    ((ContextEmbedding.alongUnion left right separate).localInput (join.leftInput input))
    localAdmitted.1.1 localAdmitted.1.2
  have secondSuccess := secondCorrect.success rightEnvironment witness.2 Reference
    ((ContextEmbedding.alongUnionRight left right separate).localInput (join.rightInput input))
    localAdmitted.2.1 localAdmitted.2.2
  simp only [Algorithm.relationalDistribution] at firstSuccess secondSuccess
  rw [← parallelClassical_relationalDistribution_left (allowAllocation := allowAllocation)
    join separate first second environment input] at firstSuccess
  rw [← parallelClassical_relationalDistribution_right (allowAllocation := allowAllocation)
    join separate first second environment input] at secondSuccess
  let distribution := (parallelClassical (allowAllocation := allowAllocation)
    join separate first second).run.relationalDistribution environment input
  let readLeft : Store (left.disjointUnion right separate) ×
      (CShape.product leftShape rightShape).Value → Store left × leftShape.Value :=
    fun pair => match pair.2 with
      | .product result _ =>
          (((ContextEmbedding.alongUnion left right separate).store pair.1).1, result)
  let readRight : Store (left.disjointUnion right separate) ×
      (CShape.product leftShape rightShape).Value → Store right × rightShape.Value :=
    fun pair => match pair.2 with
      | .product _ result =>
          (((ContextEmbedding.alongUnionRight left right separate).store pair.1).1, result)
  have firstBound : (firstProblem.successLB leftEnvironment witness.1).value ≤
      distribution.toOuterMeasure
      {pair | firstProblem.accepts leftEnvironment witness.1
        (readLeft pair).1 (readLeft pair).2} := by
    simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] at firstSuccess
    refine firstSuccess.trans_eq (congrArg distribution.toOuterMeasure ?_)
    ext ⟨original, result⟩
    cases result
    rfl
  have secondBound : (secondProblem.successLB rightEnvironment witness.2).value ≤
      distribution.toOuterMeasure
      {pair | secondProblem.accepts rightEnvironment witness.2
          (readRight pair).1 (readRight pair).2} := by
    simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] at secondSuccess
    refine secondSuccess.trans_eq (congrArg distribution.toOuterMeasure ?_)
    ext ⟨original, result⟩
    cases result
    rfl
  have events :
      ({pair : Store (left.disjointUnion right separate) ×
          (CShape.product leftShape rightShape).Value |
        (Problem.parallelClassical join separate firstProblem secondProblem).accepts
            environment witness
          pair.1 pair.2}) =
      {pair | firstProblem.accepts leftEnvironment witness.1 (readLeft pair).1 (readLeft pair).2 ∧
        secondProblem.accepts rightEnvironment witness.2
          (readRight pair).1 (readRight pair).2} := by
    ext ⟨original, result⟩
    cases result
    rfl
  change 1 - ((1 - (firstProblem.successLB leftEnvironment witness.1).value) +
      (1 - (secondProblem.successLB rightEnvironment witness.2).value)) ≤
    distribution.toOuterMeasure
      {pair | (Problem.parallelClassical join separate firstProblem secondProblem).accepts
            environment witness
        pair.1 pair.2}
  rw [events]
  exact PMF.jointEventProbability_ge_unionBound distribution _ _
    (firstProblem.successLB leftEnvironment witness.1).value
    (secondProblem.successLB rightEnvironment witness.2).value firstBound secondBound

/-- The original child guarantees give joint success without an independence assumption. -/
public lemma algorithm_parallelQuantum_success
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {leftShape rightShape : CShape}
    {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Algorithm (.quantum gates oracles operations leftService) left left leftShape false)
    (second : Algorithm (.quantum gates oracles operations rightService)
      right right rightShape false)
    (firstProblem : Problem (.quantum gates oracles operations leftService) left left leftShape)
    (secondProblem : Problem (.quantum gates oracles operations rightService)
      right right rightShape)
    (firstCorrect : first.Solves firstProblem) (secondCorrect : second.Solves secondProblem)
    (environment : (ExecutionModel.quantum gates oracles operations parentService).Environment)
    (witness : firstProblem.Witness × secondProblem.Witness)
    {Reference : Register}
    (input : OracleInput parentService (left.disjointUnion right separate) Reference)
    (admitted : (Problem.parallelQuantum join separate firstProblem secondProblem).Admits
      environment witness input) :
    ((Problem.parallelQuantum join separate firstProblem secondProblem).successLB
      environment witness).value ≤
      ((parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).relationalDistribution environment input).toOuterMeasure
          {pair | (Problem.parallelQuantum join separate firstProblem secondProblem).accepts
            environment witness
            pair.1 pair.2} := by
  let leftEnvironment : (ExecutionModel.quantum gates oracles operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment :
      (ExecutionModel.quantum gates oracles operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  have localAdmitted := (Problem.problem_parallelQuantum_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  have firstSuccess := firstCorrect.success leftEnvironment witness.1 Reference
    ((ContextEmbedding.alongUnion left right separate).localInput (join.leftInput input))
    localAdmitted.1.1 localAdmitted.1.2
  have secondSuccess := secondCorrect.success rightEnvironment witness.2 Reference
    ((ContextEmbedding.alongUnionRight left right separate).localInput (join.rightInput input))
    localAdmitted.2.1 localAdmitted.2.2
  simp only [Algorithm.relationalDistribution] at firstSuccess secondSuccess
  rw [← parallelQuantum_relationalDistribution_left (allowAllocation := allowAllocation)
    join separate first second environment input] at firstSuccess
  rw [← parallelQuantum_relationalDistribution_right (allowAllocation := allowAllocation)
    join separate first second environment input] at secondSuccess
  let distribution := (parallelQuantum (allowAllocation := allowAllocation)
    join separate first second).run.relationalDistribution environment input
  let readLeft : Store (left.disjointUnion right separate) ×
      (CShape.product leftShape rightShape).Value → Store left × leftShape.Value :=
    fun pair => match pair.2 with
      | .product result _ =>
          (((ContextEmbedding.alongUnion left right separate).store pair.1).1, result)
  let readRight : Store (left.disjointUnion right separate) ×
      (CShape.product leftShape rightShape).Value → Store right × rightShape.Value :=
    fun pair => match pair.2 with
      | .product _ result =>
          (((ContextEmbedding.alongUnionRight left right separate).store pair.1).1, result)
  have firstBound : (firstProblem.successLB leftEnvironment witness.1).value ≤
      distribution.toOuterMeasure
      {pair | firstProblem.accepts leftEnvironment witness.1
        (readLeft pair).1 (readLeft pair).2} := by
    simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] at firstSuccess
    refine firstSuccess.trans_eq (congrArg distribution.toOuterMeasure ?_)
    ext ⟨original, result⟩
    cases result
    rfl
  have secondBound : (secondProblem.successLB rightEnvironment witness.2).value ≤
      distribution.toOuterMeasure
      {pair | secondProblem.accepts rightEnvironment witness.2
          (readRight pair).1 (readRight pair).2} := by
    simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] at secondSuccess
    refine secondSuccess.trans_eq (congrArg distribution.toOuterMeasure ?_)
    ext ⟨original, result⟩
    cases result
    rfl
  have events :
      ({pair : Store (left.disjointUnion right separate) ×
          (CShape.product leftShape rightShape).Value |
        (Problem.parallelQuantum join separate firstProblem secondProblem).accepts
            environment witness
          pair.1 pair.2}) =
      {pair | firstProblem.accepts leftEnvironment witness.1 (readLeft pair).1 (readLeft pair).2 ∧
        secondProblem.accepts rightEnvironment witness.2
          (readRight pair).1 (readRight pair).2} := by
    ext ⟨original, result⟩
    cases result
    rfl
  change 1 - ((1 - (firstProblem.successLB leftEnvironment witness.1).value) +
      (1 - (secondProblem.successLB rightEnvironment witness.2).value)) ≤
    distribution.toOuterMeasure
      {pair | (Problem.parallelQuantum join separate firstProblem secondProblem).accepts
            environment witness
        pair.1 pair.2}
  rw [events]
  exact PMF.jointEventProbability_ge_unionBound distribution _ _
    (firstProblem.successLB leftEnvironment witness.1).value
    (secondProblem.successLB rightEnvironment witness.2).value firstBound secondBound

end

end QuantumAlg.Algorithm

