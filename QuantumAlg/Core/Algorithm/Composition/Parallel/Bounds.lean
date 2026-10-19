/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Composition.Parallel.Success
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Problem.Parallel
import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Admission
import all QuantumAlg.Core.Algorithm.Composition.Parallel.State
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Execution.Time

/-!
# Resource bounds on the same supported parallel path

A positive-probability actual path pair yields two supported paths on the
original admitted child inputs. The native service maps route both event
ledgers into the parent coordinates. Both fixed contexts remain resident,
their auxiliary roles add, and simultaneous quantum time is the maximum.
-/

namespace QuantumAlg.Algorithm

noncomputable section

open Execution

/-- Every actual supported pair obeys all four independently supplied parallel limits. -/
public lemma algorithm_parallelClassical_resource_bounds
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
      environment witness input)
    (path : (parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.code.Path)
    (supported : (parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.Supports environment Reference input.state path) :
    (parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.code.resourcePool path ≤
      (Problem.parallelClassical join separate firstProblem secondProblem).resources.events ∧
    (parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.code.peakResidentSpace path ≤
      (Problem.parallelClassical join separate firstProblem secondProblem).resources.resident ∧
    (parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.code.peakAuxiliarySpace path ≤
      (Problem.parallelClassical join separate firstProblem secondProblem).resources.auxiliary ∧
    (parallelClassical (allowAllocation := allowAllocation)
        join separate first second).quantumTime path ≤
      (Problem.parallelClassical join separate firstProblem secondProblem).quantumTimeLimit := by
  let leftEnvironment : (ExecutionModel.classical operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment : (ExecutionModel.classical operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  have localAdmitted := (Problem.problem_parallelClassical_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  have leftSupported := parallelClassical_supports_left
    join separate first second environment input path supported
  have rightSupported := parallelClassical_supports_right
    join separate first second environment input path supported
  have leftEvents := firstCorrect.events leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightEvents := secondCorrect.events rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  have leftResident := firstCorrect.resident leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightResident := secondCorrect.resident rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  have leftAuxiliary := firstCorrect.auxiliary leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightAuxiliary := secondCorrect.auxiliary rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  have leftTime := firstCorrect.time leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightTime := secondCorrect.time rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  rcases path with ⟨leftPath, rightPath⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).resourcePool (leftPath, rightPath) ≤ _
    rw [Circuit.resourcePool_parallelClassical]
    exact add_le_add (Multiset.map_le_map leftEvents) (Multiset.map_le_map rightEvents)
  · change (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).peakResidentSpace (leftPath, rightPath) ≤ _
    rw [Circuit.peakResidentSpace_parallelClassical]
    rw [Circuit.fixed_peakResidentSpace] at leftResident rightResident
    exact add_le_add leftResident rightResident
  · change (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).peakAuxiliarySpace (leftPath, rightPath) ≤ _
    rw [Circuit.peakAuxiliarySpace_parallelClassical]
    rw [Circuit.fixed_peakAuxiliarySpace] at leftAuxiliary rightAuxiliary
    exact add_le_add leftAuxiliary rightAuxiliary
  · change (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).quantumTime (leftPath, rightPath) ≤ _
    rw [Circuit.quantumTime_parallelClassical]
    exact max_le_max leftTime rightTime

/-- Every actual supported pair obeys all four independently supplied parallel limits. -/
public lemma algorithm_parallelQuantum_resource_bounds
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
      environment witness input)
    (path : (parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.code.Path)
    (supported : (parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.Supports environment Reference input.state path) :
    (parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.code.resourcePool path ≤
      (Problem.parallelQuantum join separate firstProblem secondProblem).resources.events ∧
    (parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.code.peakResidentSpace path ≤
      (Problem.parallelQuantum join separate firstProblem secondProblem).resources.resident ∧
    (parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.code.peakAuxiliarySpace path ≤
      (Problem.parallelQuantum join separate firstProblem secondProblem).resources.auxiliary ∧
    (parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).quantumTime path ≤
      (Problem.parallelQuantum join separate firstProblem secondProblem).quantumTimeLimit := by
  let leftEnvironment : (ExecutionModel.quantum gates oracles operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment :
      (ExecutionModel.quantum gates oracles operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  have localAdmitted := (Problem.problem_parallelQuantum_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  have leftSupported := parallelQuantum_supports_left
    join separate first second environment input path supported
  have rightSupported := parallelQuantum_supports_right
    join separate first second environment input path supported
  have leftEvents := firstCorrect.events leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightEvents := secondCorrect.events rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  have leftResident := firstCorrect.resident leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightResident := secondCorrect.resident rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  have leftAuxiliary := firstCorrect.auxiliary leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightAuxiliary := secondCorrect.auxiliary rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  have leftTime := firstCorrect.time leftEnvironment witness.1 _ _
    localAdmitted.1.1 localAdmitted.1.2 path.1 leftSupported
  have rightTime := secondCorrect.time rightEnvironment witness.2 _ _
    localAdmitted.2.1 localAdmitted.2.2 path.2 rightSupported
  rcases path with ⟨leftPath, rightPath⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).resourcePool (leftPath, rightPath) ≤ _
    rw [Circuit.resourcePool_parallelQuantum]
    exact add_le_add (Multiset.map_le_map leftEvents) (Multiset.map_le_map rightEvents)
  · change (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).peakResidentSpace (leftPath, rightPath) ≤ _
    rw [Circuit.peakResidentSpace_parallelQuantum]
    rw [Circuit.fixed_peakResidentSpace] at leftResident rightResident
    exact add_le_add leftResident rightResident
  · change (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).peakAuxiliarySpace (leftPath, rightPath) ≤ _
    rw [Circuit.peakAuxiliarySpace_parallelQuantum]
    rw [Circuit.fixed_peakAuxiliarySpace] at leftAuxiliary rightAuxiliary
    exact add_le_add leftAuxiliary rightAuxiliary
  · change (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code).quantumTime (leftPath, rightPath) ≤ _
    rw [Circuit.quantumTime_parallelQuantum]
    exact max_le_max leftTime rightTime

end

end QuantumAlg.Algorithm

