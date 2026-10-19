/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Composition.Parallel.Bounds
public import QuantumAlg.Core.Algorithm.Composition.Parallel.States
public import QuantumAlg.Core.Algorithm.Composition.Parallel.Borrowed
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Problem.Parallel

/-!
# Complete original contracts under disjoint parallel execution

Both child algorithms retain their independent original specifications. The
same actual parallel execution supplies joint success, state promises, full
borrowed restoration, routed native events, resident and auxiliary space, and
quantum time. No independence or conditional-admission premise is added.
-/

namespace QuantumAlg.Algorithm

noncomputable section

/-- Disjoint actual classical execution preserves both complete original child contracts. -/
public lemma algorithm_parallelClassical_solves
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
    {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Algorithm (.classical operations leftService) left left leftShape false)
    (second : Algorithm (.classical operations rightService)
      right right rightShape false)
    (firstProblem : Problem (.classical operations leftService) left left leftShape)
    (secondProblem : Problem (.classical operations rightService)
      right right rightShape)
    (firstCorrect : first.Solves firstProblem) (secondCorrect : second.Solves secondProblem) :
    (parallelClassical (allowAllocation := allowAllocation) join separate first second).Solves
      (Problem.parallelClassical join separate firstProblem secondProblem) where
  success environment witness _Reference input valid initialized :=
    algorithm_parallelClassical_success join separate first second firstProblem secondProblem
      firstCorrect secondCorrect environment witness input ⟨valid, initialized⟩
  states environment witness _Reference input valid initialized requirement present :=
    algorithm_parallelClassical_states join separate first second firstProblem secondProblem
      firstCorrect secondCorrect environment witness input ⟨valid, initialized⟩ requirement present
  borrowed environment witness _Reference input valid initialized :=
    algorithm_parallelClassical_borrowed join separate first second firstProblem secondProblem
      firstCorrect secondCorrect environment witness input ⟨valid, initialized⟩
  events environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelClassical_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).1
  resident environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelClassical_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).2.1
  auxiliary environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelClassical_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).2.2.1
  time environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelClassical_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).2.2.2

/-- Disjoint actual quantum execution preserves both complete original child contracts. -/
public lemma algorithm_parallelQuantum_solves
    {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
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
    (firstCorrect : first.Solves firstProblem) (secondCorrect : second.Solves secondProblem) :
    (parallelQuantum (allowAllocation := allowAllocation) join separate first second).Solves
      (Problem.parallelQuantum join separate firstProblem secondProblem) where
  success environment witness _Reference input valid initialized :=
    algorithm_parallelQuantum_success join separate first second firstProblem secondProblem
      firstCorrect secondCorrect environment witness input ⟨valid, initialized⟩
  states environment witness _Reference input valid initialized requirement present :=
    algorithm_parallelQuantum_states join separate first second firstProblem secondProblem
      firstCorrect secondCorrect environment witness input ⟨valid, initialized⟩ requirement present
  borrowed environment witness _Reference input valid initialized :=
    algorithm_parallelQuantum_borrowed join separate first second firstProblem secondProblem
      firstCorrect secondCorrect environment witness input ⟨valid, initialized⟩
  events environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelQuantum_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).1
  resident environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelQuantum_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).2.1
  auxiliary environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelQuantum_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).2.2.1
  time environment witness _Reference input valid initialized path supported :=
    (algorithm_parallelQuantum_resource_bounds join separate first second
      firstProblem secondProblem firstCorrect secondCorrect environment witness input
      ⟨valid, initialized⟩ path supported).2.2.2

end

end QuantumAlg.Algorithm
