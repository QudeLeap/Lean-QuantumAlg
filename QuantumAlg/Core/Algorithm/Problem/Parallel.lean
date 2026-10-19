/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem.Embedding
public import QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
public import QuantumAlg.Core.Base.Accounting.Event.Composition
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Base.Accounting.Event.Composition
import all QuantumAlg.Core.Base.Model

/-!
# Independent contracts for disjoint parallel execution

Admission observes both original local caller and service marginals. It does
not condition on another child's result or assume product inputs. Joint
success uses the sum of failure allowances, while state requirements retain
each original external reference. Native events add at their actual routed
coordinates; simultaneous storage adds and quantum time takes the maximum.
All limits are functions of the supplied problems, never of a candidate run.
-/

namespace QuantumAlg.Problem

noncomputable section

/-- The joint guarantee obtained by adding the two independent failure allowances. -/
public def jointLowerBound (first second : ProbabilityLowerBound) :
    ProbabilityLowerBound where
  value := 1 - ((1 - first.value) + (1 - second.value))
  le_one := tsub_le_self

/-- Preserve both original classical contracts on their disjoint, fully resident contexts. -/
@[expose] public def parallelClassical {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Problem (.classical operations leftService) left left leftShape)
    (second : Problem (.classical operations rightService) right right rightShape) :
    Problem (.classical operations parentService) (left.disjointUnion right separate)
      (left.disjointUnion right separate) (.product leftShape rightShape) :=
  let leftPlacement := ContextEmbedding.alongUnion left right separate
  let rightPlacement := ContextEmbedding.alongUnionRight left right separate
  { Witness := first.Witness × second.Witness
    valid := fun environment witness state =>
      first.valid
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
          (leftPlacement.projectLocal state
            (fun store => (leftPlacement.store store).1)) ∧
      second.valid
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
          (rightPlacement.projectLocal state
            (fun store => (rightPlacement.store store).1))
    initialization := fun environment witness state =>
      first.initialization
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
          (leftPlacement.projectLocal state
            (fun label => ((leftPlacement.store label.1).1, (join.hidden label.2).1))) ∧
      second.initialization
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
          (rightPlacement.projectLocal state
            (fun label => ((rightPlacement.store label.1).1, (join.hidden label.2).2)))
    accepts := fun environment witness original result => match result with
      | .product firstResult secondResult =>
          first.accepts
            ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
            (leftPlacement.store original).1 firstResult ∧
          second.accepts
            ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
            (rightPlacement.store original).1 secondResult
    successLB := fun environment witness => jointLowerBound
      (first.successLB
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1)
      (second.successLB
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2)
    states := fun environment witness =>
      (first.states
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1).map
          (StateRequirement.embed leftPlacement) ++
      (second.states
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2).map
          (StateRequirement.embed rightPlacement)
    resources :=
      { events := first.resources.events.map (Resource.Event.serviceClassicalLeft join operations) +
          second.resources.events.map (Resource.Event.serviceClassicalRight join operations)
        resident := fun axis : SpaceAxis .classical =>
          first.resources.resident axis + second.resources.resident axis
        auxiliary := fun axis : SpaceAxis .classical =>
          first.resources.auxiliary axis + second.resources.auxiliary axis }
    quantumTimeLimit := max first.quantumTimeLimit second.quantumTimeLimit }

/-- Preserve both original quantum contracts on their disjoint, fully resident contexts. -/
@[expose] public def parallelQuantum {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {leftShape rightShape : CShape}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Problem (.quantum gates oracles operations leftService) left left leftShape)
    (second : Problem (.quantum gates oracles operations rightService) right right rightShape) :
    Problem (.quantum gates oracles operations parentService) (left.disjointUnion right separate)
      (left.disjointUnion right separate) (.product leftShape rightShape) :=
  let leftPlacement := ContextEmbedding.alongUnion left right separate
  let rightPlacement := ContextEmbedding.alongUnionRight left right separate
  { Witness := first.Witness × second.Witness
    valid := fun environment witness state =>
      first.valid
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
          (leftPlacement.projectLocal state
            (fun store => (leftPlacement.store store).1)) ∧
      second.valid
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
          (rightPlacement.projectLocal state
            (fun store => (rightPlacement.store store).1))
    initialization := fun environment witness state =>
      first.initialization
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
          (leftPlacement.projectLocal state
            (fun label => ((leftPlacement.store label.1).1, (join.hidden label.2).1))) ∧
      second.initialization
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
          (rightPlacement.projectLocal state
            (fun label => ((rightPlacement.store label.1).1, (join.hidden label.2).2)))
    accepts := fun environment witness original result => match result with
      | .product firstResult secondResult =>
          first.accepts
            ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1
            (leftPlacement.store original).1 firstResult ∧
          second.accepts
            ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2
            (rightPlacement.store original).1 secondResult
    successLB := fun environment witness => jointLowerBound
      (first.successLB
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1)
      (second.successLB
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2)
    states := fun environment witness =>
      (first.states
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ witness.1).map
          (StateRequirement.embed leftPlacement) ++
      (second.states
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ witness.2).map
          (StateRequirement.embed rightPlacement)
    resources :=
      { events := first.resources.events.map
          (Resource.Event.serviceQuantumLeft join gates oracles operations) +
          second.resources.events.map
            (Resource.Event.serviceQuantumRight join gates oracles operations)
        resident := fun axis : SpaceAxis .quantum =>
          first.resources.resident axis + second.resources.resident axis
        auxiliary := fun axis : SpaceAxis .quantum =>
          first.resources.auxiliary axis + second.resources.auxiliary axis }
    quantumTimeLimit := max first.quantumTimeLimit second.quantumTimeLimit }

end

end QuantumAlg.Problem
