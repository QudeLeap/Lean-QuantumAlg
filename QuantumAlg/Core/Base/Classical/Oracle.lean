/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Value
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Declared classical queries with persistent hidden state

Each query declaration fixes its operand and result shapes and a normalized
transition on its own finite hidden state. The next state and visible result
are sampled jointly. Initialization is separate from a query, so repeated calls
cannot silently restart the service or discard correlations between outputs.

Stateless sampling uses a unit hidden state. Disjoint declarations compose by
retaining both hidden states and updating only the queried component. This
interface does not grant coherent quantum access or a concrete implementation
of the black box's internal work or storage.
-/

namespace QuantumAlg

/-- Classical query access with declaration-owned finite stochastic state transitions. -/
public structure ClassicalOracleModel where
  /-- Exactly the available parameterized query instances. -/
  Query : Type
  /-- Declaration-owned query coordinates. -/
  Coordinate : Type
  /-- Query counts require decidable coordinate equality. -/
  coordinateDecidableEq : DecidableEq Coordinate
  /-- Hidden service state, separate from caller-addressable storage. -/
  HiddenState : Type
  /-- The state space is finite for these fixed model parameters. -/
  stateFintype : Fintype HiddenState
  /-- Operand shape determined by the query declaration. -/
  inputShape : Query → CShape
  /-- Visible result shape determined by the same declaration. -/
  outputShape : Query → CShape
  /-- Joint next-state and result distribution; initialization is not repeated here. -/
  transition : (query : Query) → HiddenState → (inputShape query).Value →
    PMF (HiddenState × (outputShape query).Value)
  /-- Coordinate emitted by the actual granted query instance. -/
  coordinate : Query → Coordinate

attribute [instance] ClassicalOracleModel.coordinateDecidableEq
attribute [instance] ClassicalOracleModel.stateFintype

namespace ClassicalOracleModel

/-- Empty classical access contains no query and needs no service state. -/
@[expose, implicit_reducible]
public def empty : ClassicalOracleModel where
  Query := Empty
  Coordinate := Empty
  coordinateDecidableEq := inferInstance
  HiddenState := Unit
  stateFintype := inferInstance
  inputShape query := nomatch query
  outputShape query := nomatch query
  transition query := nomatch query
  coordinate query := nomatch query

/-- A finite sampler has no mutable service state and keeps its declared distribution. -/
@[expose, implicit_reducible]
public noncomputable def stateless (Query Coordinate : Type)
    (equality : DecidableEq Coordinate) (inputShape outputShape : Query → CShape)
    (sample : (query : Query) → (inputShape query).Value → PMF (outputShape query).Value)
    (coordinate : Query → Coordinate) : ClassicalOracleModel where
  Query := Query
  Coordinate := Coordinate
  coordinateDecidableEq := equality
  HiddenState := Unit
  stateFintype := inferInstance
  inputShape := inputShape
  outputShape := outputShape
  transition query _ input := (sample query input).map (fun result => ((), result))
  coordinate := coordinate

/-- Combine disjoint query grants without merging their coordinates or hidden states. -/
@[expose, implicit_reducible]
public noncomputable def sum (left right : ClassicalOracleModel) : ClassicalOracleModel where
  Query := left.Query ⊕ right.Query
  Coordinate := left.Coordinate ⊕ right.Coordinate
  coordinateDecidableEq := inferInstance
  HiddenState := left.HiddenState × right.HiddenState
  stateFintype := inferInstance
  inputShape
    | .inl query => left.inputShape query
    | .inr query => right.inputShape query
  outputShape
    | .inl query => left.outputShape query
    | .inr query => right.outputShape query
  transition
    | .inl query, state, input =>
        (left.transition query state.1 input).map (fun result => ((result.1, state.2), result.2))
    | .inr query, state, input =>
        (right.transition query state.2 input).map (fun result => ((state.1, result.1), result.2))
  coordinate
    | .inl query => .inl (left.coordinate query)
    | .inr query => .inr (right.coordinate query)

/-- Empty classical access cannot produce an executable query. -/
public theorem no_empty_classical_oracle_query (query : empty.Query) : False :=
  nomatch query

end ClassicalOracleModel

end QuantumAlg
