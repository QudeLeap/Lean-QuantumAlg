/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Oracle.Signature
import all QuantumAlg.Core.Base.Classical.Oracle.Signature

/-!
# Declared classical services with independent interpretation

A query interface contains no stochastic transition law. An environment
interprets each atomic service separately. A sum retains both persistent states
and both interpretations, so querying one service cannot change the other.
Shared mutable access uses the same service sequentially, never a service sum.
-/

namespace QuantumAlg

/-- Fixed query interfaces with structural separation of independent services. -/
public inductive ClassicalOracleModel where
  /-- No queries and no persistent service information. -/
  | empty
  /-- One service with a fixed interface and an externally supplied interpretation. -/
  | service (signature : ClassicalOracleSignature)
  /-- Two independent services with distinct queries and persistent states. -/
  | sum (left right : ClassicalOracleModel)

namespace ClassicalOracleModel

/-- Exactly the query instances granted by this interface. -/
@[expose, implicit_reducible]
public def Query : ClassicalOracleModel → Type
  | .empty => Empty
  | .service signature => signature.Query
  | .sum left right => left.Query ⊕ right.Query

/-- Native coordinates retain the originating service. -/
@[expose, implicit_reducible]
public def Coordinate : ClassicalOracleModel → Type
  | .empty => Empty
  | .service signature => signature.Coordinate
  | .sum left right => left.Coordinate ⊕ right.Coordinate

/-- Persistent service state is separate from caller-addressable storage. -/
@[expose, implicit_reducible]
public def HiddenState : ClassicalOracleModel → Type
  | .empty => Unit
  | .service signature => signature.HiddenState
  | .sum left right => left.HiddenState × right.HiddenState

public instance coordinateDecidableEq : (model : ClassicalOracleModel) →
    DecidableEq model.Coordinate
  | .empty => inferInstanceAs (DecidableEq Empty)
  | .service signature => signature.coordinateDecidableEq
  | .sum left right =>
      letI := coordinateDecidableEq left
      letI := coordinateDecidableEq right
      inferInstanceAs (DecidableEq (left.Coordinate ⊕ right.Coordinate))

public instance stateFintype : (model : ClassicalOracleModel) → Fintype model.HiddenState
  | .empty => inferInstanceAs (Fintype Unit)
  | .service signature => signature.stateFintype
  | .sum left right =>
      letI := stateFintype left
      letI := stateFintype right
      inferInstanceAs (Fintype (left.HiddenState × right.HiddenState))

/-- Operand shape is fixed by the interface, independently of its interpretation. -/
@[expose, implicit_reducible]
public def inputShape : (model : ClassicalOracleModel) → model.Query → CShape
  | .empty, query => nomatch query
  | .service signature, query => signature.inputShape query
  | .sum left _, .inl query => left.inputShape query
  | .sum _ right, .inr query => right.inputShape query

/-- Visible result shape is fixed by the same query interface. -/
@[expose, implicit_reducible]
public def outputShape : (model : ClassicalOracleModel) → model.Query → CShape
  | .empty, query => nomatch query
  | .service signature, query => signature.outputShape query
  | .sum left _, .inl query => left.outputShape query
  | .sum _ right, .inr query => right.outputShape query

/-- Each actual query emits its original service coordinate. -/
@[expose, implicit_reducible]
public def coordinate : (model : ClassicalOracleModel) → model.Query → model.Coordinate
  | .empty, query => nomatch query
  | .service signature, query => signature.coordinate query
  | .sum left _, .inl query => .inl (left.coordinate query)
  | .sum _ right, .inr query => .inr (right.coordinate query)

/-- An environment assigns each independent service its own fixed transition law. -/
@[expose, implicit_reducible]
public def Interpretation : ClassicalOracleModel → Type
  | .empty => Unit
  | .service signature => signature.Interpretation
  | .sum left right => left.Interpretation × right.Interpretation

/-- Interpret one granted query while preserving every other service's hidden state. -/
@[expose, implicit_reducible]
public noncomputable def transition : (model : ClassicalOracleModel) →
    model.Interpretation → (query : model.Query) → model.HiddenState →
      (model.inputShape query).Value → PMF (model.HiddenState × (model.outputShape query).Value)
  | .empty, _, query => nomatch query
  | .service _, environment, query => environment.transition query
  | .sum left _, environment, .inl query => fun state input =>
      (left.transition environment.1 query state.1 input).map
        (fun result => ((result.1, state.2), result.2))
  | .sum _ right, environment, .inr query => fun state input =>
      (right.transition environment.2 query state.2 input).map
        (fun result => ((state.1, result.1), result.2))

/-- No-access execution has the unique empty service interpretation. -/
@[expose, implicit_reducible]
public def emptyInterpretation : Interpretation .empty := ()

/-- A stateless service interface fixes its ports and coordinates, not its sampling law. -/
@[expose, implicit_reducible]
public def stateless (Query Coordinate : Type) (equality : DecidableEq Coordinate)
    (inputShape outputShape : Query → CShape) (coordinate : Query → Coordinate) :
    ClassicalOracleModel :=
  .service
    { Query := Query
      Coordinate := Coordinate
      coordinateDecidableEq := equality
      HiddenState := Unit
      stateFintype := inferInstance
      inputShape := inputShape
      outputShape := outputShape
      coordinate := coordinate }

/-- An external stateless sampling law is interpreted through the ordinary service boundary. -/
@[expose, implicit_reducible]
public noncomputable def statelessInterpretation (Query Coordinate : Type)
    (equality : DecidableEq Coordinate) (inputShape outputShape : Query → CShape)
    (coordinate : Query → Coordinate)
    (sample : (query : Query) → (inputShape query).Value → PMF (outputShape query).Value) :
    (stateless Query Coordinate equality inputShape outputShape coordinate).Interpretation where
  transition query _ input := (sample query input).map (fun result => ((), result))

/-- Empty classical access cannot produce an executable query. -/
public lemma no_empty_classical_oracle_query (query : empty.Query) : False :=
  nomatch query

end ClassicalOracleModel

end QuantumAlg
