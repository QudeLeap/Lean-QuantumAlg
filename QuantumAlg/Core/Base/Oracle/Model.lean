/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Signature
public import QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Independently declared unitary oracle access

The query type contains exactly the granted, parameterized access forms. Their
physical signatures are fixed by the declaration. An execution environment
supplies their unitary interpretation without changing the program. Inverse and
controlled queries require values of that same declared query type; Core does
not grant them by transforming a label or an operator supplied at a call site.

Oracle coordinates are independent of the selected elementary-gate model.
-/

namespace QuantumAlg

/-- A declaration of available unitary queries with their own accounting coordinates. -/
public structure OracleModel where
  /-- Exactly the query instances available to a client of this declaration. -/
  Query : Type
  /-- Query counts use declaration-owned decidable coordinates. -/
  Coordinate : Type
  /-- Counting does not require equality of arbitrary semantic parameters. -/
  coordinateDecidableEq : DecidableEq Coordinate
  /-- Ordered positive dimensions of the systems involved in the query. -/
  signature : Query → QuantumSignature
  /-- One query emits exactly the coordinate selected by its declaration. -/
  coordinate : Query → Coordinate

attribute [instance] OracleModel.coordinateDecidableEq

namespace OracleModel

/-- A mathematical interpretation of the granted queries, supplied only at execution. -/
public structure Interpretation (model : OracleModel) where
  /-- Each available query acts unitarily on exactly its declared systems. -/
  operator : (query : model.Query) → UnitaryOperator (model.signature query).register

/-- The absence of oracle access has no query instances and no query coordinates. -/
@[expose, implicit_reducible]
public def empty : OracleModel where
  Query := Empty
  Coordinate := Empty
  coordinateDecidableEq := inferInstance
  signature query := nomatch query
  coordinate query := nomatch query

/-- Empty access has one interpretation and cannot reveal any oracle information. -/
@[expose, implicit_reducible]
public def emptyInterpretation : Interpretation empty where
  operator query := nomatch query

public instance : Subsingleton (Interpretation empty) where
  allEq left right := by
    cases left with
    | mk left =>
      cases right with
      | mk right =>
        have same : left = right := funext fun query => nomatch query
        cases same
        rfl

/-- One granted query, placed on systems of exactly its declared dimensions. -/
public structure Occurrence (model : OracleModel) where
  /-- A value of the declaration's available-query type. -/
  query : model.Query
  /-- Actual physical systems used by this query. -/
  placement : (model.signature query).Placement

namespace Occurrence

/-- Query accounting follows the granted query instance. -/
@[expose]
public def coordinate {model : OracleModel} (query : Occurrence model) : model.Coordinate :=
  model.coordinate query.query

/-- The environment interprets the query; placement only transports its declared coordinates. -/
@[expose]
public noncomputable def operator {model : OracleModel} (query : Occurrence model)
    (environment : Interpretation model) :
    UnitaryOperator query.placement.layout.register :=
  UnitaryOperator.reindex query.placement.indexEquiv.symm (environment.operator query.query)

/-- A call cannot supply an operator independently of its granted query. -/
public lemma oracle_occurrence_operator {model : OracleModel} (query : Occurrence model)
    (environment : Interpretation model) :
    query.operator environment =
      UnitaryOperator.reindex query.placement.indexEquiv.symm
        (environment.operator query.query) := rfl

/-- The coordinate is fixed by the same query instance that determines the operator. -/
public lemma oracle_occurrence_coordinate {model : OracleModel} (query : Occurrence model) :
    query.coordinate = model.coordinate query.query := rfl

/-- Declaring no access cannot produce an executable query occurrence. -/
public lemma no_empty_oracle_occurrence (query : Occurrence empty) : False :=
  nomatch query.query

end Occurrence

end OracleModel

end QuantumAlg
