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
operators and physical signatures are fixed by the declaration. Inverse and
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
  /-- Each granted query has its fixed unitary semantics. -/
  operator : (query : Query) → UnitaryOperator (signature query).register
  /-- One query emits exactly the coordinate selected by its declaration. -/
  coordinate : Query → Coordinate

attribute [instance] OracleModel.coordinateDecidableEq

namespace OracleModel

/-- The absence of oracle access has no query instances and no query coordinates. -/
@[expose, implicit_reducible]
public def empty : OracleModel where
  Query := Empty
  Coordinate := Empty
  coordinateDecidableEq := inferInstance
  signature query := nomatch query
  operator query := nomatch query
  coordinate query := nomatch query

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

/-- The declaration fixes the operator; placement only transports dimension-equal coordinates. -/
@[expose]
public noncomputable def operator {model : OracleModel} (query : Occurrence model) :
    UnitaryOperator query.placement.layout.register :=
  UnitaryOperator.reindex query.placement.indexEquiv.symm (model.operator query.query)

/-- A call cannot supply an operator independently of its granted query. -/
public theorem oracle_occurrence_operator {model : OracleModel} (query : Occurrence model) :
    query.operator =
      UnitaryOperator.reindex query.placement.indexEquiv.symm (model.operator query.query) := rfl

/-- The coordinate is fixed by the same query instance that determines the operator. -/
public theorem oracle_occurrence_coordinate {model : OracleModel} (query : Occurrence model) :
    query.coordinate = model.coordinate query.query := rfl

/-- Declaring no access cannot produce an executable query occurrence. -/
public theorem no_empty_oracle_occurrence (query : Occurrence empty) : False :=
  nomatch query.query

end Occurrence

end OracleModel

end QuantumAlg
