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
# Classical service interfaces and interpretations

A service interface fixes the available queries, operand and result shapes,
finite hidden-state carrier and native coordinates. Its interpretation is a
separate transition law, supplied only to execution. Initial hidden state is
an actual input and is never selected again by an ordinary query.
-/

namespace QuantumAlg

/-- One classical service's query interface, without a transition law. -/
public structure ClassicalOracleSignature where
  /-- Exactly the granted parameterized queries. -/
  Query : Type
  /-- Declaration-owned native query coordinates. -/
  Coordinate : Type
  /-- Equality is required only for counting coordinates. -/
  coordinateDecidableEq : DecidableEq Coordinate
  /-- Finite persistent state, inaccessible through caller storage references. -/
  HiddenState : Type
  /-- The interface fixes the finite state carrier at its public configuration. -/
  stateFintype : Fintype HiddenState
  /-- Operand shape selected by the granted query. -/
  inputShape : Query → CShape
  /-- Visible result shape selected by the same query. -/
  outputShape : Query → CShape
  /-- Native event emitted by an occurrence of this query. -/
  coordinate : Query → Coordinate

attribute [instance] ClassicalOracleSignature.coordinateDecidableEq
attribute [instance] ClassicalOracleSignature.stateFintype

namespace ClassicalOracleSignature

/-- One fixed transition law for every query to the same persistent service. -/
public structure Interpretation (signature : ClassicalOracleSignature) where
  /-- Next hidden state and visible result are sampled jointly. -/
  transition : (query : signature.Query) → signature.HiddenState →
    (signature.inputShape query).Value →
      PMF (signature.HiddenState × (signature.outputShape query).Value)

end ClassicalOracleSignature

end QuantumAlg
