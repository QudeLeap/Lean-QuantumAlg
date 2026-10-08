/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Model
import all QuantumAlg.Core.Base.Model
import all QuantumAlg.Core.Base.Accounting.Kind

/-!
# Model-relative execution events

A native gate coordinate belongs to the selected gate model. A query coordinate
belongs to the independently granted oracle model. Zero preparation and Z
measurement retain their fixed semantics and actual positive system dimension.
No inverse or control operation on an event creates a new executable capability.
-/

namespace QuantumAlg.Resource

/-- Event coordinates of one declared execution language. -/
public inductive Event (model : ExecutionModel) where
  /-- One actual operation from the selected classical native declaration. -/
  | classicalOperation (coordinate : model.ClassicalCoordinate)
  /-- One query granted by the selected classical oracle declaration. -/
  | classicalQuery (coordinate : model.ClassicalOracleCoordinate)
  /-- One native instance emits its model-owned gate coordinate. -/
  | gate (coordinate : model.GateCoordinate)
  /-- One granted query emits its declaration-owned query coordinate. -/
  | oracle (coordinate : model.OracleCoordinate)
  /-- Prepare one fresh physical system in its zero computational-basis state. -/
  | preparation (dimension : model.SystemDimension)
  /-- Measure one actual physical system in its computational Z basis. -/
  | measurement (dimension : model.SystemDimension)
deriving DecidableEq

namespace Event

/-- Retain the same classical grants when viewing their events inside a complete model.

The source model is fixed by the target's exact declarations. This structural
inclusion cannot admit an operation or query from a different classical model.
-/
@[expose]
public def liftClassical {model : ExecutionModel} :
    Event (.classical model.classicalOperations model.classicalOracles) → Event model
  | .classicalOperation coordinate => .classicalOperation coordinate
  | .classicalQuery coordinate => .classicalQuery coordinate
  | .gate impossible => nomatch impossible
  | .oracle impossible => nomatch impossible
  | .preparation impossible => nomatch impossible
  | .measurement impossible => nomatch impossible

/-- Structural inclusion preserves the selected native coordinate. -/
@[simp] public theorem liftClassical_classicalOperation {model : ExecutionModel}
    (coordinate : model.ClassicalCoordinate) :
    liftClassical (.classicalOperation coordinate :
      Event (.classical model.classicalOperations model.classicalOracles)) =
      (.classicalOperation coordinate : Event model) := rfl

/-- Structural inclusion preserves the selected classical query coordinate. -/
@[simp] public theorem liftClassical_classicalQuery {model : ExecutionModel}
    (coordinate : model.ClassicalOracleCoordinate) :
    liftClassical (.classicalQuery coordinate :
      Event (.classical model.classicalOperations model.classicalOracles)) =
      (.classicalQuery coordinate : Event model) := rfl

/-- Exact declaration coordinates remain distinct under structural inclusion. -/
public theorem liftClassical_injective (model : ExecutionModel) :
    Function.Injective (liftClassical (model := model)) := by
  intro left right equality
  cases left <;> cases right <;> try cases ‹Empty›
  all_goals simp_all [liftClassical]

/-- A finite system's preparation and measurement retain its actual dimension. -/
public theorem measurement_dimension_injective (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (classicalOracles : ClassicalOracleModel) :
    Function.Injective
      (measurement (model := .quantum gates oracles operations classicalOracles)) := by
  intro left right same
  cases same
  rfl

end Event

end QuantumAlg.Resource
