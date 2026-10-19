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

/-- Quantum computation time charges native gates and quantum queries only.
Classical processing, classical queries, measurement, and fresh zero preparation
have zero duration. Derived preparation and reset still charge their actual gates. -/
@[expose] public def quantumDuration {model : ExecutionModel} : Event model → Nat
  | .gate _ => 1
  | .oracle _ => 1
  | .classicalOperation _ => 0
  | .classicalQuery _ => 0
  | .preparation _ => 0
  | .measurement _ => 0

@[simp] public lemma quantumDuration_gate {model : ExecutionModel}
    (coordinate : model.GateCoordinate) :
    quantumDuration (.gate coordinate : Event model) = 1 := rfl

@[simp] public lemma quantumDuration_oracle {model : ExecutionModel}
    (coordinate : model.OracleCoordinate) :
    quantumDuration (.oracle coordinate : Event model) = 1 := rfl

@[simp] public lemma quantumDuration_classicalOperation {model : ExecutionModel}
    (coordinate : model.ClassicalCoordinate) :
    quantumDuration (.classicalOperation coordinate : Event model) = 0 := rfl

@[simp] public lemma quantumDuration_classicalQuery {model : ExecutionModel}
    (coordinate : model.ClassicalOracleCoordinate) :
    quantumDuration (.classicalQuery coordinate : Event model) = 0 := rfl

@[simp] public lemma quantumDuration_preparation {model : ExecutionModel}
    (dimension : model.SystemDimension) :
    quantumDuration (.preparation dimension : Event model) = 0 := rfl

@[simp] public lemma quantumDuration_measurement {model : ExecutionModel}
    (dimension : model.SystemDimension) :
    quantumDuration (.measurement dimension : Event model) = 0 := rfl

/-- Unit event duration is an upper bound for the canonical quantum duration. -/
public lemma quantumDuration_le_one {model : ExecutionModel} (event : Event model) :
    event.quantumDuration ≤ 1 := by
  cases event <;> simp [quantumDuration]

/-- A model with only classical grants cannot emit a positive-duration quantum event. -/
@[simp] public lemma quantumDuration_classical
    {operations : ClassicalOpModel} {oracles : ClassicalOracleModel}
    (event : Event (.classical operations oracles)) : event.quantumDuration = 0 := by
  cases event with
  | classicalOperation => rfl
  | classicalQuery => rfl
  | gate impossible => exact nomatch impossible
  | oracle impossible => exact nomatch impossible
  | preparation impossible => exact nomatch impossible
  | measurement impossible => exact nomatch impossible

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
@[simp] public lemma liftClassical_classicalOperation {model : ExecutionModel}
    (coordinate : model.ClassicalCoordinate) :
    liftClassical (.classicalOperation coordinate :
      Event (.classical model.classicalOperations model.classicalOracles)) =
      (.classicalOperation coordinate : Event model) := rfl

/-- Structural inclusion preserves the selected classical query coordinate. -/
@[simp] public lemma liftClassical_classicalQuery {model : ExecutionModel}
    (coordinate : model.ClassicalOracleCoordinate) :
    liftClassical (.classicalQuery coordinate :
      Event (.classical model.classicalOperations model.classicalOracles)) =
      (.classicalQuery coordinate : Event model) := rfl

/-- Exact declaration coordinates remain distinct under structural inclusion. -/
public lemma liftClassical_injective (model : ExecutionModel) :
    Function.Injective (liftClassical (model := model)) := by
  intro left right equality
  cases left <;> cases right <;> try cases ‹Empty›
  all_goals simp_all [liftClassical]

/-- A finite system's preparation and measurement retain its actual dimension. -/
public lemma measurement_dimension_injective (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (classicalOracles : ClassicalOracleModel) :
    Function.Injective
      (measurement (model := .quantum gates oracles operations classicalOracles)) := by
  intro left right same
  cases same
  rfl

end Event

end QuantumAlg.Resource
