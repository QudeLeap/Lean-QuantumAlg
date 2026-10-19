/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Event
public import QuantumAlg.Core.Base.Classical.Oracle.Composition
import all QuantumAlg.Core.Base.Classical.Oracle.Composition

/-!
# Event coordinates for independent service composition

Only classical-query coordinates change when a child uses one side of a
service join. Every other granted operation retains its exact coordinate.
Each side's map is injective and preserves quantum duration. Their complete
images need not be disjoint: native gates and other shared grants retain
shared coordinates, whose multiplicities add across the two children.
-/

namespace QuantumAlg.Resource.Event

open ClassicalOracleModel

variable {left right parent : ClassicalOracleModel} (join : ServiceJoin left right parent)

/-- Route left classical service events without changing native operation coordinates. -/
@[expose] public def serviceClassicalLeft (operations : ClassicalOpModel) :
    Event (.classical operations left) → Event (.classical operations parent)
  | .classicalOperation coordinate => .classicalOperation coordinate
  | .classicalQuery coordinate => .classicalQuery (join.coordinateLeft coordinate)
  | .gate impossible => nomatch impossible
  | .oracle impossible => nomatch impossible
  | .preparation impossible => nomatch impossible
  | .measurement impossible => nomatch impossible

/-- Route right classical service events without changing native operation coordinates. -/
@[expose] public def serviceClassicalRight (operations : ClassicalOpModel) :
    Event (.classical operations right) → Event (.classical operations parent)
  | .classicalOperation coordinate => .classicalOperation coordinate
  | .classicalQuery coordinate => .classicalQuery (join.coordinateRight coordinate)
  | .gate impossible => nomatch impossible
  | .oracle impossible => nomatch impossible
  | .preparation impossible => nomatch impossible
  | .measurement impossible => nomatch impossible

/-- Route the left service coordinate while preserving all quantum and native grants. -/
@[expose] public def serviceQuantumLeft (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) :
    Event (.quantum gates oracles operations left) →
      Event (.quantum gates oracles operations parent)
  | .classicalOperation coordinate => .classicalOperation coordinate
  | .classicalQuery coordinate => .classicalQuery (join.coordinateLeft coordinate)
  | .gate coordinate => .gate coordinate
  | .oracle coordinate => .oracle coordinate
  | .preparation dimension => .preparation dimension
  | .measurement dimension => .measurement dimension

/-- Route the right service coordinate while preserving all quantum and native grants. -/
@[expose] public def serviceQuantumRight (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) :
    Event (.quantum gates oracles operations right) →
      Event (.quantum gates oracles operations parent)
  | .classicalOperation coordinate => .classicalOperation coordinate
  | .classicalQuery coordinate => .classicalQuery (join.coordinateRight coordinate)
  | .gate coordinate => .gate coordinate
  | .oracle coordinate => .oracle coordinate
  | .preparation dimension => .preparation dimension
  | .measurement dimension => .measurement dimension

/-- Left classical event labels remain distinct after composition. -/
public lemma event_serviceClassicalLeft_injective (operations : ClassicalOpModel) :
    Function.Injective (serviceClassicalLeft join operations) := by
  intro first second equal
  cases first <;> cases second <;> try cases ‹Empty›
  all_goals simp_all only [serviceClassicalLeft, Event.classicalOperation.injEq,
    Event.classicalQuery.injEq, reduceCtorEq]
  all_goals exact join.serviceJoin_coordinateLeft_injective equal

/-- Right classical event labels remain distinct after composition. -/
public lemma event_serviceClassicalRight_injective (operations : ClassicalOpModel) :
    Function.Injective (serviceClassicalRight join operations) := by
  intro first second equal
  cases first <;> cases second <;> try cases ‹Empty›
  all_goals simp_all only [serviceClassicalRight, Event.classicalOperation.injEq,
    Event.classicalQuery.injEq, reduceCtorEq]
  all_goals exact join.serviceJoin_coordinateRight_injective equal

/-- Left hybrid event labels remain distinct after composition. -/
public lemma event_serviceQuantumLeft_injective (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) :
    Function.Injective (serviceQuantumLeft join gates oracles operations) := by
  intro first second equal
  cases first <;> cases second
  all_goals simp_all only [serviceQuantumLeft, Event.classicalOperation.injEq,
    Event.classicalQuery.injEq, Event.gate.injEq, Event.oracle.injEq,
    Event.preparation.injEq, Event.measurement.injEq, reduceCtorEq]
  all_goals exact join.serviceJoin_coordinateLeft_injective equal

/-- Right hybrid event labels remain distinct after composition. -/
public lemma event_serviceQuantumRight_injective (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) :
    Function.Injective (serviceQuantumRight join gates oracles operations) := by
  intro first second equal
  cases first <;> cases second
  all_goals simp_all only [serviceQuantumRight, Event.classicalOperation.injEq,
    Event.classicalQuery.injEq, Event.gate.injEq, Event.oracle.injEq,
    Event.preparation.injEq, Event.measurement.injEq, reduceCtorEq]
  all_goals exact join.serviceJoin_coordinateRight_injective equal

/-- Service routing does not introduce quantum work into classical execution. -/
public lemma event_serviceClassicalLeft_duration (operations : ClassicalOpModel)
    (event : Event (.classical operations left)) :
    (serviceClassicalLeft join operations event).quantumDuration = event.quantumDuration := by
  rw [quantumDuration_classical, quantumDuration_classical]

/-- Service routing does not introduce quantum work into classical execution. -/
public lemma event_serviceClassicalRight_duration (operations : ClassicalOpModel)
    (event : Event (.classical operations right)) :
    (serviceClassicalRight join operations event).quantumDuration = event.quantumDuration := by
  rw [quantumDuration_classical, quantumDuration_classical]

/-- Routing a left service query preserves every native event's quantum duration. -/
public lemma event_serviceQuantumLeft_duration (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (event : Event (.quantum gates oracles operations left)) :
    (serviceQuantumLeft join gates oracles operations event).quantumDuration =
      event.quantumDuration := by
  cases event <;> rfl

/-- Routing a right service query preserves every native event's quantum duration. -/
public lemma event_serviceQuantumRight_duration (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (event : Event (.quantum gates oracles operations right)) :
    (serviceQuantumRight join gates oracles operations event).quantumDuration =
      event.quantumDuration := by
  cases event <;> rfl

end QuantumAlg.Resource.Event
