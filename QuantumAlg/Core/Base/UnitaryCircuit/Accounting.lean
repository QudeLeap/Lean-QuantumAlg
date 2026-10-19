/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# Pure native accounting inside a hybrid execution

Selecting the surrounding classical operations and services does not alter a
pure word's actual quantum gate or query coordinates. Such a word emits no
classical operation, classical query, preparation or measurement. These are
identities of the existing recursive interpretations, without constructing a
converted circuit or changing any native coordinate.
-/

namespace QuantumAlg

noncomputable section

namespace UnitarySequence

variable {gates : GateModel} {oracles : OracleModel} {count : Nat}
  {layout : QuantumLayout count}

private lemma count_in_classical_context (body : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (event : Resource.Event (.quantum gates oracles operations services)) :
    ResourcePool.count event (body.eventCost operations services) =
      match event with
      | .gate coordinate =>
          ResourcePool.count (model := .quantum gates oracles) (.gate coordinate) body.eventCost
      | .oracle coordinate =>
          ResourcePool.count (model := .quantum gates oracles) (.oracle coordinate) body.eventCost
      | .classicalOperation _ | .classicalQuery _ | .preparation _ | .measurement _ => 0 := by
  induction body with
  | id => cases event <;> simp [eventCost]
  | leaf value =>
      cases value with
      | gate application =>
          cases event with
          | gate coordinate =>
              simp only [eventCost, UnitaryLeaf.event, ResourcePool.count_singleton]
              congr 1
              apply propext
              constructor
              · intro same
                exact congrArg (Resource.Event.gate (model := .quantum gates oracles))
                  (Resource.Event.gate.inj same)
              · intro same
                exact congrArg
                  (Resource.Event.gate (model := .quantum gates oracles operations services))
                  (Resource.Event.gate.inj same)
          | _ => simp [eventCost, UnitaryLeaf.event, ResourcePool.count_singleton]
      | oracle application =>
          cases event with
          | oracle coordinate =>
              simp only [eventCost, UnitaryLeaf.event, ResourcePool.count_singleton]
              congr 1
              apply propext
              constructor
              · intro same
                exact congrArg (Resource.Event.oracle (model := .quantum gates oracles))
                  (Resource.Event.oracle.inj same)
              · intro same
                exact congrArg
                  (Resource.Event.oracle (model := .quantum gates oracles operations services))
                  (Resource.Event.oracle.inj same)
          | _ => simp [eventCost, UnitaryLeaf.event, ResourcePool.count_singleton]
  | seq left right leftIH rightIH =>
      cases event <;> simp_all [eventCost, ResourcePool.count_add]
  | embed placement body bodyIH => exact bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      cases event <;> simp_all [eventCost, ResourcePool.count_add]
  | iterate repetitions body bodyIH =>
      cases event <;> simp_all [eventCost, ResourcePool.count_nsmul]
  | indexedProduct label steps start step startIH stepIH =>
      cases event <;>
        simp_all [eventCost, ResourcePool.count, Multiset.count_add, Multiset.count_sum']
  | macroCall name body bodyIH => exact bodyIH

private lemma unit_depth_in_classical_context (body : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    DepthExpr.depthEval (fun _ => 1) (body.eventDepth operations services) =
      DepthExpr.depthEval (fun _ => 1) body.eventDepth := by
  induction body with
  | id => rfl
  | leaf value => rfl
  | seq left right leftIH rightIH => simp [eventDepth, leftIH, rightIH]
  | embed placement body bodyIH => exact bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [eventDepth, leftIH, rightIH]
  | iterate repetitions body bodyIH => simp [eventDepth, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [eventDepth, startIH, stepIH]
  | macroCall name body bodyIH => exact bodyIH

end UnitarySequence

namespace UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel} {count : Nat}
  {layout : QuantumLayout count}

/-- The surrounding classical selection leaves every actual quantum count unchanged. -/
public lemma unitaryCircuit_event_count_classical_context
    (body : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (event : Resource.Event (.quantum gates oracles operations services)) :
    ResourcePool.count event (body.eventCost operations services) =
      match event with
      | .gate coordinate =>
          ResourcePool.count (model := .quantum gates oracles) (.gate coordinate) body.eventCost
      | .oracle coordinate =>
          ResourcePool.count (model := .quantum gates oracles) (.oracle coordinate) body.eventCost
      | .classicalOperation _ | .classicalQuery _ | .preparation _ | .measurement _ => 0 :=
  UnitarySequence.count_in_classical_context body.sequence operations services event

/-- The same native dependency graph has the same unit depth in any classical context. -/
public lemma unitaryCircuit_unit_depth_classical_context
    (body : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    DepthExpr.depthEval (fun _ => 1) (body.eventDepth operations services) =
      body.evaluatedEventDepth (fun _ => 1) :=
  UnitarySequence.unit_depth_in_classical_context body.sequence operations services

end UnitaryCircuit

end

end QuantumAlg
