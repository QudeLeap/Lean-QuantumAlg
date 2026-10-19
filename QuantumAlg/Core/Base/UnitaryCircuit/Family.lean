/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Certified parameter-dependent circuit families

A circuit family selects actual circuits in one gate model, oracle declaration
and physical layout. Its native event pool and critical path are bounded by
proved family envelopes for every runtime parameter. Both resource projections
carry universal bounds from the actual member selected at execution time.

This is the closed bridge needed by classically randomized algorithms whose
quantum operator and native resource shape depend on a sampled public value.
-/

section

namespace QuantumAlg

/-- A family of actual circuits with universally certified strict-event
envelopes and one exact physical placement. -/
public structure UnitaryCircuitFamily (Parameter : Type) (gates : GateModel)
    (oracles : OracleModel) {count : Nat} (layout : QuantumLayout count) where
  /-- The actual circuit selected by one runtime parameter. -/
  member : Parameter → UnitaryCircuit gates oracles layout
  /-- Strict event-pool envelope for every selected member. -/
  eventEnvelope : ResourcePool (.quantum gates oracles)
  member_eventCost_le : ∀ parameter, (member parameter).eventCost ≤ eventEnvelope
  /-- Strict critical-path envelope for every selected member. -/
  depthEnvelope : DepthExpr (Resource.Event (.quantum gates oracles))
  member_eventDepth_le : ∀ parameter assignment,
    DepthExpr.depthEval assignment (member parameter).eventDepth ≤
      DepthExpr.depthEval assignment depthEnvelope

namespace UnitaryCircuitFamily

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Apply the actual circuit selected by one family parameter. -/
def applyNormalized {Parameter : Type}
    (family : UnitaryCircuitFamily Parameter gates oracles layout) (parameter : Parameter)
    (environment : oracles.Interpretation) (state : NormalizedVector layout.register) :
      NormalizedVector layout.register :=
  (family.member parameter).applyNormalized environment state

@[simp] lemma applyNormalized_eq {Parameter : Type}
    (family : UnitaryCircuitFamily Parameter gates oracles layout) (parameter : Parameter)
    (environment : oracles.Interpretation) (state : NormalizedVector layout.register) :
    family.applyNormalized parameter environment state =
      (family.member parameter).applyNormalized environment state :=
  rfl

namespace HeterogeneousResourceFixture

private def member (single : UnitaryCircuit gates oracles layout) :
    Bool → UnitaryCircuit gates oracles layout
  | false => single
  | true => UnitaryCircuit.seq single single

/-- A regression fixture whose members share their physical layout while the
second member executes the supplied circuit twice. Both actual projections are
proved below one envelope without constructing a raw gate in the Core layer. -/
private def family (single : UnitaryCircuit gates oracles layout) :
    UnitaryCircuitFamily Bool gates oracles layout where
  member := member single
  eventEnvelope := single.eventCost + single.eventCost
  member_eventCost_le parameter := by
    cases parameter
    · rw [ResourcePool.le_iff_count]
      intro event
      simp [member]
    · simp [member]
  depthEnvelope := .seq single.eventDepth single.eventDepth
  member_eventDepth_le parameter assignment := by
    cases parameter
    · simp only [member, DepthExpr.depthEval_seq]
      exact Nat.le_add_right _ _
    · simp [member]

/-- The fixture's two selected members do not have the same event pool. -/
example (single : UnitaryCircuit gates oracles layout)
    (event : Resource.Event (.quantum gates oracles))
    (positive : 0 < ResourcePool.count event single.eventCost) :
    ((family single).member false).eventCost ≠
      ((family single).member true).eventCost := by
  intro equality
  have countEquality := congrArg (ResourcePool.count event) equality
  simp [family, member] at countEquality
  omega

/-- The fixture's two selected members do not have the same unit-cost depth. -/
example (single : UnitaryCircuit gates oracles layout)
    (positive : 0 < DepthExpr.depthEval (fun _ => 1) single.eventDepth) :
    DepthExpr.depthEval (fun _ => 1) ((family single).member false).eventDepth ≠
      DepthExpr.depthEval (fun _ => 1) ((family single).member true).eventDepth := by
  change DepthExpr.depthEval (fun _ => 1) single.eventDepth ≠
    DepthExpr.depthEval (fun _ => 1) (UnitaryCircuit.seq single single).eventDepth
  rw [UnitaryCircuit.seq_eventDepth, DepthExpr.depthEval_seq]
  omega

end HeterogeneousResourceFixture

end

end UnitaryCircuitFamily

end QuantumAlg

end
