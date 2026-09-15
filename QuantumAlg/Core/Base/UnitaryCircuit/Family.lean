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

A `UnitaryCircuitFamily Parameter R` is one public family of real `UnitaryCircuit R`
objects whose strict event pool and event critical path are bounded by proved
family envelopes, while their physical layout is identical for every runtime
parameter.  The envelopes cannot replace or float free of the member circuits:
both resource projections carry universal bounds from the actual member
selected at execution time.

This is the closed bridge needed by classically randomized algorithms whose
quantum operator and native resource shape depend on a sampled public value.
-/

section

namespace QuantumAlg

/-- A family of actual circuits with universally certified strict-event
envelopes and one exact physical placement. -/
public structure UnitaryCircuitFamily (Parameter : Type) (R : Register) where
  /-- The actual circuit selected by one runtime parameter. -/
  member : Parameter → UnitaryCircuit R
  /-- Strict event-pool envelope for every selected member. -/
  eventEnvelope : ResourcePool .quantum
  member_eventCost_le : ∀ parameter, (member parameter).eventCost ≤ eventEnvelope
  /-- Strict critical-path envelope for every selected member. -/
  depthEnvelope : DepthExpr (Resource.Event .quantum)
  member_eventDepth_le : ∀ parameter assignment,
    DepthExpr.depthEval assignment (member parameter).eventDepth ≤
      DepthExpr.depthEval assignment depthEnvelope
  /-- Common physical placement, proved exact for every member. -/
  commonPhysicalIdx : List Nat
  member_physical_idx :
    ∀ parameter, (member parameter).physical_idx = commonPhysicalIdx

namespace UnitaryCircuitFamily

noncomputable section

/-- Apply the actual circuit selected by one family parameter. -/
def applyNormalized {Parameter : Type} {R : Register}
    (family : UnitaryCircuitFamily Parameter R) (parameter : Parameter)
    (state : NormalizedVector R) : NormalizedVector R :=
  (family.member parameter).applyNormalized state

@[simp] theorem applyNormalized_eq {Parameter : Type} {R : Register}
    (family : UnitaryCircuitFamily Parameter R) (parameter : Parameter)
    (state : NormalizedVector R) :
    family.applyNormalized parameter state =
      (family.member parameter).applyNormalized state :=
  rfl

namespace HeterogeneousResourceFixture

private def member {R : Register} (single : UnitaryCircuit R) : Bool → UnitaryCircuit R
  | false => single
  | true => UnitaryCircuit.seq single single

/-- A regression fixture whose members share their physical layout while the
second member executes the supplied circuit twice. Both actual projections are
proved below one envelope without constructing a raw gate in the Core layer. -/
private def family {R : Register} (single : UnitaryCircuit R) : UnitaryCircuitFamily Bool R where
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
  commonPhysicalIdx := single.physical_idx
  member_physical_idx parameter := by
    cases parameter
    · rfl
    · exact UnitaryCircuit.unionPhysicalIdx_self single.physical_idx

/-- The fixture's two selected members do not have the same event pool. -/
example {R : Register} (single : UnitaryCircuit R) (event : Resource.Event .quantum)
    (positive : 0 < ResourcePool.count event single.eventCost) :
    ((family single).member false).eventCost ≠
      ((family single).member true).eventCost := by
  intro equality
  have countEquality := congrArg (ResourcePool.count event) equality
  simp [family, member] at countEquality
  omega

/-- The fixture's two selected members do not have the same unit-cost depth. -/
example {R : Register} (single : UnitaryCircuit R)
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
