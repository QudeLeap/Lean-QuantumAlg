/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Identifying equal physical layouts

A proof that two layouts are equal permits the same actual circuit to be
used at either type. It changes no physical system, basis value or event.
-/

namespace QuantumAlg.UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {source target : QuantumLayout count}

/-- Use the same native construction after proving equality of its full physical layout. -/
public def castLayout (same : source = target) (body : UnitaryCircuit gates oracles source) :
    UnitaryCircuit gates oracles target := same ▸ body

/-- Layout equality transports the original exact matrix without any new operator. -/
public theorem castLayout_matrix (same : source = target)
    (body : UnitaryCircuit gates oracles source) :
    (body.castLayout same).matrix = same ▸ body.matrix := by
  cases same
  rfl

/-- Layout equality transports the actual action on raw vectors. -/
public theorem castLayout_applyVec (same : source = target)
    (body : UnitaryCircuit gates oracles source)
    (state : HilbertVector source.register) :
    (body.castLayout same).applyVec (same ▸ state) =
      same ▸ body.applyVec state := by
  cases same
  rfl

/-- Identifying equal layouts retains the complete original event sequence. -/
public theorem castLayout_eventTrace (same : source = target)
    (body : UnitaryCircuit gates oracles source) :
    (body.castLayout same).eventTrace = body.eventTrace := by
  cases same
  rfl

/-- Identifying equal layouts retains every actual native count. -/
public theorem castLayout_eventCost (same : source = target)
    (body : UnitaryCircuit gates oracles source) :
    (body.castLayout same).eventCost = body.eventCost := by
  cases same
  rfl

/-- Identifying equal layouts retains the complete dependency expression. -/
public theorem castLayout_eventDepth (same : source = target)
    (body : UnitaryCircuit gates oracles source) :
    (body.castLayout same).eventDepth = body.eventDepth := by
  cases same
  rfl

/-- Every duration assignment gives the same depth after identifying equal layouts. -/
public theorem castLayout_evaluatedEventDepth (same : source = target)
    (body : UnitaryCircuit gates oracles source)
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (body.castLayout same).evaluatedEventDepth duration = body.evaluatedEventDepth duration := by
  cases same
  rfl

end QuantumAlg.UnitaryCircuit
