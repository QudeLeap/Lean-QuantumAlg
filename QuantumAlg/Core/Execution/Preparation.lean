/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Basis
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.State.Basis
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# Fixed zero preparation on fresh physical systems

Each allocated wire is prepared in its zero computational-basis state and
emits one preparation event at its actual positive dimension. Independent fresh
systems may be prepared in parallel. The circuit constructor checks allocation
and disjointness from the complete existing context.
-/

namespace QuantumAlg.ZeroPreparation

/-- The sole normalized state produced by the built-in preparation instruction. -/
public noncomputable def normalized {count : Nat} (layout : QuantumLayout count) :
    NormalizedVector layout.register := (BasisPreparation.zero layout).normalized

/-- One fixed preparation event for each actual allocated physical system. -/
public def eventTrace (gates : GateModel) (oracles : OracleModel) {count : Nat}
    (layout : QuantumLayout count)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    List (Resource.Event (.quantum gates oracles operations classicalOracles)) :=
  List.ofFn fun index => .preparation (layout.wire index).dimension

/-- Literal multiplicities of those actual per-system preparations. -/
public def eventCost (gates : GateModel) (oracles : OracleModel) {count : Nat}
    (layout : QuantumLayout count)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum gates oracles operations classicalOracles) :=
  ResourcePool.ofList (eventTrace gates oracles layout operations classicalOracles)

/-- Distinct fresh wires are independent; the empty layout has no preparation depth. -/
public def eventDepth (gates : GateModel) (oracles : OracleModel) {count : Nat}
    (layout : QuantumLayout count)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    DepthExpr (Resource.Event (.quantum gates oracles operations classicalOracles)) :=
  (eventTrace gates oracles layout operations classicalOracles).foldr
    (fun event depth => .tensor (.atom event) depth) .id

/-- Every allocated system contributes exactly one fixed preparation occurrence. -/
public lemma zeroPreparation_event_count (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (layout : QuantumLayout count) :
    (eventTrace gates oracles layout).length = count := by simp [eventTrace]

/-- Empty allocation has no event and cannot hide a preparation. -/
public lemma zeroPreparation_empty_events (gates : GateModel) (oracles : OracleModel)
    (layout : QuantumLayout 0) : eventTrace gates oracles layout = [] := by
  simp [eventTrace]

end QuantumAlg.ZeroPreparation
