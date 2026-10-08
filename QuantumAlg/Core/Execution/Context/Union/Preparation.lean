/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Context.Union.Unitary
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Actual fixed preparation beside a resident frame

Disjointness of the complete prepared context ensures that the original fresh
key and every new wire remain available beside the supplied frame. The emitted
instructions allocate zero on the actual union and load fixed bits using the
selected gate model.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

variable {ctx frame : RuntimeCtx .quantum} {count : Nat}
  (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
  (separate : RuntimeCtx.StorageDisjoint (ctx.addOwnedLayout key layout fresh disjoint) frame)

include key layout fresh disjoint separate in
/-- The original context is disjoint from any frame disjoint from its complete prepared context. -/
theorem preparation_original_disjoint : RuntimeCtx.StorageDisjoint ctx frame := by
  constructor
  · have keys := (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp separate.1
    change List.Disjoint (key :: ctx.keys) frame.keys at keys
    exact (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
      (List.disjoint_left.mpr fun _ present other =>
        List.disjoint_left.mp keys (List.mem_cons_of_mem _ present) other)
  · have wires := (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp separate.2
    apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    apply List.disjoint_left.mpr
    intro wire present other
    apply List.disjoint_left.mp wires _ other
    change wire ∈ (layout.wires ++ ctx.quantumWires).map QuantumWire.identity
    rw [List.map_append]
    exact List.mem_append_right _ present

private theorem preparation_fresh_union :
    key ∉ (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate)).keys := by
  rw [RuntimeCtx.keys_disjointUnion]
  intro present
  rcases List.mem_append.mp present with original | framed
  · exact fresh original
  · have keys := (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp separate.1
    change List.Disjoint (key :: ctx.keys) frame.keys at keys
    exact List.disjoint_left.mp keys List.mem_cons_self framed

private theorem preparation_wires_union :
    List.Disjoint layout.identities (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate)).physicalIdx := by
  rw [RuntimeCtx.physicalIdx_disjointUnion]
  apply List.disjoint_left.mpr
  intro wire prepared present
  rcases List.mem_append.mp present with original | framed
  · exact List.disjoint_left.mp disjoint prepared original
  · have wires := (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp separate.2
    apply List.disjoint_left.mp wires _ framed
    change wire ∈ (layout.wires ++ ctx.quantumWires).map QuantumWire.identity
    rw [List.map_append]
    exact List.mem_append_left _
      (by simpa only [← layout_identities_eq_map_wires] using prepared)

/-- Allocate zero on the actual union while retaining the complete resident frame. -/
def prepareZeroFramed {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel} :
    Circuit (.quantum gates oracles operations services) (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate))
      ((ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame separate) :=
  Circuit.prepareZero (gates := gates) (oracles := oracles)
    (operations := operations) (classicalOracles := services) _ key layout
    (preparation_fresh_union key layout fresh disjoint separate)
    (preparation_wires_union key layout fresh disjoint separate)

/-- Prepare zero on the actual union, then load fixed bits with the model's real gates. -/
def prepareFramed {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout) :
    Circuit (.quantum gates oracles operations services) (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate))
      ((ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame separate) :=
  (prepareZeroFramed key layout fresh disjoint separate).seq
      (Circuit.unitary (operations := operations) (classicalOracles := services)
        (frameUnitary (ctx.addOwnedLayout key layout fresh disjoint)
          frame separate load))

/-- The actual trace charges zero allocation and every fixed-bit loading gate. -/
theorem prepareFramed_eventTrace {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    (path : (prepareFramed key layout fresh disjoint separate
      (operations := operations) (services := services) load).Path) :
    (prepareFramed key layout fresh disjoint separate load).eventTrace path =
      ZeroPreparation.eventTrace gates oracles layout operations services ++
        load.eventTrace operations services := by
  exact congrArg (fun events =>
    ZeroPreparation.eventTrace gates oracles layout operations services ++ events)
    (contextUnion_frameUnitary_eventTrace
      (ctx.addOwnedLayout key layout fresh disjoint) frame separate load operations services)

/-- Both the allocation and the loading gate retain the complete resident frame. -/
theorem prepareFramed_visitedContexts {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    (path : (prepareFramed key layout fresh disjoint separate
      (operations := operations) (services := services) load).Path) :
    (prepareFramed key layout fresh disjoint separate load).visitedContexts path =
      [ctx.disjointUnion frame (preparation_original_disjoint key layout fresh disjoint separate),
        (ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame separate,
        (ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame separate] := rfl

end

end QuantumAlg.Execution.ContextUnion
