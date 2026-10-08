/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Preparation
import all QuantumAlg.Core.Execution.Trace.Preparation

/-!
# Live space of fixed preparation beside a resident frame

Zero allocation and its fixed loading program visit the same complete prepared
context. Neither step needs another bank, even when the frame contains arbitrary
resident systems and classical storage.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

variable {ctx frame : RuntimeCtx .quantum} {count : Nat}
  (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
  (separate : RuntimeCtx.StorageDisjoint (ctx.addOwnedLayout key layout fresh disjoint) frame)

private theorem original_resident_le_prepared :
    (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate)).residentSpace ≤
    ((ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame
      separate).residentSpace := by
  rw [RuntimeCtx.residentSpace_disjointUnion, RuntimeCtx.residentSpace_disjointUnion,
    RuntimeCtx.residentSpace_addOwnedLayout]
  exact fun axis => Nat.add_le_add_right (Nat.le_add_left _ _) _

private theorem original_auxiliary_le_prepared :
    (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate)).auxiliarySpace ≤
    ((ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame
      separate).auxiliarySpace := by
  rw [RuntimeCtx.auxiliarySpace_disjointUnion, RuntimeCtx.auxiliarySpace_disjointUnion,
    RuntimeCtx.auxiliarySpace_addOwnedLayout]
  exact fun axis => Nat.add_le_add_right (Nat.le_add_left _ _) _

/-- Fixed zero preparation and loading attain exactly their final resident context. -/
theorem prepareFramed_peakResidentSpace {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    (path : (prepareFramed key layout fresh disjoint separate
      (operations := operations) (services := services) load).Path) :
    (prepareFramed key layout fresh disjoint separate load).peakResidentSpace path =
      ((ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame
        separate).residentSpace := by
  unfold Circuit.peakResidentSpace
  rw [prepareFramed_visitedContexts]
  change SpacePool.max _ (SpacePool.max _ (SpacePool.max _ 0)) = _
  rw [SpacePool.max_zero, SpacePool.max_self]
  exact SpacePool.max_eq_right
    (original_resident_le_prepared key layout fresh disjoint separate)

/-- Fixed zero preparation and loading attain exactly their final auxiliary context. -/
theorem prepareFramed_peakAuxiliarySpace {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    (path : (prepareFramed key layout fresh disjoint separate
      (operations := operations) (services := services) load).Path) :
    (prepareFramed key layout fresh disjoint separate load).peakAuxiliarySpace path =
      ((ctx.addOwnedLayout key layout fresh disjoint).disjointUnion frame
        separate).auxiliarySpace := by
  unfold Circuit.peakAuxiliarySpace
  rw [prepareFramed_visitedContexts]
  change SpacePool.max _ (SpacePool.max _ (SpacePool.max _ 0)) = _
  rw [SpacePool.max_zero, SpacePool.max_self]
  exact SpacePool.max_eq_right
    (original_auxiliary_le_prepared key layout fresh disjoint separate)

end

end QuantumAlg.Execution.ContextUnion
