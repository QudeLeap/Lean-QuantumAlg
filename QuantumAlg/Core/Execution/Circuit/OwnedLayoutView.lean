/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Time
public import QuantumAlg.Core.Execution.Context.OwnedLayoutView
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Execution.Context.OwnedLayoutView.Laws

/-!
# Scoped owned slices execute the original allocation-free child

The full classical-quantum state and arbitrary external reference pass through
the exact ordered physical coordinates and back. The scope has no native
event or depth cost, and every existing physical system remains resident.
-/

namespace QuantumAlg.Circuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {original viewed : RuntimeCtx .quantum} {allowAllocation : Bool}
  (view : OwnedLayoutView original viewed)
  (body : Circuit (.quantum gates oracles operations services) viewed viewed false)

private lemma execute_ownedLayoutView_eq
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State original Reference (services.HiddenState × H)) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).execute
      environment Reference state =
        view.join (body.execute environment Reference (view.split state)) := rfl

/-- The original child runs on the complete corresponding state, then the grouping is restored. -/
public lemma execute_ownedLayoutView
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State original Reference (services.HiddenState × H)) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).execute
      environment Reference state =
        view.join (body.execute environment Reference (view.split state)) :=
  execute_ownedLayoutView_eq view body environment Reference state

/-- Every selected actual native event is precisely the child's selected actual event. -/
public lemma eventTrace_ownedLayoutView (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).eventTrace path =
      body.eventTrace path := rfl

private lemma resourcePool_ownedLayoutView_eq (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).resourcePool path =
      body.resourcePool path := rfl

/-- Scope boundaries introduce no native event coordinate. -/
public lemma resourcePool_ownedLayoutView (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).resourcePool path =
      body.resourcePool path := resourcePool_ownedLayoutView_eq view body path

private lemma eventDepth_ownedLayoutView_eq (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).eventDepth path =
      body.eventDepth path := rfl

/-- All native dependencies of the allocation-free child are retained. -/
public lemma eventDepth_ownedLayoutView (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).eventDepth path =
      body.eventDepth path := eventDepth_ownedLayoutView_eq view body path

/-- Regrouping adds no critical-path work under any event duration model. -/
private lemma depth_ownedLayoutView_eq (duration : Resource.Event
    (.quantum gates oracles operations services) → Nat) (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).depth duration path =
      body.depth duration path := rfl

/-- Regrouping adds no critical-path work under any event duration model. -/
public lemma depth_ownedLayoutView (duration : Resource.Event
    (.quantum gates oracles operations services) → Nat) (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).depth duration path =
      body.depth duration path := depth_ownedLayoutView_eq view body duration path

/-- Quantum computation time is exactly that of the allocation-free child. -/
private lemma quantumTime_ownedLayoutView_eq (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).quantumTime path =
      body.quantumTime path := rfl

/-- Quantum computation time is exactly that of the allocation-free child. -/
public lemma quantumTime_ownedLayoutView (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).quantumTime path =
      body.quantumTime path := quantumTime_ownedLayoutView_eq view body path

/-- All original physical systems and classical cells stay resident in the scope. -/
public lemma peakResidentSpace_ownedLayoutView (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation)
      view body).peakResidentSpace path =
      body.peakResidentSpace path := by
  rw [body.fixed_peakResidentSpace, ← view.residentSpace_eq]
  change SpacePool.max original.residentSpace 0 = original.residentSpace
  exact SpacePool.max_zero _

/-- The original ownership roles give exactly the child's auxiliary peak. -/
public lemma peakAuxiliarySpace_ownedLayoutView (path : body.Path) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation)
      view body).peakAuxiliarySpace path =
      body.peakAuxiliarySpace path := by
  rw [body.fixed_peakAuxiliarySpace, ← view.auxiliarySpace_eq]
  change SpacePool.max original.auxiliarySpace 0 = original.auxiliarySpace
  exact SpacePool.max_zero _

end

end QuantumAlg.Circuit
