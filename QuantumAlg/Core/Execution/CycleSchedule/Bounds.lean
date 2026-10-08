/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# Compositional bounds for fixed complete-cycle schedules

Bounds on abstract section paths compose without expanding their concrete
interpreters or histories. Structural regrouping transports that bound to
the same actual source circuit while retaining the fixed independent plan.
-/

namespace QuantumAlg.Circuit.CycleSchedule

noncomputable section

/-- Two certified sections with one common allowance retain that maximum
on every actual sequential path and their admitted physical boundary. -/
public theorem maximumCycleDepth_seq_le {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind} {leftShape shape : CShape}
    {leftPlan : CyclePlan model pre middle leftShape}
    {rightPlan : CyclePlan model middle post shape}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    (left : CycleSchedule leftPlan first) (right : CycleSchedule rightPlan second)
    (entry : EntryCompatible leftPlan rightPlan first)
    (boundary : IsClassical second ∨ Nonempty (RestartCleanup first))
    (duration : Resource.Event model → Nat) (limit : Nat)
    (leftBound : ∀ path : first.Path, left.maximumCycleDepth duration path ≤ limit)
    (rightBound : ∀ path : second.Path, right.maximumCycleDepth duration path ≤ limit)
    (path : (first.seq second).Path) :
    (CycleSchedule.seq first second left right entry boundary).maximumCycleDepth
      duration path ≤ limit :=
  max_le (leftBound path.1) (rightBound path.2)

/-- Structural regrouping transports a bound on abstract target paths to
every actual source path, without changing the intended completed computations. -/
public theorem maximumCycleDepth_reassociate_le {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {plan : CyclePlan model pre post shape} {source target : Circuit model pre post}
    (association : Reassociation source target) (schedule : CycleSchedule plan target)
    (duration : Resource.Event model → Nat) (limit : Nat)
    (bounded : ∀ path : target.Path, schedule.maximumCycleDepth duration path ≤ limit)
    (path : source.Path) :
    (CycleSchedule.reassociate association schedule).maximumCycleDepth duration path ≤ limit :=
  bounded (association.path path)

end

end QuantumAlg.Circuit.CycleSchedule
