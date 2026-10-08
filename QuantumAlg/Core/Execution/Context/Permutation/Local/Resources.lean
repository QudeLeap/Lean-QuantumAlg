/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.Local
import all QuantumAlg.Core.Execution.Local.Framing.Resources

/-!
# Actual resources under entry permutation

The rebuilt local circuit preserves ordered events and evaluated dependencies.
Its visited contexts contain exactly the original entries and fixed ownership
roles, so all native-dimensional resident and auxiliary coordinates agree.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

open scoped BigOperators

/-- The corresponding actual paths have identical ordered native events. -/
theorem localCircuit_eventTrace : {model : ExecutionModel} →
    {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) →
    (target : RuntimeCtx model.kind) →
    (same : pre.entries.Perm target.entries) → (path : code.Path) →
    (localCircuit code supported target same).eventTrace
      (localPathEquiv code supported target same path) = code.eventTrace path
  | _, _, _, .id _, _, _, _, _ => rfl
  | _, _, _, .classical _, supported, _, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _, _ => False.elim supported
  | _, _, _, .unitary (operations := operations)
      (classicalOracles := services) program, _, _, same, _ =>
      unitaryProgram_trace same program operations services
  | _, _, _, .measureZ (gates := gates) (oracles := oracles) (ctx := ctx)
      (operations := operations) (classicalOracles := services) wire _, _, target, same, _ => by
      change [Circuit.zEvent (gates := gates) (oracles := oracles)
        (target.quantumLayout.wire (positions same wire)).dimension operations services] =
          [Circuit.zEvent (gates := gates) (oracles := oracles)
            (ctx.quantumLayout.wire wire).dimension operations services]
      rw [positions_wire]
  | _, _, _, .retain _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, target, same, path =>
      congrArg₂ List.append (localCircuit_eventTrace first supported.1 target same path.1)
        (localCircuit_eventTrace second supported.2 target
          (postPermutation first supported.1 same) path.2)
  | _, _, _, .branch _ body, supported, target, same, path =>
      localCircuit_eventTrace (body path.1) (supported path.1) target same path.2
  | _, _, _, .iterate count body, supported, target, same, path =>
      congrArg List.flatten (congrArg List.ofFn (funext fun index : Fin count =>
        localCircuit_eventTrace body supported target same (path index)))
  | _, _, _, .workspace _ _ _ _ _, supported, _, _, _ => False.elim supported

/-- Actual resource multiplicities follow by projecting the same ordered event trace. -/
theorem localCircuit_resourcePool {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) (target : RuntimeCtx model.kind)
    (same : pre.entries.Perm target.entries) (path : code.Path) :
    (localCircuit code supported target same).resourcePool
      (localPathEquiv code supported target same path) = code.resourcePool path :=
  congrArg ResourcePool.ofList (localCircuit_eventTrace code supported target same path)

/-- Entry permutation preserves the actual depth for every assignment of native event durations. -/
theorem localCircuit_depth : {model : ExecutionModel} →
    {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) →
    (target : RuntimeCtx model.kind) →
    (same : pre.entries.Perm target.entries) →
    (duration : Resource.Event model → Nat) → (path : code.Path) →
    (localCircuit code supported target same).depth duration
      (localPathEquiv code supported target same path) = code.depth duration path
  | _, _, _, .id _, _, _, _, _, _ => rfl
  | _, _, _, .classical _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .unitary (operations := operations)
      (classicalOracles := services) program, _, _, same, duration, _ =>
      unitaryProgram_depth same program operations services duration
  | _, _, _, .measureZ (gates := gates) (oracles := oracles) (ctx := ctx)
      (operations := operations) (classicalOracles := services) wire _,
      _, target, same, duration, _ => by
      change duration (Circuit.zEvent (gates := gates) (oracles := oracles)
        (target.quantumLayout.wire (positions same wire)).dimension operations services) =
          duration (Circuit.zEvent (gates := gates) (oracles := oracles)
            (ctx.quantumLayout.wire wire).dimension operations services)
      rw [positions_wire]
  | _, _, _, .retain _ _ _ _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, target, same, duration, path =>
      congrArg₂ Nat.add (localCircuit_depth first supported.1 target same duration path.1)
        (localCircuit_depth second supported.2 target
          (postPermutation first supported.1 same) duration path.2)
  | _, _, _, .branch _ body, supported, target, same, duration, path =>
      localCircuit_depth (body path.1) (supported path.1) target same duration path.2
  | _, _, _, .iterate count body, supported, target, same, duration, path =>
      congrArg (fun value : Nat => 0 + value)
        (Finset.sum_congr rfl fun index : Fin count => fun _ =>
          localCircuit_depth body supported target same duration (path index))
  | _, _, _, .workspace _ _ _ _ _, supported, _, _, _, _ => False.elim supported

/-- Every visited context is the unchanged target of the actual local circuit. -/
theorem localCircuit_visited {model : ExecutionModel}
    {pre post target : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal)
    (same : pre.entries.Perm target.entries)
    (path : (localCircuit code supported target same).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (localCircuit code supported target same).visitedContexts path) :
    visited = target :=
  ContextUnion.local_visited _ (localCircuit_isLocal code supported target same)
    path visited present

/-- The actual resident peak counts precisely the original live entries. -/
theorem localCircuit_peakResidentSpace {model : ExecutionModel}
    {pre post target : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal)
    (same : pre.entries.Perm target.entries)
    (path : (localCircuit code supported target same).Path) :
    (localCircuit code supported target same).peakResidentSpace path = pre.residentSpace := by
  let compiled := localCircuit code supported target same
  have upper := compiled.peakResidentSpace_le_of_visited path target.residentSpace (by
    intro visited present
    exact (congrArg RuntimeCtx.residentSpace
      (localCircuit_visited code supported same path visited present)).le)
  have lower := compiled.residentSpace_le_peak_of_visited path target
    (ContextUnion.local_pre_mem compiled (localCircuit_isLocal code supported target same) path)
  exact (le_antisymm upper lower).trans (resident_space same).symm

/-- Fixed auxiliary roles give the same actual auxiliary peak after permutation. -/
theorem localCircuit_peakAuxiliarySpace {model : ExecutionModel}
    {pre post target : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal)
    (same : pre.entries.Perm target.entries)
    (path : (localCircuit code supported target same).Path) :
    (localCircuit code supported target same).peakAuxiliarySpace path = pre.auxiliarySpace := by
  let compiled := localCircuit code supported target same
  have upper := compiled.peakAuxiliarySpace_le_of_visited path target.auxiliarySpace (by
    intro visited present
    exact (congrArg RuntimeCtx.auxiliarySpace
      (localCircuit_visited code supported same path visited present)).le)
  have lower := compiled.auxiliarySpace_le_peak_of_visited path target
    (ContextUnion.local_pre_mem compiled (localCircuit_isLocal code supported target same) path)
  exact (le_antisymm upper lower).trans (auxiliary_space same).symm

end

end QuantumAlg.Execution.ContextPermutation
