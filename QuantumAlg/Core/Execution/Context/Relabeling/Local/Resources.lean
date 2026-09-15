/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.Local
import all QuantumAlg.Core.Execution.Local.Framing.Resources

/-!
# Actual local resources under injective placement

Every corresponding path retains the entire emitted native event list and
evaluated dependency depth. Each visited context contains precisely the mapped
original entries, so both complete resident space and fixed-role auxiliary
space retain all original native coordinates.
-/

namespace QuantumAlg.Execution.ContextRelabeling

noncomputable section

open scoped BigOperators

/-- Corresponding paths emit exactly the same native events in the same order. -/
theorem localCircuit_eventTrace : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    (code : Circuit pre post) → (supported : code.IsLocal) →
    (keys : StorageKey ↪ StorageKey) → (physical : Nat ↪ Nat) → (path : code.Path) →
    (localCircuit code supported keys physical).eventTrace
      (localPathEquiv code supported keys physical path) = code.eventTrace path
  | _, _, _, .id _, _, _, _, _ => rfl
  | _, _, _, .classical _, supported, _, _, _ => False.elim supported
  | _, _, _, .declaredCall _, supported, _, _, _ => False.elim supported
  | _, _, _, .unitary (ctx := ctx) program placed, _, keys, physical, _ =>
      unitaryProgram_trace ctx keys physical program placed
  | _, _, _, .measureZ (ctx := ctx) wire _, _, keys, physical, _ => by
      change [Circuit.zEvent ((ctx.relabel keys physical).quantumLayout.wire
        (positions ctx keys physical wire)).dimension] =
          [Circuit.zEvent (ctx.quantumLayout.wire wire).dimension]
      rw [positions_dimension]
  | _, _, _, .randomBits _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .retain _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .prepare _ _ _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, keys, physical, path =>
      congrArg₂ List.append (localCircuit_eventTrace first supported.1 keys physical path.1)
        (localCircuit_eventTrace second supported.2 keys physical path.2)
  | _, _, _, .branch _ body, supported, keys, physical, path =>
      localCircuit_eventTrace (body path.1) (supported path.1) keys physical path.2
  | _, _, _, .iterate count body, supported, keys, physical, path =>
      congrArg List.flatten (congrArg List.ofFn (funext fun index : Fin count =>
        localCircuit_eventTrace body supported keys physical (path index)))
  | _, _, _, .workspace _ _ _ _ _, supported, _, _, _ => False.elim supported

/-- Every actual native resource count is unchanged under the path correspondence. -/
theorem localCircuit_resourcePool {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal)
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) (path : code.Path) :
    (localCircuit code supported keys physical).resourcePool
      (localPathEquiv code supported keys physical path) = code.resourcePool path :=
  congrArg ResourcePool.ofList (localCircuit_eventTrace code supported keys physical path)

/-- Actual dependency depth is preserved for every assignment of native event durations. -/
theorem localCircuit_depth : {kind : ProblemKind} → {pre post : RuntimeCtx kind} →
    (code : Circuit pre post) → (supported : code.IsLocal) →
    (keys : StorageKey ↪ StorageKey) → (physical : Nat ↪ Nat) →
    (duration : Resource.Event kind → Nat) → (path : code.Path) →
    (localCircuit code supported keys physical).depth duration
      (localPathEquiv code supported keys physical path) = code.depth duration path
  | _, _, _, .id _, _, _, _, _, _ => rfl
  | _, _, _, .classical _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .declaredCall _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .unitary (ctx := ctx) program placed, _, keys, physical, duration, _ =>
      unitaryProgram_depth ctx keys physical program placed duration
  | _, _, _, .measureZ (ctx := ctx) wire _, _, keys, physical, duration, _ => by
      change duration (Circuit.zEvent ((ctx.relabel keys physical).quantumLayout.wire
        (positions ctx keys physical wire)).dimension) =
          duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension)
      rw [positions_dimension]
  | _, _, _, .randomBits _ _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .retain _ _ _ _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .prepare _ _ _ _ _ _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, keys, physical, duration, path =>
      congrArg₂ Nat.add (localCircuit_depth first supported.1 keys physical duration path.1)
        (localCircuit_depth second supported.2 keys physical duration path.2)
  | _, _, _, .branch _ body, supported, keys, physical, duration, path =>
      localCircuit_depth (body path.1) (supported path.1) keys physical duration path.2
  | _, _, _, .iterate count body, supported, keys, physical, duration, path =>
      congrArg (fun value : Nat => 0 + value)
        (Finset.sum_congr rfl fun index : Fin count => fun _ =>
          localCircuit_depth body supported keys physical duration (path index))
  | _, _, _, .workspace _ _ _ _ _, supported, _, _, _, _ => False.elim supported

/-- Every visited context contains exactly the mapped original complete live entries. -/
theorem localCircuit_visited {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal)
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (localCircuit code supported keys physical).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (localCircuit code supported keys physical).visitedContexts path) :
    visited = pre.relabel keys physical :=
  ContextUnion.local_visited _ (localCircuit_isLocal code supported keys physical)
    path visited present

/-- Actual resident peaks count every original classical cell and dimension-indexed system. -/
theorem localCircuit_peakResidentSpace {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal)
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (localCircuit code supported keys physical).Path) :
    (localCircuit code supported keys physical).peakResidentSpace path = pre.residentSpace := by
  let compiled := localCircuit code supported keys physical
  have upper := compiled.peakResidentSpace_le_of_visited path
    (pre.relabel keys physical).residentSpace (by
      intro visited present
      exact (congrArg RuntimeCtx.residentSpace
        (localCircuit_visited code supported keys physical path visited present)).le)
  have lower := compiled.residentSpace_le_peak_of_visited path (pre.relabel keys physical)
    (ContextUnion.local_pre_mem compiled (localCircuit_isLocal code supported keys physical) path)
  exact (le_antisymm upper lower).trans (pre.relabel_residentSpace keys physical)

/-- Actual auxiliary peaks retain every original ownership role and native space coordinate. -/
theorem localCircuit_peakAuxiliarySpace {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (supported : code.IsLocal)
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (localCircuit code supported keys physical).Path) :
    (localCircuit code supported keys physical).peakAuxiliarySpace path = pre.auxiliarySpace := by
  let compiled := localCircuit code supported keys physical
  have upper := compiled.peakAuxiliarySpace_le_of_visited path
    (pre.relabel keys physical).auxiliarySpace (by
      intro visited present
      exact (congrArg RuntimeCtx.auxiliarySpace
        (localCircuit_visited code supported keys physical path visited present)).le)
  have lower := compiled.auxiliarySpace_le_peak_of_visited path (pre.relabel keys physical)
    (ContextUnion.local_pre_mem compiled (localCircuit_isLocal code supported keys physical) path)
  exact (le_antisymm upper lower).trans (pre.relabel_auxiliarySpace keys physical)

end

end QuantumAlg.Execution.ContextRelabeling
