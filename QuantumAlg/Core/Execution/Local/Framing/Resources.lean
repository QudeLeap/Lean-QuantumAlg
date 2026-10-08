/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Context.Union.Unitary
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Actual path resources of local circuit framing

The compiler preserves the ordered native events and their evaluated
dependencies. Every visited context contains both real input contexts,
including all quantum dimensions and all classical cells. These equations
are projections of the emitted circuit and its own finite paths.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

open scoped BigOperators

/-- The emitted circuit remains a member of the same allocation-free local fragment. -/
theorem frameLocal_isLocal : {model : ExecutionModel} →
    {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) → (frame : RuntimeCtx model.kind) →
    (separate : RuntimeCtx.StorageDisjoint pre frame) →
    (frameLocal code supported frame separate).IsLocal
  | _, _, _, .id _, _, _, _ => trivial
  | _, _, _, .classical _, supported, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _ => False.elim supported
  | _, _, _, .unitary _, _, _, _ => trivial
  | _, _, _, .measureZ _ _, _, _, _ => trivial
  | _, _, _, .retain _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, frame, separate =>
      ⟨frameLocal_isLocal first supported.1 frame separate,
        frameLocal_isLocal second supported.2 frame
          (localPostDisjoint first supported.1 frame separate)⟩
  | _, _, _, .branch _ body, supported, frame, separate =>
      fun value => frameLocal_isLocal (body value) (supported value) frame separate
  | _, _, _, .iterate _ body, supported, frame, separate =>
      frameLocal_isLocal body supported frame separate
  | _, _, _, .workspace _ _ _ _ _, supported, _, _ => False.elim supported

/-- The corresponding actual paths have identical ordered native events. -/
theorem frameLocal_eventTrace : {model : ExecutionModel} →
    {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) → (frame : RuntimeCtx model.kind) →
    (separate : RuntimeCtx.StorageDisjoint pre frame) → (path : code.Path) →
    (frameLocal code supported frame separate).eventTrace
      (frameLocalPathEquiv code supported frame separate path) = code.eventTrace path
  | _, _, _, .id _, _, _, _, _ => rfl
  | _, _, _, .classical _, supported, _, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _, _ => False.elim supported
  | _, _, _, .unitary (ctx := ctx) (operations := operations)
      (classicalOracles := services) program, _, frame, separate, _ =>
      contextUnion_frameUnitary_eventTrace ctx frame separate program operations services
  | _, _, _, .measureZ (gates := gates) (oracles := oracles) (ctx := ctx)
      (operations := operations) (classicalOracles := services) wire _, _, frame, separate, _ => by
      change [Circuit.zEvent (gates := gates) (oracles := oracles)
        ((ctx.disjointUnion frame separate).quantumLayout.wire
          (leftPosition ctx frame separate wire)).dimension operations services] =
          [Circuit.zEvent (gates := gates) (oracles := oracles)
            (ctx.quantumLayout.wire wire).dimension operations services]
      rw [contextUnion_left_dimension]
  | _, _, _, .retain _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, frame, separate, path =>
      congrArg₂ List.append (frameLocal_eventTrace first supported.1 frame separate path.1)
        (frameLocal_eventTrace second supported.2 frame
          (localPostDisjoint first supported.1 frame separate) path.2)
  | _, _, _, .branch _ body, supported, frame, separate, path =>
      frameLocal_eventTrace (body path.1) (supported path.1) frame separate path.2
  | _, _, _, .iterate count body, supported, frame, separate, path =>
      congrArg List.flatten (congrArg List.ofFn (funext fun index : Fin count =>
        frameLocal_eventTrace body supported frame separate (path index)))
  | _, _, _, .workspace _ _ _ _ _, supported, _, _, _ => False.elim supported

/-- Actual resource multiplicities follow by projecting the same ordered event trace. -/
theorem frameLocal_resourcePool {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) (frame : RuntimeCtx model.kind)
    (separate : RuntimeCtx.StorageDisjoint pre frame) (path : code.Path) :
    (frameLocal code supported frame separate).resourcePool
      (frameLocalPathEquiv code supported frame separate path) = code.resourcePool path :=
  congrArg ResourcePool.ofList (frameLocal_eventTrace code supported frame separate path)

/-- Framing preserves the actual depth for every assignment of native event durations. -/
theorem frameLocal_depth : {model : ExecutionModel} →
    {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → (supported : code.IsLocal) → (frame : RuntimeCtx model.kind) →
    (separate : RuntimeCtx.StorageDisjoint pre frame) →
    (duration : Resource.Event model → Nat) → (path : code.Path) →
    (frameLocal code supported frame separate).depth duration
      (frameLocalPathEquiv code supported frame separate path) = code.depth duration path
  | _, _, _, .id _, _, _, _, _, _ => rfl
  | _, _, _, .classical _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .unitary (ctx := ctx) (operations := operations)
      (classicalOracles := services) program, _, frame, separate, duration, _ =>
      contextUnion_frameUnitary_evaluatedEventDepth ctx frame separate program
        operations services duration
  | _, _, _, .measureZ (gates := gates) (oracles := oracles) (ctx := ctx)
      (operations := operations) (classicalOracles := services) wire _,
      _, frame, separate, duration, _ => by
      change duration (Circuit.zEvent (gates := gates) (oracles := oracles)
        ((ctx.disjointUnion frame separate).quantumLayout.wire
          (leftPosition ctx frame separate wire)).dimension operations services) =
          duration (Circuit.zEvent (gates := gates) (oracles := oracles)
            (ctx.quantumLayout.wire wire).dimension operations services)
      rw [contextUnion_left_dimension]
  | _, _, _, .retain _ _ _ _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, frame, separate, duration, path =>
      congrArg₂ Nat.add (frameLocal_depth first supported.1 frame separate duration path.1)
        (frameLocal_depth second supported.2 frame
          (localPostDisjoint first supported.1 frame separate) duration path.2)
  | _, _, _, .branch _ body, supported, frame, separate, duration, path =>
      frameLocal_depth (body path.1) (supported path.1) frame separate duration path.2
  | _, _, _, .iterate count body, supported, frame, separate, duration, path =>
      congrArg (fun value : Nat => 0 + value)
        (Finset.sum_congr rfl fun index : Fin count => fun _ =>
          frameLocal_depth body supported frame separate duration (path index))
  | _, _, _, .workspace _ _ _ _ _, supported, _, _, _, _ => False.elim supported

private theorem local_visited : {model : ExecutionModel} →
    {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → code.IsLocal → (path : code.Path) →
    (visited : RuntimeCtx model.kind) → visited ∈ code.visitedContexts path → visited = pre
  | _, _, _, .id _, _, _, _, present => List.mem_singleton.mp present
  | _, _, _, .classical _, supported, _, _, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _, _, _ => False.elim supported
  | _, _, _, .unitary _, _, _, _, present => List.mem_singleton.mp present
  | _, _, _, .measureZ _ _, _, _, _, present => List.mem_singleton.mp present
  | _, _, _, .retain _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _, _, _ => False.elim supported
  | _, _, _, .seq first second, supported, path, visited, present => by
      rcases List.mem_append.mp present with before | after
      · exact local_visited first supported.1 path.1 visited before
      · exact (local_visited second supported.2 path.2 visited after).trans
          (first.isLocal_endpoints supported.1).symm
  | _, _, _, .branch _ body, supported, path, visited, present =>
      local_visited (body path.1) (supported path.1) path.2 visited present
  | _, _, _, .iterate _ body, supported, path, visited, present => by
      rcases List.mem_cons.mp present with same | later
      · exact same
      · obtain ⟨part, inParts, inPart⟩ := List.mem_flatten.mp later
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp inParts
        exact local_visited body supported (path index) visited inPart
  | _, _, _, .workspace _ _ _ _ _, supported, _, _, _ => False.elim supported

private theorem local_pre_mem : {model : ExecutionModel} →
    {pre post : RuntimeCtx model.kind} →
    (code : Circuit model pre post) → code.IsLocal → (path : code.Path) →
    pre ∈ code.visitedContexts path
  | _, _, _, .id _, _, _ => List.mem_singleton_self _
  | _, _, _, .classical _, supported, _ => False.elim supported
  | _, _, _, .classicalQuery _, supported, _ => False.elim supported
  | _, _, _, .unitary _, _, _ => List.mem_singleton_self _
  | _, _, _, .measureZ _ _, _, _ => List.mem_singleton_self _
  | _, _, _, .retain _ _ _ _, supported, _ => False.elim supported
  | _, _, _, .prepareZero _ _ _ _ _, supported, _ => False.elim supported
  | _, _, _, .seq first _second, supported, path =>
      List.mem_append_left _ (local_pre_mem first supported.1 path.1)
  | _, _, _, .branch _ body, supported, path =>
      local_pre_mem (body path.1) (supported path.1) path.2
  | _, _, _, .iterate _ _, _, _ => List.mem_cons_self
  | _, _, _, .workspace _ _ _ _ _, supported, _ => False.elim supported

/-- Every actual compiled path keeps exactly the complete union context resident. -/
theorem frameLocal_visited {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) (frame : RuntimeCtx model.kind)
    (separate : RuntimeCtx.StorageDisjoint pre frame)
    (path : (frameLocal code supported frame separate).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (frameLocal code supported frame separate).visitedContexts path) :
    visited = pre.disjointUnion frame separate :=
  local_visited _ (frameLocal_isLocal code supported frame separate) path visited present

/-- All native-dimensional resident space, including classical cells on both sides, is counted. -/
theorem frameLocal_peakResidentSpace {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) (frame : RuntimeCtx model.kind)
    (separate : RuntimeCtx.StorageDisjoint pre frame)
    (path : (frameLocal code supported frame separate).Path) :
    (frameLocal code supported frame separate).peakResidentSpace path =
      pre.residentSpace + frame.residentSpace := by
  let compiled := frameLocal code supported frame separate
  have upper := compiled.peakResidentSpace_le_of_visited path
    (pre.disjointUnion frame separate).residentSpace (by
      intro visited present
      exact (congrArg RuntimeCtx.residentSpace
        (frameLocal_visited code supported frame separate path visited present)).le)
  have lower := compiled.residentSpace_le_peak_of_visited path
    (pre.disjointUnion frame separate)
    (local_pre_mem compiled (frameLocal_isLocal code supported frame separate) path)
  exact (le_antisymm upper lower).trans (RuntimeCtx.residentSpace_disjointUnion pre frame separate)

/-- Auxiliary roles are counted from the same actual union on every execution path. -/
theorem frameLocal_peakAuxiliarySpace {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (supported : code.IsLocal) (frame : RuntimeCtx model.kind)
    (separate : RuntimeCtx.StorageDisjoint pre frame)
    (path : (frameLocal code supported frame separate).Path) :
    (frameLocal code supported frame separate).peakAuxiliarySpace path =
      pre.auxiliarySpace + frame.auxiliarySpace := by
  let compiled := frameLocal code supported frame separate
  have upper := compiled.peakAuxiliarySpace_le_of_visited path
    (pre.disjointUnion frame separate).auxiliarySpace (by
      intro visited present
      exact (congrArg RuntimeCtx.auxiliarySpace
        (frameLocal_visited code supported frame separate path visited present)).le)
  have lower := compiled.auxiliarySpace_le_peak_of_visited path
    (pre.disjointUnion frame separate)
    (local_pre_mem compiled (frameLocal_isLocal code supported frame separate) path)
  exact (le_antisymm upper lower).trans (RuntimeCtx.auxiliarySpace_disjointUnion pre frame separate)

end

end QuantumAlg.Execution.ContextUnion
