/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Transport
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Actual caller-store readings through structural workspace transport

The relation compares existing typed reads of two actual stores. Workspace
entry and exit preserve it by the interpreter's real push and pop operations.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace.Transport

/-- Every transported caller read agrees with its value in the actual caller store. -/
def ReadsAs {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) (before : Store outer) (after : Store inner) : Prop :=
  ∀ {shape : CShape} (input : CInputRef outer shape),
    after.read (transport.liftInput input) = before.read input

/-- Identity transport compares an actual store with itself. -/
lemma workspaceTransport_readsAs_id {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) : (id ctx).ReadsAs store store := by
  intro shape input
  rw [liftInput_id]

/-- Agreement through identity transport is equality of actual stores. -/
lemma workspaceTransport_readsAs_id_iff {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {before after : Store ctx} : (id ctx).ReadsAs before after ↔ after = before := by
  constructor
  · intro reads
    apply Store.store_eq_of_storage_reads after before
    intro shape input
    exact reads (.storage input)
  · rintro rfl
    exact workspaceTransport_readsAs_id _

/-- Agreement of actual reads composes through nested structural transports. -/
lemma workspaceTransport_readsAs_compose {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind}
    (first : Transport outer middle) (second : Transport middle inner)
    {before : Store outer} {between : Store middle} {after : Store inner}
    (firstReads : first.ReadsAs before between)
    (secondReads : second.ReadsAs between after) :
    (first.compose second).ReadsAs before after := by
  intro shape input
  rw [liftInput_compose]
  exact (secondReads (first.liftInput input)).trans (firstReads input)

/-- Actual workspace entry preserves every transported caller reading. -/
lemma workspaceTransport_readsAs_pushWorkspace {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner)
    {before : Store outer} {after : Store inner}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (reads : transport.ReadsAs before after) :
    (transport.underWorkspace key shape fresh).ReadsAs before
      (after.pushWorkspace key shape fresh) := by
  intro observed input
  rw [liftInput_underWorkspace]
  exact (Store.read_pushWorkspace_underWorkspace after key shape fresh
    (transport.liftInput input)).trans (reads input)

/-- Actual workspace exit preserves every transported caller reading. -/
lemma workspaceTransport_readsAs_popWorkspace {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner)
    {before : Store outer} (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    {after : Store (inner.addWorkspace key shape fresh)}
    (reads : (transport.underWorkspace key shape fresh).ReadsAs before after) :
    transport.ReadsAs before (Store.popWorkspace key shape fresh after) := by
  intro observed input
  exact (Store.read_popWorkspace_underWorkspace key shape fresh after
    (transport.liftInput input)).trans (by
      simpa only [liftInput_underWorkspace] using reads input)

/-- Agreement in an extended scope is precisely agreement after popping its lexical head. -/
lemma workspaceTransport_readsAs_underWorkspace_iff {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner)
    {before : Store outer} (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    {after : Store (inner.addWorkspace key shape fresh)} :
    (transport.underWorkspace key shape fresh).ReadsAs before after ↔
      transport.ReadsAs before (Store.popWorkspace key shape fresh after) := by
  constructor
  · exact transport.workspaceTransport_readsAs_popWorkspace key shape fresh
  · intro reads observed input
    rw [liftInput_underWorkspace]
    exact (Store.read_popWorkspace_underWorkspace key shape fresh after
      (transport.liftInput input)).symm.trans (reads input)

end QuantumAlg.Execution.ClassicalWorkspace.Transport
