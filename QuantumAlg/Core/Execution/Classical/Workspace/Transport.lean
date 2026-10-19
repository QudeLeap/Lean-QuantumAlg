/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace
public import QuantumAlg.Core.Algorithm.ClassicalOp
public import QuantumAlg.Core.Algorithm.ClassicalOp.Input.Map
public import QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Algorithm.ClassicalOp.Input.Map

/-!
# Structural caller references across lexical workspace scopes

Transport preserves the exact physical support of every read and the identity
and ownership of every writable cell. It introduces no execution semantics.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- A typed storage lift preserving physical identities and ownership roles. -/
public structure Transport {kind : ProblemKind} (outer inner : RuntimeCtx kind) where
  /-- Lift one typed storage reference into the inner workspace context. -/
  liftStorage : ∀ {shape : CShape}, CStorageRef outer shape → CStorageRef inner shape
  liftStorage_key : ∀ {shape : CShape} (ref : CStorageRef outer shape),
    (liftStorage ref).key = ref.key
  liftStorage_role : ∀ {shape : CShape} (ref : CStorageRef outer shape),
    (liftStorage ref).role = ref.role

namespace Transport

/-- Lift an input by mapping only its storage leaves, retaining all constructors and indices. -/
@[expose] public def liftInput {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) {shape : CShape} (input : CInputRef outer shape) :
    CInputRef inner shape :=
  input.mapStorage transport.liftStorage

/-- The same typed storage map lifts writable references with their existing ownership. -/
@[expose] public def liftWrite {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) {shape : CShape} (output : CWriteRef outer shape) :
    CWriteRef inner shape where
  toCStorageRef := transport.liftStorage output.toCStorageRef
  writable := by
    rw [transport.liftStorage_role]
    exact output.writable

/-- A transported output retains its declared ownership role. -/
public lemma liftWrite_role {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) {shape : CShape} (output : CWriteRef outer shape) :
    (transport.liftWrite output).toCStorageRef.role = output.toCStorageRef.role :=
  transport.liftStorage_role output.toCStorageRef

/-- A transported output retains its exact physical identity. -/
public lemma liftWrite_key {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) {shape : CShape} (output : CWriteRef outer shape) :
    (transport.liftWrite output).key = output.key :=
  transport.liftStorage_key output.toCStorageRef

/-- Reading and writing use the same transported storage reference. -/
public lemma liftWrite_input {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) {shape : CShape} (output : CWriteRef outer shape) :
    transport.liftInput (.storage output.toCStorageRef) =
      .storage (transport.liftWrite output).toCStorageRef := rfl

/-- Structural lifting preserves the complete ordered support of every caller read. -/
public lemma liftInput_storageKeys {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) {shape : CShape} (input : CInputRef outer shape) :
    (transport.liftInput input).storageKeys = input.storageKeys := by
  induction input with
  | storage ref => exact congrArg List.singleton (transport.liftStorage_key ref)
  | product left right leftIH rightIH => exact congrArg₂ List.append leftIH rightIH
  | fixedVector entries entriesIH =>
      exact congrArg List.flatten (congrArg List.ofFn (funext entriesIH))
  | first input ih => exact ih
  | second input ih => exact ih
  | vectorGet input index ih => exact ih
  | bitsGet input index ih => exact ih
  | wordBitGet input index ih => exact ih

/-- Structural identity before entering a workspace scope. -/
public def id {kind : ProblemKind} (ctx : RuntimeCtx kind) : Transport ctx ctx where
  liftStorage := fun ref => ref
  liftStorage_key := fun _ => rfl
  liftStorage_role := fun _ => rfl

/-- Compose structural lifts through nested lexical scopes. -/
public def compose {kind : ProblemKind} {outer middle inner : RuntimeCtx kind}
    (first : Transport outer middle) (second : Transport middle inner) :
    Transport outer inner where
  liftStorage ref := second.liftStorage (first.liftStorage ref)
  liftStorage_key ref := (second.liftStorage_key _).trans (first.liftStorage_key ref)
  liftStorage_role ref := (second.liftStorage_role _).trans (first.liftStorage_role ref)

/-- Extend a structural lift through the actual existing workspace instruction. -/
public def underWorkspace {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys) :
    Transport outer (inner.addWorkspace key shape fresh) where
  liftStorage ref := (transport.liftStorage ref).underWorkspace key shape fresh
  liftStorage_key ref := transport.liftStorage_key ref
  liftStorage_role ref := transport.liftStorage_role ref

/-- Identity transport retains the complete caller input expression. -/
public lemma liftInput_id {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape) : (id ctx).liftInput input = input :=
  CInputRef.input_mapStorage_id input

/-- Input lifting follows the composition of its typed storage maps. -/
public lemma liftInput_compose {kind : ProblemKind} {outer middle inner : RuntimeCtx kind}
    (first : Transport outer middle) (second : Transport middle inner)
    {shape : CShape} (input : CInputRef outer shape) :
    (first.compose second).liftInput input = second.liftInput (first.liftInput input) :=
  CInputRef.input_mapStorage_compose first.liftStorage second.liftStorage input

/-- Lifting through an additional workspace uses the existing structural workspace lift. -/
public lemma liftInput_underWorkspace {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ inner.keys) {observed : CShape} (input : CInputRef outer observed) :
    (transport.underWorkspace key shape fresh).liftInput input =
      (transport.liftInput input).underWorkspace key shape fresh := by
  exact (CInputRef.input_mapStorage_compose transport.liftStorage
    (fun ref => ref.underWorkspace key shape fresh) input).trans
      (CInputRef.input_mapStorage_underWorkspace (transport.liftInput input) key shape fresh)

/-- A transported read avoids exactly the same physical keys as its caller reference. -/
public lemma workspaceTransport_input_avoids_iff {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner)
    {shape : CShape} (input : CInputRef outer shape) (key : StorageKey) :
    key ∉ (transport.liftInput input).storageKeys ↔ key ∉ input.storageKeys := by
  rw [transport.liftInput_storageKeys]

end Transport

end QuantumAlg.Execution.ClassicalWorkspace
