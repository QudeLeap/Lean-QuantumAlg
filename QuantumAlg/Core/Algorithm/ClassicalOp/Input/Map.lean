/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Structural maps of classical input references

A typed map of storage references determines the map of every closed input
expression. Products, projections, vector entries and bit indices are retained
exactly, with no independent choice of how to transform a compound read.
-/

namespace QuantumAlg.CInputRef

/-- Map storage leaves while preserving every structural constructor and index. -/
@[expose] public def mapStorage {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (lift : ∀ {shape : CShape}, CStorageRef outer shape → CStorageRef inner shape)
    {shape : CShape} : CInputRef outer shape → CInputRef inner shape
  | .storage ref => .storage (lift ref)
  | .product left right => .product (mapStorage lift left) (mapStorage lift right)
  | .fixedVector entries => .fixedVector fun index => mapStorage lift (entries index)
  | .first input => .first (mapStorage lift input)
  | .second input => .second (mapStorage lift input)
  | .vectorGet input index => .vectorGet (mapStorage lift input) index
  | .bitsGet input index => .bitsGet (mapStorage lift input) index
  | .wordBitGet input index => .wordBitGet (mapStorage lift input) index

/-- Mapping storage leaves identically preserves the complete input expression. -/
public lemma input_mapStorage_id {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape) :
    mapStorage (fun ref => ref) input = input := by
  induction input with
  | storage ref => rfl
  | product left right leftIH rightIH => exact congrArg₂ product leftIH rightIH
  | fixedVector entries entriesIH => exact congrArg fixedVector (funext entriesIH)
  | first input ih => exact congrArg first ih
  | second input ih => exact congrArg second ih
  | vectorGet input index ih => exact congrArg (fun source => vectorGet source index) ih
  | bitsGet input index ih => exact congrArg (fun source => bitsGet source index) ih
  | wordBitGet input index ih => exact congrArg (fun source => wordBitGet source index) ih

/-- Structural mapping respects composition of the typed storage maps. -/
public lemma input_mapStorage_compose {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind}
    (first : ∀ {shape : CShape}, CStorageRef outer shape → CStorageRef middle shape)
    (second : ∀ {shape : CShape}, CStorageRef middle shape → CStorageRef inner shape)
    {shape : CShape} (input : CInputRef outer shape) :
    mapStorage (fun ref => second (first ref)) input =
      mapStorage second (mapStorage first input) := by
  induction input with
  | storage ref => rfl
  | product left right leftIH rightIH => exact congrArg₂ product leftIH rightIH
  | fixedVector entries entriesIH => exact congrArg fixedVector (funext entriesIH)
  | first input ih => exact congrArg CInputRef.first ih
  | second input ih => exact congrArg CInputRef.second ih
  | vectorGet input index ih => exact congrArg (fun source => vectorGet source index) ih
  | bitsGet input index ih => exact congrArg (fun source => bitsGet source index) ih
  | wordBitGet input index ih => exact congrArg (fun source => wordBitGet source index) ih

/-- The existing lexical workspace lift is the structural map of its storage lift. -/
public lemma input_mapStorage_underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (workspaceShape : CShape) (fresh : key ∉ ctx.keys) :
    mapStorage (fun ref => ref.underWorkspace key workspaceShape fresh) input =
      input.underWorkspace key workspaceShape fresh := by
  induction input with
  | storage ref => rfl
  | product left right leftIH rightIH => exact congrArg₂ product leftIH rightIH
  | fixedVector entries entriesIH => exact congrArg fixedVector (funext entriesIH)
  | first input ih => exact congrArg first ih
  | second input ih => exact congrArg second ih
  | vectorGet input index ih => exact congrArg (fun source => vectorGet source index) ih
  | bitsGet input index ih => exact congrArg (fun source => bitsGet source index) ih
  | wordBitGet input index ih => exact congrArg (fun source => wordBitGet source index) ih

end QuantumAlg.CInputRef
