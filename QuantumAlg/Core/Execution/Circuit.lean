/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Execution.Preparation
public import QuantumAlg.Core.Execution.Classical.Call
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Classical.Call
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Typed circuits with classical storage and intermediate Z measurement

Every instruction is indexed by its exact live input and output contexts.
Quantum operations act on the single register derived from that context's
physical wires and dimensions. Z measurement writes its actual outcome into
an existing finite classical register and preserves every quantum wire.
Classical branching reads an existing shaped value before selecting a body.

The same syntax determines execution, paths, native events, and live-space
visits. Only classical workspace has lexical release. Preparing fresh quantum
systems grows the live context; subsequent measurement does not undo that
allocation.
-/

namespace QuantumAlg

/-- The instruction language for one exact finite classical or quantum computation. -/
public inductive Circuit : {kind : ProblemKind} → RuntimeCtx kind → RuntimeCtx kind → Type 1 where
  /-- Perform no operation and keep the live context. -/
  | id {kind : ProblemKind} (ctx : RuntimeCtx kind) : Circuit ctx ctx
  /-- Read the atomic operation's typed inputs and write its computed output. -/
  | classical {kind : ProblemKind} {ctx : RuntimeCtx kind} {input output : CShape}
      (op : ClassicalOp input output ctx ctx) : Circuit ctx ctx
  /-- Execute a declaration-owned classical subroutine at its actual references. -/
  | declaredCall {kind : ProblemKind} {ctx : RuntimeCtx kind} {input output : CShape}
      (call : DeclaredClassicalCall ctx input output) : Circuit ctx ctx
  /-- Apply a certified pure circuit on exactly the live register and placement. -/
  | unitary {ctx : RuntimeCtx .quantum} (program : UnitaryCircuit ctx.register)
      (placement : program.physical_idx = ctx.physicalIdx) : Circuit ctx ctx
  /-- Measure one wire and store its observed finite value, retaining all wires. -/
  | measureZ {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
      (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
      Circuit ctx ctx
  /-- Generate uniformly random bits and write them into the actual output cell. -/
  | randomBits {kind : ProblemKind} {ctx : RuntimeCtx kind} (width : Nat)
      (output : CWriteRef ctx (.bits width)) : Circuit ctx ctx
  /-- Allocate one retained classical cell with the shape's canonical initial encoding. -/
  | retain {kind : ProblemKind} (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
      (fresh : key ∉ ctx.keys) : Circuit ctx (ctx.addRetained key shape fresh)
  /-- Allocate and prepare fresh physical systems beside the complete existing register. -/
  | prepare (ctx : RuntimeCtx .quantum) (key : StorageKey)
      {systemCount : Nat} (layout : QuantumLayout systemCount)
      (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
      (preparation : BasisPreparation layout) :
      Circuit ctx (ctx.addOwnedLayout key layout fresh disjoint)
  /-- Execute the second instruction after the first, matching their exact contexts. -/
  | seq {kind : ProblemKind} {pre mid post : RuntimeCtx kind}
      (first : Circuit pre mid) (second : Circuit mid post) : Circuit pre post
  /-- Read one actual classical value and execute its corresponding branch. -/
  | branch {kind : ProblemKind} {pre post : RuntimeCtx kind} {shape : CShape}
      (input : CInputRef pre shape) (body : shape.Value → Circuit pre post) : Circuit pre post
  /-- Repeat a context-preserving body an exact finite number of times. -/
  | iterate {kind : ProblemKind} {ctx : RuntimeCtx kind}
      (count : Nat) (body : Circuit ctx ctx) : Circuit ctx ctx
  /-- Allocate classical workspace, execute the body, and release that exact head cell. -/
  | workspace {kind : ProblemKind} (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
      (fresh : key ∉ ctx.keys)
      (body : Circuit (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh)) :
      Circuit ctx ctx

namespace Circuit

/-- Finite execution records preserve observed outcomes and selected branch bodies.
These mathematical records do not introduce physical runtime storage. -/
@[expose, implicit_reducible]
public def Path {kind : ProblemKind} {pre post : RuntimeCtx kind} : Circuit pre post → Type
  | .id _ => Unit
  | .classical _ => Unit
  | .declaredCall _ => Unit
  | .unitary _ _ => Unit
  | .measureZ (ctx := ctx) wire _ => Fin (ctx.quantumLayout.wire wire).dimension
  | .randomBits width _ => Fin (2 ^ width)
  | .retain _ _ _ _ => Unit
  | .prepare _ _ _ _ _ _ => Unit
  | .seq first second => first.Path × second.Path
  | .branch (shape := shape) _ body => (value : shape.Value) × (body value).Path
  | .iterate count body => Fin count → body.Path
  | .workspace _ _ _ _ body => body.Path

/-- Each exact finite circuit has a finite type of complete execution records. -/
public noncomputable instance pathFintype {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) : Fintype code.Path := by
  induction code with
  | id | classical | declaredCall | unitary | measureZ | randomBits | retain | prepare =>
      dsimp [Path]
      infer_instance
  | seq first second firstIH secondIH =>
      letI := firstIH
      letI := secondIH
      exact inferInstanceAs (Fintype (first.Path × second.Path))
  | branch input body bodyIH =>
      letI := bodyIH
      exact inferInstanceAs (Fintype ((value : _) × (body value).Path))
  | iterate count body bodyIH =>
      letI := bodyIH
      exact inferInstanceAs (Fintype (Fin count → body.Path))
  | workspace ctx key shape fresh body bodyIH => exact bodyIH

end Circuit

end QuantumAlg
