/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Execution.Preparation
public import QuantumAlg.Core.Execution.Classical.Native
public import QuantumAlg.Core.Execution.Classical.Query
public import QuantumAlg.Core.Execution.Store
public import QuantumAlg.Core.Base.Accounting.Context.Embedding
public import QuantumAlg.Core.Base.Classical.Oracle.Composition
import all QuantumAlg.Core.Execution.Classical.Native
import all QuantumAlg.Core.Execution.Classical.Query
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Model-relative complete classical and quantum executions

Every instruction has exact live input and output contexts and the same chosen
execution language. Native classical operations and classical queries require
tokens of the selected declarations, including randomized operations. Quantum
instructions use the context's physical layout. Preparation creates only zero
states. Z measurement retains all wires and writes its actual bounded outcome
before classical feedback chooses subsequent operations.
-/

namespace QuantumAlg

/-- Actual execution syntax sharing its operation model with the surrounding specification. -/
public inductive Circuit : (model : ExecutionModel) →
    RuntimeCtx model.kind → RuntimeCtx model.kind →
      (allowAllocation : Bool := true) → Type 1 where
  /-- Preserve the exact live context. -/
  | id {model : ExecutionModel} {allowAllocation : Bool}
      (ctx : RuntimeCtx model.kind) : Circuit model ctx ctx allowAllocation
  /-- Execute one granted classical native operation at its actual references. -/
  | classical {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
      (application : model.classicalOperations.Application ctx) :
      Circuit model ctx ctx allowAllocation
  /-- Query the selected classical service using its current persistent hidden state. -/
  | classicalQuery {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
      (application : model.classicalOracles.Application ctx) :
      Circuit model ctx ctx allowAllocation
  /-- Execute the selected language on exactly the complete live physical layout. -/
  | unitary {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
      {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
      {allowAllocation : Bool}
      (program : UnitaryCircuit gates oracles ctx.quantumLayout) :
      Circuit (.quantum gates oracles operations classicalOracles) ctx ctx allowAllocation
  /-- Measure one actual wire and retain its quantum system and classical outcome. -/
  | measureZ {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
      {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
      {allowAllocation : Bool}
      (wire : Fin ctx.systemCount)
      (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
      Circuit (.quantum gates oracles operations classicalOracles) ctx ctx allowAllocation
  /-- Allocate retained classical storage with its canonical initial encoding. -/
  | retain {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (key : StorageKey)
      (shape : CShape) (fresh : key ∉ ctx.keys) :
      Circuit model ctx (ctx.addRetained key shape fresh)
  /-- Allocate distinct fresh quantum systems and prepare every one in zero. -/
  | prepareZero {gates : GateModel} {oracles : OracleModel}
      {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
      (ctx : RuntimeCtx .quantum) (key : StorageKey) {systemCount : Nat}
      (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
      (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
      Circuit (.quantum gates oracles operations classicalOracles) ctx
        (ctx.addOwnedLayout key layout fresh disjoint)
  /-- Exact intermediate contexts and the operation model agree at composition. -/
  | seq {model : ExecutionModel} {pre mid post : RuntimeCtx model.kind}
      {allowAllocation : Bool}
      (first : Circuit model pre mid allowAllocation)
      (second : Circuit model mid post allowAllocation) : Circuit model pre post allowAllocation
  /-- Read a shaped classical value before executing its selected branch. -/
  | branch {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
      {allowAllocation : Bool}
      (input : CInputRef pre shape)
      (body : shape.Value → Circuit model pre post allowAllocation) :
      Circuit model pre post allowAllocation
  /-- Execute a context-preserving body an exact finite number of times. -/
  | iterate {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
      (count : Nat) (body : Circuit model ctx ctx allowAllocation) :
      Circuit model ctx ctx allowAllocation
  /-- Allocate, execute with and release the same lexical classical work cell. -/
  | workspace {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
      (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
      (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh)) :
      Circuit model ctx ctx
  /-- Interpret an original fixed-context child at its certified physical placement. -/
  | embed {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
      {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
      (body : Circuit model localCtx localCtx false) : Circuit model caller caller allowAllocation
  /-- Run disjoint classical children with independent persistent services. -/
  | parallelClassical {operations : ClassicalOpModel}
      {leftService rightService parentService : ClassicalOracleModel}
      {left right : RuntimeCtx .classical} {allowAllocation : Bool}
      (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
      (separate : RuntimeCtx.StorageDisjoint left right)
      (first : Circuit (.classical operations leftService) left left false)
      (second : Circuit (.classical operations rightService) right right false) :
      Circuit (.classical operations parentService) (left.disjointUnion right separate)
        (left.disjointUnion right separate) allowAllocation
  /-- Run disjoint hybrid children with common gate grants and independent classical services. -/
  | parallelQuantum {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
      {leftService rightService parentService : ClassicalOracleModel}
      {left right : RuntimeCtx .quantum} {allowAllocation : Bool}
      (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
      (separate : RuntimeCtx.StorageDisjoint left right)
      (first : Circuit (.quantum gates oracles operations leftService) left left false)
      (second : Circuit (.quantum gates oracles operations rightService) right right false) :
      Circuit (.quantum gates oracles operations parentService) (left.disjointUnion right separate)
        (left.disjointUnion right separate) allowAllocation

namespace Circuit

/-- Complete finite histories record actual measurement outcomes and classical branch selections. -/
@[expose, implicit_reducible]
public def Path {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool} : Circuit model pre post allowAllocation → Type
  | .id _ => Unit
  | .classical (model := model) application =>
      (model.classicalOperations.outputShape application.token).Value
  | .classicalQuery (model := model) application =>
      (model.classicalOracles.outputShape application.query).Value
  | .unitary _ => Unit
  | .measureZ (ctx := ctx) wire _ => Fin (ctx.quantumLayout.wire wire).dimension
  | .retain _ _ _ _ => Unit
  | .prepareZero _ _ _ _ _ => Unit
  | .seq first second => first.Path × second.Path
  | .branch (shape := shape) _ body => (value : shape.Value) × (body value).Path
  | .iterate count body => Fin count → body.Path
  | .workspace _ _ _ _ body => body.Path
  | .embed _ body => body.Path
  | .parallelClassical _ _ first second => first.Path × second.Path
  | .parallelQuantum _ _ first second => first.Path × second.Path

/-- Mathematical execution histories are finite and allocate no physical runtime storage. -/
public noncomputable instance pathFintype {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) : Fintype code.Path := by
  induction code with
  | id | classical | classicalQuery | unitary | measureZ | retain | prepareZero =>
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
  | embed placement body bodyIH => exact bodyIH
  | parallelClassical join separate first second firstIH secondIH
  | parallelQuantum join separate first second firstIH secondIH =>
      letI := firstIH
      letI := secondIH
      exact inferInstanceAs (Fintype (first.Path × second.Path))

end Circuit

end QuantumAlg
