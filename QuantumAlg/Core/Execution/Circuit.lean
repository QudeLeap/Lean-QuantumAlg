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
    RuntimeCtx model.kind → RuntimeCtx model.kind → Type 1 where
  /-- Preserve the exact live context. -/
  | id {model : ExecutionModel} (ctx : RuntimeCtx model.kind) : Circuit model ctx ctx
  /-- Execute one granted classical native operation at its actual references. -/
  | classical {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
      (application : model.classicalOperations.Application ctx) : Circuit model ctx ctx
  /-- Query the selected classical service using its current persistent hidden state. -/
  | classicalQuery {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
      (application : model.classicalOracles.Application ctx) : Circuit model ctx ctx
  /-- Execute the selected language on exactly the complete live physical layout. -/
  | unitary {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
      {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
      (program : UnitaryCircuit gates oracles ctx.quantumLayout) :
      Circuit (.quantum gates oracles operations classicalOracles) ctx ctx
  /-- Measure one actual wire and retain its quantum system and classical outcome. -/
  | measureZ {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
      {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
      (wire : Fin ctx.systemCount)
      (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
      Circuit (.quantum gates oracles operations classicalOracles) ctx ctx
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
      (first : Circuit model pre mid) (second : Circuit model mid post) : Circuit model pre post
  /-- Read a shaped classical value before executing its selected branch. -/
  | branch {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
      (input : CInputRef pre shape) (body : shape.Value → Circuit model pre post) :
      Circuit model pre post
  /-- Execute a context-preserving body an exact finite number of times. -/
  | iterate {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
      (count : Nat) (body : Circuit model ctx ctx) : Circuit model ctx ctx
  /-- Allocate, execute with and release the same lexical classical work cell. -/
  | workspace {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
      (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
      (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh)) :
      Circuit model ctx ctx

namespace Circuit

/-- Complete finite histories record actual measurement outcomes and classical branch selections. -/
@[expose, implicit_reducible]
public def Path {model : ExecutionModel} {pre post : RuntimeCtx model.kind} :
    Circuit model pre post → Type
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

/-- Mathematical execution histories are finite and allocate no physical runtime storage. -/
public noncomputable instance pathFintype {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post) : Fintype code.Path := by
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

end Circuit

end QuantumAlg
