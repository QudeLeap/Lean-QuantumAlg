/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
public import QuantumAlg.Core.Execution.Context.Embedding.References

/-!
# Complete algorithms built from original fixed-context children

Each wrapper retains the child's original Circuit node. The complete caller
manifest includes every local and complement resource, while a parallel result
pairs the two actual structural observations. Classical services are combined
only by the same closed independent-service witness used by the interpreter.

Correctness and budget transfer are separate theorems about these actual runs;
none is supplied as executable data to the wrappers.
-/

namespace QuantumAlg.Algorithm

noncomputable section

/-- Call a fixed-context algorithm at its certified physical and storage placement. -/
@[expose] public def embed {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind} {shape : CShape}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (child : Algorithm model localCtx localCtx shape false) :
    Algorithm model caller caller shape allowAllocation where
  run :=
    { code := .embed placement child.run.code
      output := placement.output child.run.output }

/-- Compose disjoint classical algorithms without sharing or resetting mutable services. -/
@[expose] public def parallelClassical {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
    {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Algorithm (.classical operations leftService) left left leftShape false)
    (second : Algorithm (.classical operations rightService) right right rightShape false) :
    Algorithm (.classical operations parentService) (left.disjointUnion right separate)
      (left.disjointUnion right separate) (.product leftShape rightShape) allowAllocation where
  run :=
    { code := .parallelClassical join separate first.run.code second.run.code
      output := Output.all (left.disjointUnion right separate)
        (.product
          ((ContextEmbedding.alongUnion left right separate).outputRead first.run.output.result)
          ((ContextEmbedding.alongUnionRight left right separate).outputRead
              second.run.output.result)) }

/-- Compose disjoint hybrid algorithms with the same quantum grants and independent services. -/
@[expose] public def parallelQuantum {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {leftShape rightShape : CShape}
    {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Algorithm (.quantum gates oracles operations leftService) left left leftShape false)
    (second : Algorithm (.quantum gates oracles operations rightService) right right rightShape
        false) :
    Algorithm (.quantum gates oracles operations parentService) (left.disjointUnion right separate)
      (left.disjointUnion right separate) (.product leftShape rightShape) allowAllocation where
  run :=
    { code := .parallelQuantum join separate first.run.code second.run.code
      output := Output.all (left.disjointUnion right separate)
        (.product
          ((ContextEmbedding.alongUnion left right separate).outputRead first.run.output.result)
          ((ContextEmbedding.alongUnionRight left right separate).outputRead
              second.run.output.result)) }

end

end QuantumAlg.Algorithm
