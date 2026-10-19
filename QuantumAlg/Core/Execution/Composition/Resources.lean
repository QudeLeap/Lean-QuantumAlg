/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Context.Embedding

/-!
# Exact path resources of original child composition

Embedding retains the child's actual event coordinates and charges the entire
caller context. Parallel composition routes independent service coordinates,
adds occurrences of shared native coordinates, and charges the complete union.
The canonical maximum time equations are supplied by the time interface.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

/-- Placement retains every actual child event and its multiplicity. -/
private lemma resourcePool_embed_proof {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false) (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).resourcePool path =
      body.resourcePool path := rfl

/-- Exact event accounting of the same original child paths. -/
public lemma resourcePool_embed {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false) (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).resourcePool path =
      body.resourcePool path :=
  resourcePool_embed_proof placement body path

/-- A placed child keeps the entire caller context resident throughout its execution. -/
public lemma peakResidentSpace_embed {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false) (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).peakResidentSpace path =
      caller.residentSpace :=
  SpacePool.max_zero _

/-- A placed child retains every caller auxiliary role, including complement storage. -/
public lemma peakAuxiliarySpace_embed {model : ExecutionModel}
    {localCtx caller : RuntimeCtx model.kind}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false) (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).peakAuxiliarySpace path =
      caller.auxiliarySpace :=
  SpacePool.max_zero _

/-- Both independent event ledgers are routed into their actual parent coordinates. -/
private lemma resourcePool_parallelClassical_proof
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).resourcePool (leftPath, rightPath) =
        (first.resourcePool leftPath).map (Resource.Event.serviceClassicalLeft join operations) +
          (second.resourcePool rightPath).map
            (Resource.Event.serviceClassicalRight join operations) := rfl

/-- Exact event accounting of the same original child paths. -/
public lemma resourcePool_parallelClassical
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).resourcePool (leftPath, rightPath) =
        (first.resourcePool leftPath).map (Resource.Event.serviceClassicalLeft join operations) +
          (second.resourcePool rightPath).map
            (Resource.Event.serviceClassicalRight join operations) :=
  resourcePool_parallelClassical_proof join separate first second leftPath rightPath

/-- Both live contexts contribute their actual resident storage simultaneously. -/
public lemma peakResidentSpace_parallelClassical
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).peakResidentSpace (leftPath, rightPath) =
        left.residentSpace + right.residentSpace :=
  (SpacePool.max_zero _).trans (RuntimeCtx.residentSpace_disjointUnion left right separate)

/-- Both live contexts contribute their actual auxiliary storage simultaneously. -/
public lemma peakAuxiliarySpace_parallelClassical
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).peakAuxiliarySpace (leftPath, rightPath) =
        left.auxiliarySpace + right.auxiliarySpace :=
  (SpacePool.max_zero _).trans (RuntimeCtx.auxiliarySpace_disjointUnion left right separate)

/-- Both independent event ledgers are routed into their actual parent coordinates. -/
private lemma resourcePool_parallelQuantum_proof
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).resourcePool (leftPath, rightPath) =
        (first.resourcePool leftPath).map
          (Resource.Event.serviceQuantumLeft join gates oracles operations) +
          (second.resourcePool rightPath).map
            (Resource.Event.serviceQuantumRight join gates oracles operations) := rfl

/-- Exact event accounting of the same original child paths. -/
public lemma resourcePool_parallelQuantum
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).resourcePool (leftPath, rightPath) =
        (first.resourcePool leftPath).map
          (Resource.Event.serviceQuantumLeft join gates oracles operations) +
          (second.resourcePool rightPath).map
            (Resource.Event.serviceQuantumRight join gates oracles operations) :=
  resourcePool_parallelQuantum_proof join separate first second leftPath rightPath

/-- Both live contexts contribute their actual resident storage simultaneously. -/
public lemma peakResidentSpace_parallelQuantum
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).peakResidentSpace (leftPath, rightPath) =
        left.residentSpace + right.residentSpace :=
  (SpacePool.max_zero _).trans (RuntimeCtx.residentSpace_disjointUnion left right separate)

/-- Both live contexts contribute their actual auxiliary storage simultaneously. -/
public lemma peakAuxiliarySpace_parallelQuantum
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).peakAuxiliarySpace (leftPath, rightPath) =
        left.auxiliarySpace + right.auxiliarySpace :=
  (SpacePool.max_zero _).trans (RuntimeCtx.auxiliarySpace_disjointUnion left right separate)

end QuantumAlg.Circuit
