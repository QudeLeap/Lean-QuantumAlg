/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Construction
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Semantics and accounting of physical model-relative circuits

Every observation comes from the actual construction stored by the circuit.
The type fixes the gate model, declared oracle access and full physical layout.
Native events include expanded macro bodies, while macro names support separate
statistics on that same execution. No label-to-cost interpretation is accepted.
-/

namespace QuantumAlg.UnitaryCircuit

open scoped BigOperators

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Exact, metadata-free unitary semantics of the actual construction. -/
public def matrix (circuit : UnitaryCircuit gates oracles layout)
    (environment : oracles.Interpretation) : UnitaryOperator layout.register :=
  circuit.sequence.toUnitary environment

/-- Ordered native occurrences, including every actual macro expansion. -/
public def eventTrace (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    List (Resource.Event (.quantum gates oracles operations classicalOracles)) :=
  circuit.sequence.eventTrace operations classicalOracles

/-- Literal model-relative event multiplicities from the same construction. -/
public def eventCost (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum gates oracles operations classicalOracles) :=
  circuit.sequence.eventCost operations classicalOracles

/-- Native dependency structure; macro boundaries preserve the complete depth. -/
public def eventDepth (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    DepthExpr (Resource.Event (.quantum gates oracles operations classicalOracles)) :=
  circuit.sequence.eventDepth operations classicalOracles

/-- Evaluate actual dependency depth under independently supplied event durations. -/
public def evaluatedEventDepth (duration : Resource.Event (.quantum gates oracles) → Nat)
    (circuit : UnitaryCircuit gates oracles layout) : Nat :=
  DepthExpr.depthEval duration circuit.eventDepth

/-- Count the deepest sequential chain of occurrences of one literal event coordinate. -/
public def eventQueryDepth (focus : Resource.Event (.quantum gates oracles))
    (circuit : UnitaryCircuit gates oracles layout) : Nat :=
  DepthExpr.queryDepthEval focus circuit.eventDepth

/-- Count descriptive macro occurrences without replacing their native expansions. -/
public def macroCount (name : String) (circuit : UnitaryCircuit gates oracles layout) : Nat :=
  circuit.sequence.macroTrace.count name

/-- Linearize the dependency expression with literal native-event multiplicities. -/
public def resourcesFromEventDepth (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum gates oracles operations classicalOracles) :=
  DepthExpr.costEval (fun event => ResourcePool.singleton event)
    (circuit.eventDepth operations classicalOracles)

/-- Native multiplicity and dependency accounting observe the same construction. -/
@[simp] public lemma resourcesFromEventDepth_eq_eventCost
    (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    circuit.resourcesFromEventDepth operations classicalOracles =
      circuit.eventCost operations classicalOracles :=
  UnitarySequence.resourcesFromEventDepth_eq_eventCost circuit.sequence operations classicalOracles

/-- Forgetting order in the actual native trace yields exactly the circuit's event ledger. -/
@[simp] public lemma ofList_eventTrace_eq_eventCost
    (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool.ofList (circuit.eventTrace operations classicalOracles) =
      circuit.eventCost operations classicalOracles :=
  UnitarySequence.ofList_eventTrace_eq_eventCost circuit.sequence operations classicalOracles

/-- The action on a mathematical vector carries no model selection in the state type. -/
public def applyVec (circuit : UnitaryCircuit gates oracles layout)
    (environment : oracles.Interpretation)
    (state : HilbertVector layout.register) : HilbertVector layout.register :=
  (circuit.matrix environment).applyVec state

/-- Apply the actual operator while preserving mathematical normalization. -/
public def applyNormalized (circuit : UnitaryCircuit gates oracles layout)
    (environment : oracles.Interpretation)
    (state : NormalizedVector layout.register) : NormalizedVector layout.register :=
  (circuit.matrix environment).apply state

variable (environment : oracles.Interpretation)

@[simp] lemma identity_matrix : ((identity gates oracles layout).matrix environment) = 1 := by rfl

@[simp] lemma identity_eventCost : (identity gates oracles layout).eventCost = 0 := by rfl

@[simp] lemma identity_eventTrace : (identity gates oracles layout).eventTrace = [] := by rfl

@[simp] lemma identity_eventDepth : (identity gates oracles layout).eventDepth = .id := by rfl

@[simp] lemma evaluatedEventDepth_identity
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (identity gates oracles layout).evaluatedEventDepth duration = 0 := by
  rfl

@[simp] lemma leaf_matrix (leaf : UnitaryLeaf gates oracles layout) :
    ((ofLeaf leaf).matrix environment) = leaf.operator environment := by rfl

@[simp] lemma leaf_eventCost (leaf : UnitaryLeaf gates oracles layout) :
    (ofLeaf leaf).eventCost = ResourcePool.singleton leaf.event := by rfl

@[simp] public lemma native_matrix (application : GateModel.Application gates layout) :
    ((native (oracles := oracles) application).matrix environment) = application.operator := by rfl

@[simp] public lemma native_eventCost (application : GateModel.Application gates layout) :
    (native (oracles := oracles) application).eventCost =
      ResourcePool.singleton (model := .quantum gates oracles) (.gate application.coordinate) := by
  rfl

/-- A native instruction records exactly the coordinate of its actual model token. -/
@[simp] public lemma native_eventTrace (application : GateModel.Application gates layout) :
    (native (oracles := oracles) application).eventTrace =
      [.gate application.coordinate] := by rfl

@[simp] lemma evaluatedEventDepth_native
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (application : GateModel.Application gates layout) :
    (native (oracles := oracles) application).evaluatedEventDepth duration =
      duration (.gate application.coordinate) := by
  rfl

@[simp] lemma query_matrix (application : OracleModel.Application oracles layout) :
    (query (gates := gates) application).matrix environment =
      application.operator environment := by rfl

@[simp] lemma query_eventCost (application : OracleModel.Application oracles layout) :
    (query (gates := gates) application).eventCost =
      ResourcePool.singleton (model := .quantum gates oracles)
        (.oracle application.coordinate) := by
  rfl

@[simp] lemma evaluatedEventDepth_query
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (application : OracleModel.Application oracles layout) :
    (query (gates := gates) application).evaluatedEventDepth duration =
      duration (.oracle application.coordinate) := by
  rfl

@[simp] lemma seq_matrix (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).matrix environment =
      right.matrix environment * left.matrix environment := by rfl

/-- Parallel syntax denotes the product of the two actual lifted operators. -/
@[simp] public lemma parallel_matrix_raw {leftCount rightCount count : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {layout : QuantumLayout count} (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    ((parallel left right leftPlacement rightPlacement disjoint).matrix environment) =
      rightPlacement.liftOperator (right.matrix environment) *
        leftPlacement.liftOperator (left.matrix environment) := by
  rfl

/-- Sequential execution applies the first actual operator before the second. -/
@[simp] public lemma applyNormalized_seq (left right : UnitaryCircuit gates oracles layout)
    (state : NormalizedVector layout.register) :
    (seq left right).applyNormalized environment state =
      right.applyNormalized environment (left.applyNormalized environment state) := by
  apply NormalizedVector.ext
  intro index
  change ((right.matrix environment) * (left.matrix environment)).applyVec state index =
    (right.matrix environment).applyVec ((left.matrix environment).applyVec state) index
  rw [UnitaryOperator.mul_applyVec]

@[simp] lemma seq_eventCost (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).eventCost = left.eventCost + right.eventCost := by rfl

@[simp] lemma seq_eventTrace (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).eventTrace = left.eventTrace ++ right.eventTrace := by rfl

@[simp] lemma seq_eventDepth (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).eventDepth = .seq left.eventDepth right.eventDepth := by rfl

@[simp] lemma evaluatedEventDepth_seq
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).evaluatedEventDepth duration =
      left.evaluatedEventDepth duration + right.evaluatedEventDepth duration := by rfl

@[simp] lemma parallel_eventCost {leftCount rightCount totalCount : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {totalLayout : QuantumLayout totalCount}
    (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout totalLayout)
    (rightPlacement : QuantumLayout.Embedding rightLayout totalLayout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    (parallel left right leftPlacement rightPlacement disjoint).eventCost =
      left.eventCost + right.eventCost := by
  rfl

@[simp] lemma evaluatedEventDepth_parallel {leftCount rightCount totalCount : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {totalLayout : QuantumLayout totalCount}
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout totalLayout)
    (rightPlacement : QuantumLayout.Embedding rightLayout totalLayout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    (parallel left right leftPlacement rightPlacement disjoint).evaluatedEventDepth duration =
      max (left.evaluatedEventDepth duration) (right.evaluatedEventDepth duration) := by
  rfl

@[simp] lemma iterate_matrix (repetitions : Nat)
    (body : UnitaryCircuit gates oracles layout) :
    (iterate repetitions body).matrix environment =
      body.matrix environment ^ repetitions := by rfl

@[simp] lemma iterate_eventCost (repetitions : Nat)
    (body : UnitaryCircuit gates oracles layout) :
    (iterate repetitions body).eventCost = repetitions • body.eventCost := by rfl

@[simp] lemma iterate_eventTrace (repetitions : Nat)
    (body : UnitaryCircuit gates oracles layout) :
    (iterate repetitions body).eventTrace =
      (List.replicate repetitions body.eventTrace).flatten := by
  rfl

@[simp] lemma iterate_eventDepth (repetitions : Nat)
    (body : UnitaryCircuit gates oracles layout) :
    (iterate repetitions body).eventDepth = .iterate repetitions body.eventDepth := by rfl

@[simp] lemma macroCall_matrix (name : String) (body : UnitaryCircuit gates oracles layout) :
    ((macroCall name body).matrix environment) = (body.matrix environment) := by rfl

@[simp] lemma macroCall_eventCost (name : String) (body : UnitaryCircuit gates oracles layout) :
    (macroCall name body).eventCost = body.eventCost := by rfl

@[simp] lemma macroCall_eventTrace (name : String) (body : UnitaryCircuit gates oracles layout) :
    (macroCall name body).eventTrace = body.eventTrace := by rfl

@[simp] lemma macroCall_eventDepth (name : String) (body : UnitaryCircuit gates oracles layout) :
    (macroCall name body).eventDepth = body.eventDepth := by rfl

/-- Descriptive macro boundaries add no dependency beyond their retained native body. -/
@[simp] public lemma evaluatedEventDepth_macroCall
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (name : String) (body : UnitaryCircuit gates oracles layout) :
    (macroCall name body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rfl

/-- The macro name adds one observation while every nested occurrence remains visible. -/
public lemma macroCount_macroCall (focus name : String)
    (body : UnitaryCircuit gates oracles layout) :
    (macroCall name body).macroCount focus =
      (if name = focus then 1 else 0) + body.macroCount focus := by
  by_cases same : name = focus
  · subst name
    simp [macroCount, macroCall, UnitarySequence.macroTrace, Nat.add_comm]
  · simp [macroCount, macroCall, UnitarySequence.macroTrace, same]

@[simp] lemma indexedProduct_matrix (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles layout)
    (step : Fin steps → UnitaryCircuit gates oracles layout) :
    ((indexedProduct label steps start step).matrix environment) =
      (List.ofFn (fun index => ((step index).matrix environment))).foldl
        (fun accumulated next => next * accumulated) (start.matrix environment) := by rfl

@[simp] lemma indexedProduct_eventCost (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles layout)
    (step : Fin steps → UnitaryCircuit gates oracles layout) :
    (indexedProduct label steps start step).eventCost =
      start.eventCost + ∑ index, (step index).eventCost := by rfl

@[simp] lemma indexedProduct_eventDepth (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles layout)
    (step : Fin steps → UnitaryCircuit gates oracles layout) :
    (indexedProduct label steps start step).eventDepth =
      .indexedProduct label steps start.eventDepth
        (fun index => (step index).eventDepth) := by rfl

@[simp] lemma evaluatedEventDepth_indexedProduct
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (label : String) (steps : Nat) (start : UnitaryCircuit gates oracles layout)
    (step : Fin steps → UnitaryCircuit gates oracles layout) :
    (indexedProduct label steps start step).evaluatedEventDepth duration =
      start.evaluatedEventDepth duration +
        ∑ index, (step index).evaluatedEventDepth duration := by
  rfl

end

end QuantumAlg.UnitaryCircuit
