/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.Depth.Transform
import all QuantumAlg.Core.Base.Accounting.Event.Composition
import all QuantumAlg.Core.Base.Accounting.Event
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Execution.Preparation

/-!
# Quantum computation time of an actual execution path

The canonical duration charges native quantum gates and quantum queries only.
The dependency expression comes from the same circuit and path as semantics,
event counts, and live space. Sequential dependencies accumulate; explicit
parallel dependencies use the existing maximum interpretation.
-/

namespace QuantumAlg.Circuit

open scoped BigOperators

variable {allowAllocation : Bool} {model : ExecutionModel} {pre mid post : RuntimeCtx model.kind}

/-- Quantum computation time of the actual complete path. -/
@[expose] public def quantumTime (code : Circuit model pre post allowAllocation)
    (path : code.Path) : Nat :=
  code.depth Resource.Event.quantumDuration path

/-- Any independently dominating event durations give a conservative time bound. -/
public lemma quantumTime_le_depth (code : Circuit model pre post allowAllocation)
    (duration : Resource.Event model → Nat)
    (dominates : ∀ event, event.quantumDuration ≤ duration event) (path : code.Path) :
    code.quantumTime path ≤ code.depth duration path :=
  DepthExpr.depthEval_mono dominates (code.eventDepth path)

/-- Existing complete-path unit-event bounds remain valid quantum time bounds. -/
public lemma quantumTime_le_unitDepth (code : Circuit model pre post allowAllocation)
    (path : code.Path) :
    code.quantumTime path ≤ code.depth (fun _ => 1) path :=
  code.quantumTime_le_depth _ Resource.Event.quantumDuration_le_one path

/-- Identity performs no quantum work. -/
@[simp] public lemma quantumTime_id (ctx : RuntimeCtx model.kind)
    (path : (Circuit.id (model := model) (allowAllocation := allowAllocation) ctx).Path) :
    (Circuit.id (model := model)
      (allowAllocation := allowAllocation) ctx).quantumTime path = 0 := by
  simp [quantumTime, depth, eventDepth]

/-- Successive complete executions accumulate their actual quantum time. -/
public lemma quantumTime_seq (first : Circuit model pre mid allowAllocation)
    (second : Circuit model mid post allowAllocation)
    (left : first.Path) (right : second.Path) :
    (first.seq second).quantumTime (left, right) =
      first.quantumTime left + second.quantumTime right :=
  depth_seq first second Resource.Event.quantumDuration left right

/-- Placement interprets the same fixed child's dependency expression. -/
public lemma quantumTime_embed {localCtx caller : RuntimeCtx model.kind}
    (placement : ContextEmbedding localCtx caller)
    (body : Circuit model localCtx localCtx false) (path : body.Path) :
    (Circuit.embed (allowAllocation := allowAllocation) placement body).quantumTime path =
      body.quantumTime path := by
  simp [quantumTime, depth, eventDepth]

/-- Every complete execution in a purely classical model has zero quantum time. -/
@[simp] public lemma quantumTime_classicalModel
    {operations : ClassicalOpModel} {oracles : ClassicalOracleModel}
    {before after : RuntimeCtx .classical}
    (code : Circuit (.classical operations oracles) before after allowAllocation)
    (path : code.Path) :
    code.quantumTime path = 0 := by
  change DepthExpr.depthEval Resource.Event.quantumDuration (code.eventDepth path) = 0
  generalize code.eventDepth path = expression
  induction expression <;> simp_all [DepthExpr.depthEval]

/-- Disjoint classical children combine their actual quantum times by maximum. -/
public lemma quantumTime_parallelClassical
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).quantumTime (leftPath, rightPath) =
        max (first.quantumTime leftPath) (second.quantumTime rightPath) := by
  simp only [quantumTime_classicalModel, max_self]

/-- Disjoint quantum children combine their actual quantum times by maximum. -/
public lemma quantumTime_parallelQuantum
    {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    (leftPath : first.Path) (rightPath : second.Path) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).quantumTime (leftPath, rightPath) =
        max (first.quantumTime leftPath) (second.quantumTime rightPath) := by
  simp [quantumTime, depth, eventDepth,
    DepthExpr.depthEval_mapSchedule, Function.comp_def,
    Resource.Event.event_serviceQuantumLeft_duration,
    Resource.Event.event_serviceQuantumRight_duration]

/-- A classical branch contributes exactly its selected body's quantum time. -/
public lemma quantumTime_branch {shape : CShape} (input : CInputRef pre shape)
    (body : shape.Value → Circuit model pre post allowAllocation) (value : shape.Value)
    (path : (body value).Path) :
    (Circuit.branch input body).quantumTime ⟨value, path⟩ =
      (body value).quantumTime path := by
  simp [quantumTime, depth, eventDepth]

/-- Repetitions accumulate the quantum time of every recorded iteration. -/
public lemma quantumTime_iterate (count : Nat) (body : Circuit model pre pre allowAllocation)
    (path : (Circuit.iterate count body).Path) :
    (Circuit.iterate count body).quantumTime path =
      ∑ index : Fin count, body.quantumTime (path index) := by
  simp [quantumTime, depth, eventDepth, DepthExpr.depthEval]

/-- Repeating a body with a fixed path time adds that time once per execution. -/
public lemma quantumTime_iterate_of_constant (count : Nat)
    (body : Circuit model pre pre allowAllocation)
    (time : Nat) (constant : ∀ path, body.quantumTime path = time)
    (path : (Circuit.iterate count body).Path) :
    (Circuit.iterate count body).quantumTime path = count * time := by
  simp [quantumTime_iterate, constant]

/-- A native classical operation has zero quantum duration. -/
@[simp] public lemma quantumTime_classical
    (application : model.classicalOperations.Application pre)
    (path : (Circuit.classical (model := model)
      (allowAllocation := allowAllocation) application).Path) :
    (Circuit.classical (model := model)
      (allowAllocation := allowAllocation) application).quantumTime path = 0 := by
  simp [quantumTime, depth, eventDepth]

/-- Access to a classical service has zero quantum duration. -/
@[simp] public lemma quantumTime_classicalQuery
    (application : model.classicalOracles.Application pre)
    (path : (Circuit.classicalQuery (model := model)
      (allowAllocation := allowAllocation) application).Path) :
    (Circuit.classicalQuery (model := model)
      (allowAllocation := allowAllocation) application).quantumTime path = 0 := by
  simp [quantumTime, depth, eventDepth]

/-- Z measurement itself has zero duration; any correction gate remains charged separately. -/
@[simp] public lemma quantumTime_measureZ
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (path : (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates)
      (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) wire output).Path) :
    (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      wire output).quantumTime path = 0 := by
  simp [quantumTime, depth, eventDepth, zEvent]

/-- One actual native quantum application contributes one unit of quantum time. -/
@[simp] public lemma quantumTime_native
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (application : GateModel.Application gates ctx.quantumLayout)
    (path : (Circuit.unitary (oracles := oracles) (operations := operations)
      (classicalOracles := classicalOracles) (allowAllocation := allowAllocation)
      (UnitaryCircuit.native application)).Path) :
    (Circuit.unitary (oracles := oracles) (operations := operations)
      (classicalOracles := classicalOracles) (allowAllocation := allowAllocation)
      (UnitaryCircuit.native application)).quantumTime path = 1 := by rfl

/-- One actual quantum oracle application contributes one unit of quantum time. -/
@[simp] public lemma quantumTime_query
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (application : OracleModel.Application oracles ctx.quantumLayout)
    (path : (Circuit.unitary (gates := gates) (operations := operations)
      (classicalOracles := classicalOracles) (allowAllocation := allowAllocation)
      (UnitaryCircuit.query application)).Path) :
    (Circuit.unitary (gates := gates) (operations := operations)
      (classicalOracles := classicalOracles) (allowAllocation := allowAllocation)
      (UnitaryCircuit.query application)).quantumTime path = 1 := by rfl

/-- Fresh zero preparation contributes no quantum gate or query time. -/
@[simp] public lemma quantumTime_prepareZero
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    (ctx : RuntimeCtx .quantum) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (path : (Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      ctx key layout fresh disjoint).Path) :
    (Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      ctx key layout fresh disjoint).quantumTime path = 0 := by
  have fold (events : List (Resource.Event
      (.quantum gates oracles operations classicalOracles)))
      (zero : ∀ event ∈ events, event.quantumDuration = 0) :
      DepthExpr.depthEval Resource.Event.quantumDuration
        (events.foldr (fun event depth => .tensor (.atom event) depth) .id) = 0 := by
    induction events with
    | nil => rfl
    | cons event events ih =>
        simp only [List.foldr_cons, DepthExpr.depthEval, zero event (by simp),
          ih (fun event member => zero event (by simp [member])), max_self]
  apply fold
  intro event member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  rfl

end QuantumAlg.Circuit
