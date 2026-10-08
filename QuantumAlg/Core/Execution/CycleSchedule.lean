/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Output
public import QuantumAlg.Core.Execution.Borrowed.State
public import QuantumAlg.Core.Execution.Borrowed
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Observe
public import QuantumAlg.Core.Execution.State.Promise
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Algorithm.CyclePlan
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.CyclePlan
import all QuantumAlg.Core.Execution.Circuit.Reassociation

/-!
# Certified complete-cycle schedules of actual executions

A schedule implements the caller's fixed independent cycle plan on the
existing typed circuit. A coherent final cycle can end with live output.
Starting another quantum cycle additionally requires actual measurement and
reinitialization of every owned system. Cleanup alone cannot change the
caller's cycle plan. Actual prefix outputs supply the continuation's input,
including its persistent service state. The original circuit still supplies
chronological depth, events, paths, and live-space accounting.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- One whole executed section solves the caller's fixed protocol, including
its state promises, borrowed restoration and independent resource bounds. -/
public structure CompleteCycle {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (code : Circuit model pre post) (protocol : Problem model pre post shape) where
  /-- Every live entry and the observed result at the completed boundary. -/
  output : Output post shape
  /-- The same exact executed code establishes the independently chosen protocol. -/
  certified : Algorithm.Solves
    (⟨{ code := code, output := output }⟩ : Algorithm model pre post shape) protocol

/-- A standalone classical section has no hidden quantum operation, query,
preparation, or measurement on any interpreter path. -/
public def IsClassical {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) : Prop :=
  ∀ (path : code.Path) (event : Resource.Event model),
    event ∈ code.eventTrace path →
      (∃ coordinate, event = .classicalOperation coordinate) ∨
      (∃ coordinate, event = .classicalQuery coordinate)

/-- A caller-selected physical basis label for the owned output is prepared
in every complete record, including zero-mass records and arbitrary reference. -/
public def ReinitializedAt {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ) : Prop :=
  ∀ (Reference : Register) {H : Type} [Fintype H]
    (state : Execution.State pre Reference (model.HiddenState × H))
    (label : Execution.Store post × (model.HiddenState × (H × code.Path))),
  (StatePromise.pure (NormalizedVector.ket seed)).Holds
    (DensityOperator.observeSelection post.quantumLayout
      post.borrowedSelectionᶜ Reference ((code.execute Reference state).block label))

/-- Physical cleanup leaves every owned system in one fixed, predetermined basis state,
even after conditioning on the complete store, hidden service state and path.
The seed is chosen before every input, reference, history and execution label;
it may describe zero reset or a fixed re-preparation, but cannot depend on an outcome.
This certificate proves no caller protocol and grants no cycle boundary by
itself. Only the caller's independently fixed sequential plan authorizes a cut. -/
public structure RestartCleanup {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post) where
  /-- Every actual path includes a quantum measurement. -/
  measured : ∀ path : code.Path, ∃ measuredDimension : model.SystemDimension,
    Resource.Event.measurement measuredDimension ∈ code.eventTrace path
  /-- The actual borrowed interface is restored for every input and external
  reference, independently of the protocol's input predicate. -/
  restores : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : Execution.State pre Reference (model.HiddenState × H)),
    code.BorrowedRestored Reference state (code.execute Reference state)
  /-- One fixed seed reinitializes every owned output wire on every actual record,
  with arbitrary borrowed and external-reference correlations retained in the final state. -/
  reinitialized : ∃ seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ,
    ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : Execution.State pre Reference (model.HiddenState × H))
      (label : Execution.Store post × (model.HiddenState × (H × code.Path))),
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection post.quantumLayout
        post.borrowedSelectionᶜ Reference
        ((code.execute Reference state).block label))

/-- The actual normalized prefix output, retaining its live store, persistent
service state and quantum/reference correlations. Only mathematical histories
are summed away; no service initialization or physical reset is performed. -/
public def nextInput {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) :
    Execution.OracleInput model.classicalOracles post Reference where
  state := (code.execute Reference
    (input.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
      (fun record => (record.1, record.2.1))
  normalized := (ExecutionState.mapClassical_mass _ _).trans
    ((code.execute_mass Reference _).trans
      ((input.state.mapClassical_mass _).trans input.normalized))

/-- Every admitted actual prefix output satisfies the next protocol's caller
and joint service domains. An empty local predicate cannot exclude a real
caller execution that the enclosing specification admits. -/
public def EntryCompatible {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind} {leftShape shape : CShape}
    (left : CyclePlan model pre mid leftShape)
    (right : CyclePlan model mid post shape) (first : Circuit model pre mid) : Prop :=
  ∀ (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    left.Admits input → right.Admits (first.nextInput input)

/-- An actual measurement cannot be hidden in a standalone classical section.
Its recorded outcome path always carries a quantum measurement event. -/
public theorem measureZ_notClassical {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    ¬ IsClassical (Circuit.measureZ (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) wire output) := by
  intro classical
  let dimension := (ctx.quantumLayout.wire wire).dimension
  let path : (Circuit.measureZ (gates := gates) (oracles := oracles)
    (operations := operations) (classicalOracles := classicalOracles) wire output).Path :=
      ⟨0, dimension.pos⟩
  have present : (Resource.Event.measurement dimension :
      Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
      (Circuit.measureZ (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) wire output).eventTrace
          path := by
    simp [Circuit.eventTrace, Circuit.zEvent, dimension]
  rcases classical path (.measurement dimension) present with
    ⟨_, impossible⟩ | ⟨_, impossible⟩
  · cases impossible
  · cases impossible

/-- Certified execution of the caller's independent plan on the same code.
The two indices prevent changing either the circuit or the intended cycles. -/
public inductive CycleSchedule {model : ExecutionModel} :
    {pre post : RuntimeCtx model.kind} → {shape : CShape} →
      CyclePlan model pre post shape → Circuit model pre post → Type 1 where
  | complete {pre post : RuntimeCtx model.kind} {shape : CShape}
      {protocol : Problem model pre post shape}
      (code : Circuit model pre post) (contract : CompleteCycle code protocol) :
      CycleSchedule (.cycle protocol) code
  | classical {pre post : RuntimeCtx model.kind} {shape : CShape}
      {protocol : Problem model pre post shape}
      (code : Circuit model pre post) (contract : CompleteCycle code protocol)
      (onlyClassical : IsClassical code) : CycleSchedule (.classical protocol) code
  | seq {pre mid post : RuntimeCtx model.kind} {leftShape shape : CShape}
      {leftPlan : CyclePlan model pre mid leftShape}
      {rightPlan : CyclePlan model mid post shape}
      (first : Circuit model pre mid) (second : Circuit model mid post)
      (left : CycleSchedule leftPlan first) (right : CycleSchedule rightPlan second)
      (entry : EntryCompatible leftPlan rightPlan first)
      (boundary : IsClassical second ∨ Nonempty (RestartCleanup first)) :
      CycleSchedule (.seq leftPlan rightPlan) (.seq first second)
  | reassociate {pre post : RuntimeCtx model.kind} {shape : CShape}
      {plan : CyclePlan model pre post shape} {source target : Circuit model pre post}
      (association : Reassociation source target) (schedule : CycleSchedule plan target) :
      CycleSchedule plan source

namespace CycleSchedule

/-- The maximum depth of a declared complete quantum cycle on the actual path.
Standalone classical work is retained in `code.depth`, not charged here. -/
@[expose] public def maximumCycleDepth {model : ExecutionModel} :
    {pre post : RuntimeCtx model.kind} → {shape : CShape} →
    {plan : CyclePlan model pre post shape} → {code : Circuit model pre post} →
    (schedule : CycleSchedule plan code) → (duration : Resource.Event model → Nat) →
      code.Path → Nat
  | _, _, _, _, _, .complete actual _, duration, path => actual.depth duration path
  | _, _, _, _, _, .classical _ _ _, _, _ => 0
  | _, _, _, _, _, .seq _ _ left right _ _, duration, path =>
      max (left.maximumCycleDepth duration path.1)
        (right.maximumCycleDepth duration path.2)
  | _, _, _, _, _, .reassociate association schedule, duration, path =>
      schedule.maximumCycleDepth duration (association.path path)

/-- A certified complete cycle retains all of its actual internal depth. -/
@[simp] public theorem maximumCycleDepth_complete {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {protocol : Problem model pre post shape} (code : Circuit model pre post)
    (contract : CompleteCycle code protocol) (duration : Resource.Event model → Nat)
    (path : code.Path) :
    (CycleSchedule.complete code contract).maximumCycleDepth duration path =
      code.depth duration path := rfl

private theorem maximumCycleDepth_of_singlePlan {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {plan : CyclePlan model pre post shape} {code : Circuit model pre post}
    (schedule : CycleSchedule plan code) (duration : Resource.Event model → Nat) :
    ∀ (protocol : Problem model pre post shape), plan = .cycle protocol →
      ∀ path : code.Path,
        schedule.maximumCycleDepth duration path = code.depth duration path := by
  induction schedule with
  | complete actual contract => intro protocol same path; rfl
  | classical actual contract onlyClassical => intro protocol same; cases same
  | seq first second left right entry boundary leftIH rightIH =>
      intro protocol same
      cases same
  | reassociate association schedule ih =>
      intro protocol same path
      exact (ih protocol same (association.path path)).trans
        (association.reassociation_depth_eq duration path).symm

/-- A caller that specifies one cycle retains the whole executed dependency
depth, including any internal measurement, feedback or reset sequence. -/
public theorem maximumCycleDepth_cycle {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {protocol : Problem model pre post shape} {code : Circuit model pre post}
    (schedule : CycleSchedule (.cycle protocol) code)
    (duration : Resource.Event model → Nat) (path : code.Path) :
    schedule.maximumCycleDepth duration path = code.depth duration path :=
  maximumCycleDepth_of_singlePlan schedule duration protocol rfl path

/-- Standalone classical processing contributes no quantum-cycle depth. -/
@[simp] public theorem maximumCycleDepth_classical {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {protocol : Problem model pre post shape} (code : Circuit model pre post)
    (contract : CompleteCycle code protocol)
    (onlyClassical : IsClassical code) (duration : Resource.Event model → Nat)
    (path : code.Path) :
    (CycleSchedule.classical code contract onlyClassical).maximumCycleDepth duration path = 0 := rfl

/-- Consecutive complete-cycle sections combine by maximum, with their
original sequential dependency retained by `Circuit.depth`. -/
@[simp] public theorem maximumCycleDepth_seq {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind} {leftShape shape : CShape}
    {leftPlan : CyclePlan model pre mid leftShape}
    {rightPlan : CyclePlan model mid post shape}
    (first : Circuit model pre mid) (second : Circuit model mid post)
    (left : CycleSchedule leftPlan first) (right : CycleSchedule rightPlan second)
    (entry : EntryCompatible leftPlan rightPlan first)
    (boundary : IsClassical second ∨ Nonempty (RestartCleanup first))
    (duration : Resource.Event model → Nat) (path : (Circuit.seq first second).Path) :
    (CycleSchedule.seq first second left right entry boundary).maximumCycleDepth duration path =
      max (left.maximumCycleDepth duration path.1)
        (right.maximumCycleDepth duration path.2) := rfl

/-- Regrouping the same instructions retains the fixed independent plan and
every certified intermediate boundary on the corresponding actual path. -/
@[simp] public theorem maximumCycleDepth_reassociate {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {plan : CyclePlan model pre post shape} {source target : Circuit model pre post}
    (association : Reassociation source target) (schedule : CycleSchedule plan target)
    (duration : Resource.Event model → Nat) (path : source.Path) :
    (CycleSchedule.reassociate association schedule).maximumCycleDepth duration path =
      schedule.maximumCycleDepth duration (association.path path) := rfl

/-- Every declared cycle lies within the unchanged whole-run dependency depth. -/
public theorem maximumCycleDepth_le_depth {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {plan : CyclePlan model pre post shape} {code : Circuit model pre post}
    (schedule : CycleSchedule plan code)
    (duration : Resource.Event model → Nat) (path : code.Path) :
    schedule.maximumCycleDepth duration path ≤ code.depth duration path := by
  induction schedule with
  | complete actual contract => exact le_refl _
  | classical actual contract onlyClassical => exact Nat.zero_le _
  | seq first second left right entry boundary leftIH rightIH =>
      change max (left.maximumCycleDepth duration path.1)
          (right.maximumCycleDepth duration path.2) ≤
        first.depth duration path.1 + second.depth duration path.2
      have leftBound := leftIH path.1
      have rightBound := rightIH path.2
      omega
  | reassociate association schedule ih =>
      exact (ih (association.path path)).trans
        (le_of_eq (association.reassociation_depth_eq duration path).symm)

end CycleSchedule

end

end QuantumAlg.Circuit

namespace QuantumAlg.Algorithm

noncomputable section

/-- Correctness and an admissible cycle schedule for one fixed caller specification.
The entry proof connects every actual admitted caller input to the first leaf;
each sequential constructor then establishes the next actual entry condition. -/
public structure CycleSolves {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (algorithm : Algorithm model pre post shape)
    (specification : CycleProblem model pre post shape) : Type 1 where
  /-- Ordinary correctness, state, restoration and whole-run resource guarantees. -/
  correctness : Solves algorithm specification.outcome
  /-- The actual code implements exactly the caller's independently selected plan. -/
  schedule : Circuit.CycleSchedule specification.plan algorithm.run.code
  /-- Every admitted caller input is admitted by the first cycle protocol. -/
  entry : ∀ (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    specification.outcome.Admits input → specification.plan.Admits input

namespace CycleSolves

/-- Maximum complete-cycle depth under the fixed, actually admissible caller plan. -/
public def maximumCycleDepth {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {algorithm : Algorithm model pre post shape}
    {specification : CycleProblem model pre post shape}
    (certificate : CycleSolves algorithm specification)
    (duration : Resource.Event model → Nat) (path : algorithm.run.code.Path) : Nat :=
  certificate.schedule.maximumCycleDepth duration path

/-- The certified cycle coordinate is bounded by unchanged chronological depth. -/
public theorem maximumCycleDepth_le_wholeRunDepth {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {algorithm : Algorithm model pre post shape}
    {specification : CycleProblem model pre post shape}
    (certificate : CycleSolves algorithm specification)
    (duration : Resource.Event model → Nat) (path : algorithm.run.code.Path) :
    certificate.maximumCycleDepth duration path ≤ algorithm.run.code.depth duration path :=
  certificate.schedule.maximumCycleDepth_le_depth duration path

end CycleSolves

end

end QuantumAlg.Algorithm
