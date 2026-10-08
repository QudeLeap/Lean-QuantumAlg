/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# Rejected quantum-cycle cuts

Two consecutive native gates cannot pass the physical restart obligation.
More generally, the caller's one-cycle protocol cannot be replaced by a
sequential plan, even when an internal measurement and reset really occurred.
Entry-domain checks prevent excluding actual admitted caller inputs.
-/

namespace QuantumAlg.Circuit

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- A single native gate has no measured result for a quantum restart. -/
theorem singleGate_noRestart
    (body : UnitaryCircuit gates oracles ctx.quantumLayout)
    (coordinate : gates.Coordinate)
    (trace : body.eventTrace operations classicalOracles = [.gate coordinate]) :
    ¬ Nonempty (RestartCleanup
      (Circuit.unitary (operations := operations)
        (classicalOracles := classicalOracles) body)) := by
  intro ⟨boundary⟩
  obtain ⟨dimension, present⟩ := boundary.measured ()
  change (Resource.Event.measurement dimension :
    Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
      body.eventTrace operations classicalOracles at present
  rw [trace] at present
  simp at present

/-- The second native gate cannot be hidden in a classical tail. -/
theorem singleGate_notClassical
    (body : UnitaryCircuit gates oracles ctx.quantumLayout)
    (coordinate : gates.Coordinate)
    (trace : body.eventTrace operations classicalOracles = [.gate coordinate]) :
    ¬ IsClassical (Circuit.unitary (operations := operations)
      (classicalOracles := classicalOracles) body) := by
  intro classical
  have present : (Resource.Event.gate coordinate :
      Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
        (Circuit.unitary (operations := operations)
          (classicalOracles := classicalOracles) body).eventTrace () := by
    change (Resource.Event.gate coordinate :
      Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
        body.eventTrace operations classicalOracles
    rw [trace]
    simp
  rcases classical () (.gate coordinate) present with
    ⟨_, impossible⟩ | ⟨_, impossible⟩
  · cases impossible
  · cases impossible

/-- The exact `CycleSchedule.seq` boundary obligation rejects a split between
two single-gate quantum executions, including the two-H counterexample. -/
theorem twoSingleGates_noSplit
    (body : UnitaryCircuit gates oracles ctx.quantumLayout)
    (coordinate : gates.Coordinate)
    (trace : body.eventTrace operations classicalOracles = [.gate coordinate]) :
    ¬ (IsClassical (Circuit.unitary (operations := operations)
          (classicalOracles := classicalOracles) body) ∨
        Nonempty (RestartCleanup (Circuit.unitary (operations := operations)
          (classicalOracles := classicalOracles) body))) := by
  intro proposed
  rcases proposed with classical | restart
  · exact singleGate_notClassical body coordinate trace classical
  · exact singleGate_noRestart body coordinate trace restart

end QuantumAlg.Circuit

namespace QuantumAlg.Circuit.CycleSchedule

variable {model : ExecutionModel} {pre mid post : RuntimeCtx model.kind}
  {leftShape shape : CShape}

/-- A physical cleanup witness cannot turn a caller's single computation into
two independently completed protocols. -/
theorem fixedCycle_noSequentialPlan (protocol : Problem model pre post shape)
    (left : CyclePlan model pre mid leftShape) (right : CyclePlan model mid post shape) :
    (CyclePlan.cycle protocol : CyclePlan model pre post shape) ≠ .seq left right := by
  intro same
  cases same

/-- A reset followed by feedback inside one caller cycle retains their sum.
The statement covers actual measured reset code and classically selected gates;
no special instruction or macro can evade the fixed cycle specification. -/
theorem intermediateFeedback_keepsWholeDepth
    (first : Circuit model pre mid) (second : Circuit model mid post)
    (protocol : Problem model pre post shape)
    (schedule : CycleSchedule (.cycle protocol) (.seq first second))
    (duration : Resource.Event model → Nat) (path : (Circuit.seq first second).Path) :
    schedule.maximumCycleDepth duration path =
      first.depth duration path.1 + second.depth duration path.2 := by
  rw [maximumCycleDepth_cycle]
  rfl

/-- Replacing positive success by zero changes the fixed independent protocol;
its schedule cannot be transported to the original caller plan. -/
theorem zeroSuccess_notFixedPlan
    (fixed substitute : Problem model pre post shape)
    (positive : 0 < fixed.successLB.value) (zero : substitute.successLB.value = 0) :
    (CyclePlan.cycle fixed : CyclePlan model pre post shape) ≠ .cycle substitute := by
  intro same
  have protocols : fixed = substitute := CyclePlan.cycle.inj same
  have impossible : fixed.successLB.value = 0 :=
    (congrArg (fun protocol : Problem model pre post shape => protocol.successLB.value)
      protocols).trans zero
  exact (ne_of_gt positive) impossible

end QuantumAlg.Circuit.CycleSchedule

namespace QuantumAlg.Algorithm.CycleSolves

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}

/-- A false validity predicate cannot certify a caller input that the actual
outer problem admits. Empty scientific domains remain legal when no such input exists. -/
theorem falseValidity_rejectsAdmittedCaller
    (algorithm : Algorithm model pre post shape)
    (outcome protocol : Problem model pre post shape)
    (empty : ∀ state, ¬ protocol.valid state) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (admitted : outcome.Admits input) :
    ¬ Nonempty (CycleSolves algorithm
      { outcome := outcome, plan := .cycle protocol }) := by
  intro ⟨certificate⟩
  exact empty _ (certificate.entry Reference input admitted).1

/-- An impossible joint service initialization cannot hide an actual admitted
caller input either; no fresh or independent service state is substituted. -/
theorem falseInitialization_rejectsAdmittedCaller
    (algorithm : Algorithm model pre post shape)
    (outcome protocol : Problem model pre post shape)
    (empty : ∀ state, ¬ protocol.initialization state) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (admitted : outcome.Admits input) :
    ¬ Nonempty (CycleSolves algorithm
      { outcome := outcome, plan := .cycle protocol }) := by
  intro ⟨certificate⟩
  exact empty _ (certificate.entry Reference input admitted).2

end QuantumAlg.Algorithm.CycleSolves
