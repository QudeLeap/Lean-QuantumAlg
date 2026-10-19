/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Trace.Boundary
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Actual resources of Simon's two reusable reset batches

Both batches retain every real measurement and selected X event. Their
corrections occupy at most two quantum layers in total, and an empty bank
has no quantum duration. Every visited context is the original context:
the old additional one-bit reset workspace is absent.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

variable {allowAllocation : Bool} {oracles : OracleModel}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

private lemma correction_eventCost (half : Fin 2)
    (value : CShape.Value (.fixedVector n (.finite 2))) :
    (correction (oracles := oracles) base noQuantum n count half value).eventCost =
      ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask value) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
          (.gate .singleQubit) := by
  rw [correction, UnitaryCircuit.placeAt_eventCost,
    ZReset.BankParallel.Correction.layer_eventCost]

private lemma correction_eventCost_context (half : Fin 2)
    (value : CShape.Value (.fixedVector n (.finite 2))) :
    (correction (oracles := oracles) base noQuantum n count half value).eventCost
      BitWord.model .empty =
        ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask value) •
          ResourcePool.singleton (model := nativeModel oracles) (.gate .singleQubit) := by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((correction (oracles := oracles) base noQuantum n count half value).eventCost
      BitWord.model .empty) =
      ResourcePool.count event
        (ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask value) •
          ResourcePool.singleton (model := nativeModel oracles) (.gate .singleQubit))
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate => cases coordinate <;> simp [correction_eventCost]
  | oracle _ => simp [correction_eventCost]
  | classicalOperation _ => simp
  | classicalQuery _ => simp
  | preparation _ => simp
  | measurement _ => simp

/-- One actual batch retains all n measurements and exactly its stored one outcomes. -/
lemma batch_resourcePool (half : Fin 2)
    (path : (batch (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).Path) :
    (batch (allowAllocation := allowAllocation) base noQuantum n count half).resourcePool path =
      n • ResourcePool.singleton (model := nativeModel oracles) (.measurement (2 : ℕ+)) +
        ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.2.1) •
          ResourcePool.singleton (model := nativeModel oracles) (.gate .singleQubit) := by
  change (measure (allowAllocation := allowAllocation) base noQuantum n count half).resourcePool
    path.1 +
      (Circuit.unitary (allowAllocation := allowAllocation) (operations := BitWord.model)
        (classicalOracles := .empty)
        (correction base noQuantum n count half path.2.1)).resourcePool path.2.2 = _
  have measured := QubitReadouts.measurement_resources (allowAllocation := allowAllocation)
    (gates := AlgorithmGate.model) (oracles := oracles) (operations := BitWord.model)
    (services := .empty) (positions base noQuantum n count half)
    (qubits base noQuantum n count half) (cells base noQuantum n count) path.1
  have corrected := (UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (correction (oracles := oracles) base noQuantum n count half path.2.1)
    BitWord.model .empty).trans (correction_eventCost_context base noQuantum n count half path.2.1)
  exact congrArg₂ (· + ·) measured corrected

private lemma correction_depth_le (half : Fin 2)
    (value : CShape.Value (.fixedVector n (.finite 2))) :
    (correction (oracles := oracles) base noQuantum n count half value).evaluatedEventDepth
      (fun _ => 1) ≤ if n = 0 then 0 else 1 := by
  rw [correction, UnitaryCircuit.placeAt_evaluatedEventDepth]
  by_cases empty : n = 0
  · subst n
    change 0 ≤ 0
    exact le_rfl
  · rw [if_neg empty]
    exact ZReset.BankParallel.Correction.layer_unitDepth_le oracles n _

/-- Each nonempty batch executes at most one actual conditional quantum layer. -/
lemma batch_quantumTime_le (half : Fin 2)
    (path : (batch (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).Path) :
    (batch (allowAllocation := allowAllocation) base noQuantum n count half).quantumTime path ≤
      if n = 0 then 0 else 1 := by
  have measured :
      (measure (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half).quantumTime path.1 = 0 := by
    refine (Circuit.measurementSequence_depth (allowAllocation := allowAllocation)
      (readouts base noQuantum n count half) Resource.Event.quantumDuration path.1).trans ?_
    simp [Circuit.zEvent, Resource.Event.quantumDuration]
  change (measure (allowAllocation := allowAllocation) base noQuantum n count half).quantumTime
    path.1 + (selected (allowAllocation := allowAllocation)
      base noQuantum n count half).quantumTime path.2 ≤ _
  rw [measured, Nat.zero_add]
  change (Circuit.unitary (allowAllocation := allowAllocation) (operations := BitWord.model)
    (classicalOracles := .empty)
    (correction base noQuantum n count half path.2.1)).quantumTime path.2.2 ≤ _
  apply (Circuit.quantumTime_le_unitDepth _ _).trans
  change DepthExpr.depthEval (fun _ => 1)
    ((correction (oracles := oracles) base noQuantum n count half path.2.1).eventDepth
      BitWord.model .empty) ≤ _
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  exact correction_depth_le base noQuantum n count half path.2.1

/-- The same physical bank needs at most two correction layers, and zero at width zero. -/
lemma code_quantumTime_le
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    (code (allowAllocation := allowAllocation) base noQuantum n count).quantumTime path ≤
      if n = 0 then 0 else 2 := by
  change (batch (allowAllocation := allowAllocation) base noQuantum n count 0).quantumTime path.1 +
    (batch (allowAllocation := allowAllocation) base noQuantum n count 1).quantumTime path.2 ≤ _
  have first := batch_quantumTime_le base noQuantum n count 0 path.1
  have second := batch_quantumTime_le base noQuantum n count 1 path.2
  by_cases empty : n = 0
  · simp only [if_pos empty] at first second ⊢
    omega
  · simp only [if_neg empty] at first second ⊢
    omega

/-- Both batches retain exactly 2n measurements and their two actual selected X counts. -/
lemma code_resourcePool
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    (code (allowAllocation := allowAllocation) base noQuantum n count).resourcePool path =
      (2 * n) • ResourcePool.singleton (model := nativeModel oracles) (.measurement (2 : ℕ+)) +
        (ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.1.2.1) +
          ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.2.2.1)) •
            ResourcePool.singleton (model := nativeModel oracles) (.gate .singleQubit) := by
  change (batch (allowAllocation := allowAllocation) base noQuantum n count 0).resourcePool path.1 +
    (batch (allowAllocation := allowAllocation) base noQuantum n count 1).resourcePool path.2 = _
  rw [batch_resourcePool, batch_resourcePool, Nat.two_mul, add_nsmul, add_nsmul]
  ac_rfl

/-- The independent original 2n-wire event envelope still bounds the actual optimized reset. -/
lemma code_resourcePool_le
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    (code (allowAllocation := allowAllocation) base noQuantum n count).resourcePool path ≤
      ZReset.Bank.envelope (oracles := oracles) (2 * n) BitWord.model := by
  rw [code_resourcePool, ResourcePool.le_iff_count]
  intro event
  simp only [ZReset.Bank.envelope, ZReset.eventEnvelope, nsmul_add,
    ResourcePool.count_add, ResourcePool.count_nsmul]
  have first := ZReset.BankParallel.Correction.xCount_le n (QubitReadouts.mask path.1.2.1)
  have second := ZReset.BankParallel.Correction.xCount_le n (QubitReadouts.mask path.2.2.1)
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  omega

private lemma batch_visited (half : Fin 2)
    (path : (batch (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).Path) (visited : RuntimeCtx .quantum)
    (present : visited ∈ (batch (allowAllocation := allowAllocation)
      base noQuantum n count half).visitedContexts path) :
    visited = context base noQuantum n count := by
  change visited ∈ List.append (α := RuntimeCtx .quantum)
    ((Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles) (operations := BitWord.model)
      (classicalOracles := .empty)
      (readouts base noQuantum n count half)).visitedContexts path.1)
    [context base noQuantum n count] at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  rcases List.mem_append.mp present with measured | correction
  · exact (List.mem_replicate.mp measured).2
  · exact List.mem_singleton.mp correction

private lemma code_visited
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) (visited : RuntimeCtx .quantum)
    (present : visited ∈ (code (allowAllocation := allowAllocation)
      base noQuantum n count).visitedContexts path) :
    visited = context base noQuantum n count := by
  rcases List.mem_append.mp present with first | second
  · exact batch_visited base noQuantum n count 0 path.1 visited first
  · exact batch_visited base noQuantum n count 1 path.2 visited second

/-- The reset has exactly the original resident context, with no additional scratch bit. -/
lemma code_peakResidentSpace
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    (code (allowAllocation := allowAllocation) base noQuantum n count).peakResidentSpace path =
      (context base noQuantum n count).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rw [code_visited base noQuantum n count path visited present]
  · exact Circuit.input_residentSpace_le_peak _ path

/-- The same original storage roles give the exact auxiliary peak without reset workspace. -/
lemma code_peakAuxiliarySpace
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    (code (allowAllocation := allowAllocation) base noQuantum n count).peakAuxiliarySpace path =
      (context base noQuantum n count).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rw [code_visited base noQuantum n count path visited present]
  · exact Circuit.input_auxiliarySpace_le_peak _ path

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
