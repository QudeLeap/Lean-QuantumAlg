/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Bank.Parallel.Program
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Program
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Trace.Boundary
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Actual counts, quantum time, and scratch peaks for parallel bank reset

Every bank wire is still measured exactly once, and every selected X is
still charged. Only disjoint native corrections share a dependency layer.
The parent accounts for all simultaneous scalar outcome cells in both live
space coordinates and releases them before returning to the original context.
-/

namespace QuantumAlg.ZReset.BankParallel

open Execution

noncomputable section

variable {allowAllocation : Bool} {ctx : RuntimeCtx .quantum} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}

variable (positions : Fin width ≃ Fin ctx.systemCount)
  (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
  (cells : Fin width → CWriteRef ctx (.finite 2))

/-- Every actual Z write remains in the native measurement pool. -/
lemma measure_resourcePool
    (path : (measure (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (measure (allowAllocation := allowAllocation) positions qubits cells).resourcePool path =
      width • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) :=
  QubitReadouts.measurement_resources (allowAllocation := allowAllocation) positions (fun index =>
    qubits (positions index)) cells path

/-- Stored-result selection counts exactly its actual one outcomes, with no correction for zero. -/
lemma selected_resourcePool
    (path : (selected (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (selected (allowAllocation := allowAllocation) positions qubits cells).resourcePool path =
      Correction.xCount ctx.systemCount
        (fun wire => QubitReadouts.mask path.1 (positions.symm wire)) •
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) :=
          by
  rcases path with ⟨value, unitPath⟩
  let program := Correction.program ctx.quantumLayout qubits oracles
    (fun wire => QubitReadouts.mask value (positions.symm wire))
  exact (UnitaryCircuit.ofList_eventTrace_eq_eventCost program operations services).trans
    (Correction.program_eventCost_context ctx.quantumLayout qubits oracles _ operations services)

/-- The complete fixed body contains precisely the measured wires and its selected X events. -/
lemma body_resourcePool
    (path : (body (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (body (allowAllocation := allowAllocation) positions qubits cells).resourcePool path =
      width • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) +
      Correction.xCount ctx.systemCount
        (fun wire => QubitReadouts.mask path.2.1 (positions.symm wire)) •
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) :=
          by
  change (measure (allowAllocation := allowAllocation) positions qubits cells).resourcePool path.1 +
    (selected (allowAllocation := allowAllocation) positions qubits cells).resourcePool path.2 = _
  rw [measure_resourcePool, selected_resourcePool]

/-- Measurements retain their real events while contributing zero canonical quantum duration. -/
lemma measure_quantumTime
    (path : (measure (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (measure (allowAllocation := allowAllocation) positions qubits cells).quantumTime path = 0 := by
  refine (Circuit.measurementSequence_depth
    (QubitReadouts.readouts positions (fun index => qubits (positions index)) cells)
    Resource.Event.quantumDuration path).trans ?_
  simp [Circuit.zEvent, Resource.Event.quantumDuration]

/-- An actual branch executes at most one layer of native corrections. -/
lemma selected_quantumTime_le
    (path : (selected (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (selected (allowAllocation := allowAllocation) positions qubits cells).quantumTime path ≤ 1 :=
      by
  let program := Correction.program ctx.quantumLayout qubits oracles
    (fun wire => QubitReadouts.mask path.1 (positions.symm wire))
  change (Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
    (classicalOracles := services) program).quantumTime path.2 ≤ 1
  apply (Circuit.quantumTime_le_unitDepth _ path.2).trans
  change DepthExpr.depthEval (fun _ => 1) (program.eventDepth operations services) ≤ 1
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  exact Correction.program_unitDepth_le ctx.quantumLayout qubits oracles _

/-- Real measurement and feed-forward surround exactly one possible correction layer. -/
lemma body_quantumTime_le
    (path : (body (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (body (allowAllocation := allowAllocation) positions qubits cells).quantumTime path ≤ 1 := by
  refine (Circuit.quantumTime_seq
    (measure (allowAllocation := allowAllocation) positions qubits cells)
    (selected (allowAllocation := allowAllocation) positions qubits cells)
    path.1 path.2).trans_le ?_
  rw [measure_quantumTime, Nat.zero_add]
  exact selected_quantumTime_le positions qubits cells path.2

private lemma body_visited
    (path : (body (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path)
    (visited : RuntimeCtx .quantum)
    (present : visited ∈ (body (allowAllocation := allowAllocation) positions qubits
      cells).visitedContexts path) : visited = ctx := by
  change visited ∈ List.append (α := RuntimeCtx .quantum)
    ((Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles) (operations := operations)
      (classicalOracles := services)
      (QubitReadouts.readouts positions
        (fun index => qubits (positions index)) cells)).visitedContexts
        path.1)
    [ctx] at present
  have visitedMeasure := Circuit.measurementSequence_visitedContexts
    (allowAllocation := allowAllocation) (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := operations) (classicalOracles := services)
    (QubitReadouts.readouts positions (fun index => qubits (positions index)) cells) path.1
  rw [visitedMeasure] at present
  rcases List.mem_append.mp present with measured | correction
  · exact (List.mem_replicate.mp measured).2
  · simpa only [List.mem_singleton] using correction

/-- The fixed body has no resident storage beyond its real supplied context. -/
lemma body_peakResidentSpace
    (path : (body (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (body (allowAllocation := allowAllocation) positions qubits cells).peakResidentSpace path =
      ctx.residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rw [body_visited positions qubits cells path visited present]
  · exact Circuit.input_residentSpace_le_peak _ path

/-- The fixed body introduces no hidden auxiliary cells. -/
lemma body_peakAuxiliarySpace
    (path : (body (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).Path) :
    (body (allowAllocation := allowAllocation) positions qubits cells).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rw [body_visited positions qubits cells path visited present]
  · exact Circuit.input_auxiliarySpace_le_peak _ path

/-- The actual parent reset uses one possible correction layer and no quantum allocation. -/
lemma code_quantumTime_le
    (path : (code (oracles := oracles) qubits operations services).Path) :
    (code (oracles := oracles) qubits operations services).quantumTime path ≤ 1 := by
  revert path
  by_cases empty : ctx.systemCount = 0
  · rw [code_zero qubits empty]
    intro path
    simp only [Circuit.quantumTime_id, Nat.zero_le]
  · rw [code_nonzero qubits empty]
    intro path
    rw [Circuit.quantumTime, Workspace.scope_depth]
    exact body_quantumTime_le _ _ _ _

/-- Every parent path contains exactly one Z write per wire and its actual selected X count. -/
lemma code_resourcePool
    (path : (code (oracles := oracles) qubits operations services).Path) :
    ∃ corrections : Nat, corrections ≤ ctx.systemCount ∧
      (code (oracles := oracles) qubits operations services).resourcePool path =
        ctx.systemCount • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) +
        corrections • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit)
            := by
  revert path
  by_cases empty : ctx.systemCount = 0
  · rw [code_zero qubits empty]
    intro path
    refine ⟨0, Nat.zero_le _, ?_⟩
    simp only [empty, zero_nsmul, zero_add]
    rfl
  · rw [code_nonzero qubits empty]
    intro path
    let fixed := body (allowAllocation := true) (oracles := oracles)
      (operations := operations) (services := services)
      (Workspace.wireEquiv ctx ctx.systemCount) (work_qubits qubits)
      (Workspace.reference ctx ctx.systemCount)
    let actual := Workspace.pathEquiv
      (model := .quantum AlgorithmGate.model oracles operations services)
      ctx ctx.systemCount fixed path
    refine ⟨Correction.xCount (Workspace.context ctx ctx.systemCount).systemCount
      (fun wire => QubitReadouts.mask actual.2.1
        ((Workspace.wireEquiv ctx ctx.systemCount).symm wire)), ?_, ?_⟩
    · exact (Correction.xCount_le _ _).trans_eq
        (Workspace.context_systemCount ctx ctx.systemCount)
    · rw [Workspace.scope_resourcePool, body_resourcePool]

/-- The independent native envelope has one Z write and at most one X for every bank wire. -/
lemma code_resourcePool_le
    (path : (code (oracles := oracles) qubits operations services).Path) :
    (code (oracles := oracles) qubits operations services).resourcePool path ≤
      ctx.systemCount • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services)
          (.measurement (2 : ℕ+)) +
      ctx.systemCount • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) :=
          by
  obtain ⟨corrections, bound, actual⟩ := code_resourcePool qubits path
  rw [actual, ResourcePool.le_iff_count]
  intro event
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ bound) _

/-- The real event trace contains exactly one dimension-two measurement per physical wire. -/
lemma code_measurement_count
    (path : (code (oracles := oracles) qubits operations services).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.measurement (2 : ℕ+))
      ((code (oracles := oracles) qubits operations services).resourcePool path) = ctx.systemCount
        := by
  obtain ⟨corrections, _, actual⟩ := code_resourcePool qubits path
  rw [actual]
  simp

/-- Positive-width reset contains an actual measurement even if every correction is identity. -/
lemma code_measured (positive : 0 < ctx.systemCount)
    (path : (code (oracles := oracles) qubits operations services).Path) :
    Resource.Event.measurement
      (model := .quantum AlgorithmGate.model oracles operations services) (2 : ℕ+) ∈
      (code (oracles := oracles) qubits operations services).eventTrace path := by
  apply List.count_pos_iff.mp
  have countPositive : 0 < ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles operations services) (.measurement (2 : ℕ+))
    ((code (oracles := oracles) qubits operations services).resourcePool path) := by
      rw [code_measurement_count]
      exact positive
  simpa only [Circuit.resourcePool, ResourcePool.count_ofList] using countPositive

/-- Peak resident storage adds exactly one scalar result bit per physical bank wire. -/
lemma code_peakResidentSpace
    (path : (code (oracles := oracles) qubits operations services).Path) :
    (code (oracles := oracles) qubits operations services).peakResidentSpace path =
      ctx.systemCount • SpacePool.ofShape (.finite 2) + ctx.residentSpace := by
  revert path
  by_cases empty : ctx.systemCount = 0
  · rw [code_zero qubits empty]
    intro path
    rw [Circuit.peakResidentSpace_id, empty, zero_nsmul, zero_add]
  · rw [code_nonzero qubits empty]
    intro path
    exact Workspace.scope_peakResidentSpace
      (model := .quantum AlgorithmGate.model oracles operations services) ctx ctx.systemCount _
      (body_peakResidentSpace _ _ _) path

/-- Peak auxiliary storage counts the same real parent-owned scalar result bits. -/
lemma code_peakAuxiliarySpace
    (path : (code (oracles := oracles) qubits operations services).Path) :
    (code (oracles := oracles) qubits operations services).peakAuxiliarySpace path =
      ctx.systemCount • SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace := by
  revert path
  by_cases empty : ctx.systemCount = 0
  · rw [code_zero qubits empty]
    intro path
    rw [Circuit.peakAuxiliarySpace_id, empty, zero_nsmul, zero_add]
  · rw [code_nonzero qubits empty]
    intro path
    exact Workspace.scope_peakAuxiliarySpace
      (model := .quantum AlgorithmGate.model oracles operations services) ctx ctx.systemCount _
      (body_peakAuxiliarySpace _ _ _) path

end

end QuantumAlg.ZReset.BankParallel
