/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Resources.Native

/-! # Same-path whole-point bounds with every actual query and selected mask retained -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Program.Parameters ctx)

attribute [local irreducible] Circuit.depth UnitaryCircuit.evaluatedEventDepth

attribute [local irreducible] ResourcePool.scale Inversion.Seed.program Inversion.program
  Native.BorrowedControl.subtractSquareProgram Normal.program Normal.inverseProgram
  Arithmetic.Reflect.program Window.Enable.program Window.Enable.inverseProgram
  Control.prepareProgram Control.restoreProgram Offset.Placed.program
  Offset.Exceptional.Placed.program Arithmetic.Call.beforeReset Arithmetic.Call.tail

/-- Both genuine arithmetic outcomes, extracted from their actual complete point paths. -/
def selectedMaskSum (path : (parameters.circuit (services := services)).Path) : Nat :=
  Arithmetic.Phase.selectedCount
      (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask
        .division parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound (parameters.divisionCallPath path)) +
    Arithmetic.Phase.selectedCount
      (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask
        .multiplication parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound (parameters.multiplicationCallPath path))

lemma selectedMaskSum_le (path : (parameters.circuit (services := services)).Path) :
    parameters.selectedMaskSum path ≤ 512 := by
  unfold selectedMaskSum
  have first := Arithmetic.Phase.selectedCount_le
    (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask
      .division parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound (parameters.divisionCallPath path))
  have second := Arithmetic.Phase.selectedCount_le
    (Arithmetic.Call.tailOutcome parameters.sameWires parameters.output parameters.mask
      .multiplication parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound (parameters.multiplicationCallPath path))
  omega

/-- The same actual two Calls retain every paid width, mask and copied-control time term. -/
lemma callQuantumTime_le (path : (parameters.circuit (services := services)).Path) :
    parameters.callQuantumTime path ≤ 1645557338 + 4 * parameters.selectedMaskSum path +
      8 * controlQuantumTime (parameters.highRemaining + parameters.lowWidth) := by
  have division := Arithmetic.Call.circuit_complete_quantumTime_le parameters.sameWires
    parameters.output parameters.mask .division parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (parameters.divisionCallPath path)
  have multiplication := Arithmetic.Call.circuit_complete_quantumTime_le parameters.sameWires
    parameters.output parameters.mask .multiplication parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (parameters.multiplicationCallPath path)
  simp only [Arithmetic.Call.transferCnot] at division multiplication
  change (parameters.arithmetic .division).depth Resource.Event.quantumDuration
    (parameters.divisionCallPath path) ≤ _ at division
  change (parameters.arithmetic .multiplication).depth Resource.Event.quantumDuration
    (parameters.multiplicationCallPath path) ≤ _ at multiplication
  dsimp only [callQuantumTime, selectedMaskSum, controlQuantumTime, controlSingle]
  omega

/-- This upper bound keeps the full actual query depths; none of their bodies is omitted. -/
lemma circuit_quantumTime_le (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.depth Resource.Event.quantumDuration path ≤
      parameters.queryQuantumTime path + 1669784446 + 4 * parameters.selectedMaskSum path +
        14 * controlQuantumTime (parameters.highRemaining + parameters.lowWidth) := by
  rw [circuit_quantumTime]
  have calls := parameters.callQuantumTime_le path
  have fixed := parameters.fixedQuantumTime_le
  omega

/-- Original runtime selector and same-table unary feedback, excluding no paid cycle direction. -/
def bareQueryToffoliLimit (highRemaining lowWidth : Nat) : Nat :=
  (2 * 2 ^ (highRemaining + lowWidth + 1) - 4) +
    (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4))

def bareQueryCnotLimit (highRemaining lowWidth : Nat) : Nat :=
  EncodedBit.WindowLookup.staticCycleCnotLimit 256 highRemaining lowWidth

def bareQuerySingleLimit (highRemaining lowWidth : Nat) : Nat :=
  (2 * 2 ^ (highRemaining + lowWidth + 1) - 2) +
    (2 * 256 + 2 + (4 * 2 ^ (highRemaining + 1) - 2))

def bareQueryQuantumTimeLimit (highRemaining lowWidth : Nat) : Nat :=
  (2 + 10 * (2 ^ (highRemaining + lowWidth) - 1) +
    2 * 2 ^ (highRemaining + lowWidth) * (2 * 8 + 1)) +
      (2 + 2 * (2 ^ lowWidth + lowWidth) +
        ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8))

lemma query_toffoli_count_le (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) ((parameters.query occurrence).resourcePool path) ≤
        bareQueryToffoliLimit parameters.highRemaining parameters.lowWidth +
          2 * controlToffoli (parameters.highRemaining + parameters.lowWidth) +
            (if occurrence.val = 3 then 52348 else 52346) := by
  have actual := (parameters.queryParameters occurrence).toffoli_count_le
    (parameters.bareQueryPath occurrence path)
  rw [query_gate_count, (queryBody_native_counts parameters.stream _
    parameters.addressBound occurrence).1]
  unfold bareQueryToffoliLimit
  omega

lemma query_cnot_count_le (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) ((parameters.query occurrence).resourcePool path) ≤
        bareQueryCnotLimit parameters.highRemaining parameters.lowWidth +
          2 * controlCnot (parameters.highRemaining + parameters.lowWidth) +
            (if occurrence.val = 3 then 508 else 510) := by
  have actual := (parameters.queryParameters occurrence).separate_coordinates
    (parameters.bareQueryPath occurrence path)
  rw [query_gate_count, (queryBody_native_counts parameters.stream _
    parameters.addressBound occurrence).2.1]
  unfold bareQueryCnotLimit
  omega

lemma query_singleQubit_count_le (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) ((parameters.query occurrence).resourcePool path) ≤
        bareQuerySingleLimit parameters.highRemaining parameters.lowWidth +
          2 * controlSingle (parameters.highRemaining + parameters.lowWidth) +
            (if occurrence.val = 3 then 4 else 0) := by
  let original := parameters.queryParameters occurrence
  have actual := EncodedBit.WindowLookup.RuntimeTable.cycleCircuit_singleQubit_count_le
    original.frame original.lookup original.outsideAddress original.outsideStack
    original.physical original.sameWires original.source original.height original.output
    original.mask original.parity original.temporary original.covered
    (parameters.bareQueryPath occurrence path)
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.gate .singleQubit) ((parameters.queryParameters occurrence).circuit.resourcePool
      (parameters.bareQueryPath occurrence path)) ≤ _ at actual
  rw [query_gate_count, (queryBody_native_counts parameters.stream _
    parameters.addressBound occurrence).2.2]
  unfold bareQuerySingleLimit
  omega

lemma query_quantumTime_le (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    (parameters.query occurrence).depth Resource.Event.quantumDuration path ≤
      bareQueryQuantumTimeLimit parameters.highRemaining parameters.lowWidth +
        2 * controlQuantumTime (parameters.highRemaining + parameters.lowWidth) +
          (if occurrence.val = 3 then 52860 else 52856) := by
  have actual := (parameters.queryParameters occurrence).quantumTime_le
    (parameters.bareQueryPath occurrence path)
  rw [query_quantumTime, queryBody_quantumTime]
  change _ ≤ bareQueryQuantumTimeLimit parameters.highRemaining parameters.lowWidth at actual
  omega

private lemma queryPool_count_le (coordinate : AlgorithmGate.Coordinate) (limit : Fin 6 → Nat)
    (bounded : ∀ occurrence
      (path : (parameters.query (services := services) occurrence).Path),
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate coordinate) ((parameters.query occurrence).resourcePool path) ≤ limit occurrence)
    (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) (parameters.queryPool path) ≤
        limit 0 + limit 1 + limit 2 + limit 3 + limit 4 + limit 5 := by
  have first := bounded 0 (parameters.queryZeroPath path)
  have second := bounded 1 (parameters.queryOnePath path)
  have third := bounded 2 (parameters.queryTwoPath path)
  have fourth := bounded 3 (parameters.queryThreePath path)
  have fifth := bounded 4 (parameters.queryFourPath path)
  have sixth := bounded 5 (parameters.queryFivePath path)
  simp only [queryPool, ResourcePool.count_add]
  omega

private lemma six_selected_amount_sum (base control ordinary exceptional : Nat) :
    let limit := fun occurrence : Fin 6 =>
      base + 2 * control + (if occurrence.val = 3 then exceptional else ordinary)
    limit 0 + limit 1 + limit 2 + limit 3 + limit 4 + limit 5 =
      5 * ordinary + exceptional + 12 * control + 6 * base := by
  norm_num
  omega

lemma queryPool_toffoli_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) (parameters.queryPool path) ≤
        314078 + 12 * controlToffoli (parameters.highRemaining + parameters.lowWidth) +
          6 * bareQueryToffoliLimit parameters.highRemaining parameters.lowWidth := by
  have actual := parameters.queryPool_count_le .toffoli
    (fun occurrence => bareQueryToffoliLimit parameters.highRemaining parameters.lowWidth +
      2 * controlToffoli (parameters.highRemaining + parameters.lowWidth) +
        (if occurrence.val = 3 then 52348 else 52346))
    parameters.query_toffoli_count_le path
  rw [six_selected_amount_sum
    (bareQueryToffoliLimit parameters.highRemaining parameters.lowWidth)
    (controlToffoli (parameters.highRemaining + parameters.lowWidth))
    52346 52348] at actual
  omega

lemma queryPool_cnot_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) (parameters.queryPool path) ≤
        3058 + 12 * controlCnot (parameters.highRemaining + parameters.lowWidth) +
          6 * bareQueryCnotLimit parameters.highRemaining parameters.lowWidth := by
  have actual := parameters.queryPool_count_le .cnot
    (fun occurrence => bareQueryCnotLimit parameters.highRemaining parameters.lowWidth +
      2 * controlCnot (parameters.highRemaining + parameters.lowWidth) +
        (if occurrence.val = 3 then 508 else 510))
    parameters.query_cnot_count_le path
  rw [six_selected_amount_sum
    (bareQueryCnotLimit parameters.highRemaining parameters.lowWidth)
    (controlCnot (parameters.highRemaining + parameters.lowWidth))
    510 508] at actual
  omega

lemma queryPool_singleQubit_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) (parameters.queryPool path) ≤
        4 + 12 * controlSingle (parameters.highRemaining + parameters.lowWidth) +
          6 * bareQuerySingleLimit parameters.highRemaining parameters.lowWidth := by
  have actual := parameters.queryPool_count_le .singleQubit
    (fun occurrence => bareQuerySingleLimit parameters.highRemaining parameters.lowWidth +
      2 * controlSingle (parameters.highRemaining + parameters.lowWidth) +
        (if occurrence.val = 3 then 4 else 0))
    parameters.query_singleQubit_count_le path
  rw [six_selected_amount_sum
    (bareQuerySingleLimit parameters.highRemaining parameters.lowWidth)
    (controlSingle (parameters.highRemaining + parameters.lowWidth))
    0 4] at actual
  omega

lemma queryQuantumTime_le (path : (parameters.circuit (services := services)).Path) :
    parameters.queryQuantumTime path ≤
      317140 + 12 * controlQuantumTime (parameters.highRemaining + parameters.lowWidth) +
        6 * bareQueryQuantumTimeLimit parameters.highRemaining parameters.lowWidth := by
  have first := parameters.query_quantumTime_le 0 (parameters.queryZeroPath path)
  have second := parameters.query_quantumTime_le 1 (parameters.queryOnePath path)
  have third := parameters.query_quantumTime_le 2 (parameters.queryTwoPath path)
  have fourth := parameters.query_quantumTime_le 3 (parameters.queryThreePath path)
  have fifth := parameters.query_quantumTime_le 4 (parameters.queryFourPath path)
  have sixth := parameters.query_quantumTime_le 5 (parameters.queryFivePath path)
  norm_num at first second third fourth fifth sixth
  unfold queryQuantumTime
  omega

lemma callPool_toffoli_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) (parameters.callPool path) ≤
        949474906 + 8 * controlToffoli (parameters.highRemaining + parameters.lowWidth) := by
  have first := parameters.arithmetic_toffoli_count_le .division
    (parameters.divisionCallPath path)
  have second := parameters.arithmetic_toffoli_count_le .multiplication
    (parameters.multiplicationCallPath path)
  simp only [callPool, ResourcePool.count_add]
  omega

lemma callPool_cnot_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) (parameters.callPool path) ≤
        603964438 + parameters.selectedMaskSum path +
          8 * controlCnot (parameters.highRemaining + parameters.lowWidth) := by
  have first := parameters.arithmetic_cnot_count_le .division
    (parameters.divisionCallPath path)
  have second := parameters.arithmetic_cnot_count_le .multiplication
    (parameters.multiplicationCallPath path)
  simp only [Arithmetic.Call.transferCnot] at first second
  simp only [callPool, ResourcePool.count_add, selectedMaskSum]
  omega

lemma callPool_singleQubit_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) (parameters.callPool path) ≤
        250955696 + 3 * parameters.selectedMaskSum path +
          8 * controlSingle (parameters.highRemaining + parameters.lowWidth) := by
  have first := parameters.arithmetic_singleQubit_count_le .division
    (parameters.divisionCallPath path)
  have second := parameters.arithmetic_singleQubit_count_le .multiplication
    (parameters.multiplicationCallPath path)
  simp only [callPool, ResourcePool.count_add, selectedMaskSum]
  omega

/-- Independent native upper bounds retain all six full queries and every paid toggle. -/
lemma circuit_toffoli_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) (parameters.circuit.resourcePool path) ≤
        972513620 + 26 * controlToffoli (parameters.highRemaining + parameters.lowWidth) +
          6 * bareQueryToffoliLimit parameters.highRemaining parameters.lowWidth := by
  have queries := parameters.queryPool_toffoli_count_le path
  have calls := parameters.callPool_toffoli_count_le path
  have fixed := parameters.fixedNativePool_toffoli_count (services := services)
  rw [circuit_resourcePool, ResourcePool.count_add, ResourcePool.count_add]
  omega

lemma circuit_cnot_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) (parameters.circuit.resourcePool path) ≤
        605209862 + parameters.selectedMaskSum path +
          26 * controlCnot (parameters.highRemaining + parameters.lowWidth) +
            6 * bareQueryCnotLimit parameters.highRemaining parameters.lowWidth := by
  have queries := parameters.queryPool_cnot_count_le path
  have calls := parameters.callPool_cnot_count_le path
  have fixed := parameters.fixedNativePool_cnot_count (services := services)
  rw [circuit_resourcePool, ResourcePool.count_add, ResourcePool.count_add]
  omega

lemma circuit_singleQubit_count_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) (parameters.circuit.resourcePool path) ≤
        251215812 + 3 * parameters.selectedMaskSum path +
          26 * controlSingle (parameters.highRemaining + parameters.lowWidth) +
            6 * bareQuerySingleLimit parameters.highRemaining parameters.lowWidth := by
  have queries := parameters.queryPool_singleQubit_count_le path
  have calls := parameters.callPool_singleQubit_count_le path
  have fixed := parameters.fixedNativePool_singleQubit_count_le (services := services)
  rw [circuit_resourcePool, ResourcePool.count_add, ResourcePool.count_add]
  omega

/-- This same-path upper bound preserves all paid mask, width and runtime-table terms. -/
lemma circuit_quantumTime_native_le (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.depth Resource.Event.quantumDuration path ≤
      1670101586 + 4 * parameters.selectedMaskSum path +
        26 * controlQuantumTime (parameters.highRemaining + parameters.lowWidth) +
          6 * bareQueryQuantumTimeLimit parameters.highRemaining parameters.lowWidth := by
  have actual := parameters.circuit_quantumTime_le path
  have queries := parameters.queryQuantumTime_le path
  omega

/-- The literal full16 specialization bounds the same actual complete point path. -/
lemma circuit_full16_coordinates
    (high : parameters.highRemaining = 7) (low : parameters.lowWidth = 8)
    (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .toffoli) (parameters.circuit.resourcePool path) ≤ 973308840 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .cnot) (parameters.circuit.resourcePool path) ≤ 807326434 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .singleQubit) (parameters.circuit.resourcePool path) ≤ 252013842 ∧
      parameters.circuit.depth Resource.Event.quantumDuration path ≤ 1678797896 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) (parameters.circuit.resourcePool path) = 2048 ∧
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (parameters.circuit.resourcePool path) ≤ 201719816 := by
  have toffoli := parameters.circuit_toffoli_count_le path
  have cnot := parameters.circuit_cnot_count_le path
  have single := parameters.circuit_singleQubit_count_le path
  have time := parameters.circuit_quantumTime_native_le path
  have mask := parameters.selectedMaskSum_le path
  have classical := parameters.circuit_classical_weight_le path
  norm_num [high, low, controlToffoli, controlCnot, controlSingle, controlQuantumTime,
    EncodedBit.Word.OneDirtyLayout.gateCount, bareQueryToffoliLimit, bareQueryCnotLimit,
    bareQuerySingleLimit, bareQueryQuantumTimeLimit,
    EncodedBit.WindowLookup.staticCycleCnotLimit,
    EncodedBit.WindowLookup.RuntimeTable.runtimeCycleClassicalLimit]
      at toffoli cnot single time classical
  exact ⟨toffoli, by omega, by omega, by omega,
    parameters.circuit_measurement_count path, classical⟩

/-- The literal tail4 specialization bounds the same actual complete point path. -/
lemma circuit_tail4_coordinates
    (high : parameters.highRemaining = 1) (low : parameters.lowWidth = 2)
    (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .toffoli) (parameters.circuit.resourcePool path) ≤ 972514108 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .cnot) (parameters.circuit.resourcePool path) ≤ 605259730 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .singleQubit) (parameters.circuit.resourcePool path) ≤ 251220930 ∧
      parameters.circuit.depth Resource.Event.quantumDuration path ≤ 1670106516 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) (parameters.circuit.resourcePool path) = 2048 ∧
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (parameters.circuit.resourcePool path) ≤ 49256 := by
  have toffoli := parameters.circuit_toffoli_count_le path
  have cnot := parameters.circuit_cnot_count_le path
  have single := parameters.circuit_singleQubit_count_le path
  have time := parameters.circuit_quantumTime_native_le path
  have mask := parameters.selectedMaskSum_le path
  have classical := parameters.circuit_classical_weight_le path
  norm_num [high, low, controlToffoli, controlCnot, controlSingle, controlQuantumTime,
    EncodedBit.Word.OneDirtyLayout.gateCount, bareQueryToffoliLimit, bareQueryCnotLimit,
    bareQuerySingleLimit, bareQueryQuantumTimeLimit,
    EncodedBit.WindowLookup.staticCycleCnotLimit,
    EncodedBit.WindowLookup.RuntimeTable.runtimeCycleClassicalLimit]
      at toffoli cnot single time classical
  exact ⟨toffoli, by omega, by omega, by omega,
    parameters.circuit_measurement_count path, classical⟩

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
