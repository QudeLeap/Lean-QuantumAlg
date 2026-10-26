/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Resources.Bounds
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Scope.Quantum.Resources

/-!
# Native and classical charges of one actual constructed-table point operation

The five paid table arrays surround the complete point program. Classical
construction is charged separately; it contributes no native quantum events.
These bounds apply to every original address width, including width zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver.Parameters

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Driver.Parameters ctx)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256)
    (spec : ModulusSpec 256) (row : Fin 34)

attribute [local irreducible] Circuit.depth UnitaryCircuit.evaluatedEventDepth

/-- Width-dependent bounds keep every original copied-control and runtime-table term. -/
def toffoliLimit : Nat :=
  972513620 + 26 * Chain.Program.Parameters.controlToffoli
    (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQueryToffoliLimit
        parameters.highRemaining parameters.lowWidth

def cnotLimit : Nat :=
  605210374 + 26 * Chain.Program.Parameters.controlCnot
    (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQueryCnotLimit
        parameters.highRemaining parameters.lowWidth

def singleQubitLimit : Nat :=
  251217348 + 26 * Chain.Program.Parameters.controlSingle
    (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQuerySingleLimit
        parameters.highRemaining parameters.lowWidth

def quantumTimeLimit : Nat :=
  1670103634 + 26 * Chain.Program.Parameters.controlQuantumTime
    (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQueryQuantumTimeLimit
        parameters.highRemaining parameters.lowWidth

def classicalLimit : Nat :=
  ClassicalRoutines.EllipticCurve.WindowTables.TableFrame.constructionBudget
    256 (parameters.highRemaining + parameters.lowWidth + 1) +
      (6 * EncodedBit.WindowLookup.RuntimeTable.runtimeCycleClassicalLimit
        256 parameters.highRemaining parameters.lowWidth + 2)

lemma circuit_toffoli_le
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .toffoli) ((Driver.circuit parameters frame spec row).resourcePool path) ≤
        parameters.toffoliLimit := by
  unfold Driver.circuit
  apply frame.withConstructedQuantumTables_count_le
    (gates := AlgorithmGate.model) (oracles := .empty) (operations := BitWord.model)
    (services := services) spec row _ (.gate .toffoli)
    (by intro coordinate incompatible; cases incompatible) parameters.toffoliLimit
  intro inner lift same table selected
  exact (Driver.kernelParameters parameters lift same table.arrays).circuit_toffoli_count_le
    selected

lemma circuit_cnot_le
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .cnot) ((Driver.circuit parameters frame spec row).resourcePool path) ≤
        parameters.cnotLimit := by
  unfold Driver.circuit
  apply frame.withConstructedQuantumTables_count_le
    (gates := AlgorithmGate.model) (oracles := .empty) (operations := BitWord.model)
    (services := services) spec row _ (.gate .cnot)
    (by intro coordinate incompatible; cases incompatible) parameters.cnotLimit
  intro inner lift same table selected
  let actual := Driver.kernelParameters parameters lift same table.arrays
  have bounded := actual.circuit_cnot_count_le selected
  have mask := actual.selectedMaskSum_le selected
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
    ((Driver.kernelParameters parameters lift same table.arrays).circuit.resourcePool selected) ≤
      605209862 + actual.selectedMaskSum selected +
        26 * Chain.Program.Parameters.controlCnot
          (parameters.highRemaining + parameters.lowWidth) +
        6 * Chain.Program.Parameters.bareQueryCnotLimit
          parameters.highRemaining parameters.lowWidth at bounded
  change _ ≤ 605210374 + 26 * Chain.Program.Parameters.controlCnot
    (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQueryCnotLimit
        parameters.highRemaining parameters.lowWidth
  omega

lemma circuit_singleQubit_le
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate .singleQubit) ((Driver.circuit parameters frame spec row).resourcePool path) ≤
        parameters.singleQubitLimit := by
  unfold Driver.circuit
  apply frame.withConstructedQuantumTables_count_le
    (gates := AlgorithmGate.model) (oracles := .empty) (operations := BitWord.model)
    (services := services) spec row _ (.gate .singleQubit)
    (by intro coordinate incompatible; cases incompatible) parameters.singleQubitLimit
  intro inner lift same table selected
  let actual := Driver.kernelParameters parameters lift same table.arrays
  have bounded := actual.circuit_singleQubit_count_le selected
  have mask := actual.selectedMaskSum_le selected
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
    ((Driver.kernelParameters parameters lift same table.arrays).circuit.resourcePool selected) ≤
      251215812 + 3 * actual.selectedMaskSum selected +
        26 * Chain.Program.Parameters.controlSingle
          (parameters.highRemaining + parameters.lowWidth) +
        6 * Chain.Program.Parameters.bareQuerySingleLimit
          parameters.highRemaining parameters.lowWidth at bounded
  change _ ≤ 251217348 + 26 * Chain.Program.Parameters.controlSingle
    (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQuerySingleLimit
        parameters.highRemaining parameters.lowWidth
  omega

lemma circuit_quantumTime_le
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    (Driver.circuit parameters frame spec row).depth Resource.Event.quantumDuration path ≤
      parameters.quantumTimeLimit := by
  unfold Driver.circuit
  apply frame.withConstructedQuantumTables_quantumTime_le spec row _ parameters.quantumTimeLimit
  intro inner lift same table selected
  let actual := Driver.kernelParameters parameters lift same table.arrays
  have bounded := actual.circuit_quantumTime_native_le selected
  have mask := actual.selectedMaskSum_le selected
  change (Driver.kernelParameters parameters lift same table.arrays).circuit.depth
    Resource.Event.quantumDuration selected ≤ 1670101586 + 4 * actual.selectedMaskSum selected +
      26 * Chain.Program.Parameters.controlQuantumTime
        (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQueryQuantumTimeLimit
        parameters.highRemaining parameters.lowWidth at bounded
  change _ ≤ 1670103634 + 26 * Chain.Program.Parameters.controlQuantumTime
    (parameters.highRemaining + parameters.lowWidth) +
      6 * Chain.Program.Parameters.bareQueryQuantumTimeLimit
        parameters.highRemaining parameters.lowWidth
  omega

lemma circuit_classical_le
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Driver.circuit parameters frame spec row).resourcePool path) ≤
        parameters.classicalLimit := by
  unfold Driver.circuit classicalLimit
  apply frame.withConstructedQuantumTables_classical_weight_le spec row _
  intro inner lift same table selected
  exact (Driver.kernelParameters parameters lift same table.arrays).circuit_classical_weight_le
    selected

/-- Lexical table construction changes no actual qubit-measurement occurrence. -/
lemma circuit_measurement_count
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((Driver.circuit parameters frame spec row).resourcePool path) =
        2048 := by
  unfold Driver.circuit
    ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame.withConstructedQuantumTables
    withCellsWithQuantumWires
  have bounded := withCellsWithQuantumWiresFrom_property
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (Transport.id ctx) rfl
    (ClassicalRoutines.EllipticCurve.WindowTables.Outer.tableShapes
      256 (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (fun cells distinct lift separated same =>
      let table := frame.tableFrame lift cells distinct separated row
      .seq (table.circuit spec)
        (.embed (ContextEmbedding.identity _)
          ((Driver.kernelParameters parameters lift
            (quantumLayout_wires_of_quantumWires same) table.arrays).circuit)))
    (fun _ _ code => ∀ selected : code.Path,
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) (code.resourcePool selected) = 2048)
    (fun _ _ _ _ _ _ available => available) (by
      intro inner cells distinct lift separated same selected
      let table := frame.tableFrame lift cells distinct separated row
      have built :=
        ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting.builder_count_zero
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          (.measurement (2 : ℕ+)) (by intro coordinate incompatible; cases incompatible)
          table spec selected.1
      rw [Circuit.resourcePool_count_seq, built, Nat.zero_add, Circuit.resourcePool_embed]
      exact (Driver.kernelParameters parameters lift
        (quantumLayout_wires_of_quantumWires same) table.arrays).circuit_measurement_count
          selected.2)
  exact bounded path

/-- The full16 native caps apply to the actual allocating table driver as well. -/
lemma circuit_full16_coordinates
    (high : parameters.highRemaining = 7) (low : parameters.lowWidth = 8)
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .toffoli) ((Driver.circuit parameters frame spec row).resourcePool path) ≤
          973308840 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .cnot) ((Driver.circuit parameters frame spec row).resourcePool path) ≤ 807326434 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .singleQubit) ((Driver.circuit parameters frame spec row).resourcePool path) ≤
          252013842 ∧
      (Driver.circuit parameters frame spec row).depth Resource.Event.quantumDuration path ≤
        1678797896 := by
  have toffoli := parameters.circuit_toffoli_le frame spec row path
  have cnot := parameters.circuit_cnot_le frame spec row path
  have single := parameters.circuit_singleQubit_le frame spec row path
  have time := parameters.circuit_quantumTime_le frame spec row path
  norm_num [toffoliLimit, cnotLimit, singleQubitLimit, quantumTimeLimit, high, low,
    Chain.Program.Parameters.controlToffoli, Chain.Program.Parameters.controlCnot,
    Chain.Program.Parameters.controlSingle, Chain.Program.Parameters.controlQuantumTime,
    EncodedBit.Word.OneDirtyLayout.gateCount,
    Chain.Program.Parameters.bareQueryToffoliLimit,
    Chain.Program.Parameters.bareQueryCnotLimit,
    Chain.Program.Parameters.bareQuerySingleLimit,
    Chain.Program.Parameters.bareQueryQuantumTimeLimit,
    EncodedBit.WindowLookup.staticCycleCnotLimit] at toffoli cnot single time
  exact ⟨toffoli, cnot, single, time⟩

lemma circuit_tail4_coordinates
    (high : parameters.highRemaining = 1) (low : parameters.lowWidth = 2)
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .toffoli) ((Driver.circuit parameters frame spec row).resourcePool path) ≤
          972514108 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .cnot) ((Driver.circuit parameters frame spec row).resourcePool path) ≤ 605259730 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate .singleQubit) ((Driver.circuit parameters frame spec row).resourcePool path) ≤
          251220930 ∧
      (Driver.circuit parameters frame spec row).depth Resource.Event.quantumDuration path ≤
        1670106516 := by
  have toffoli := parameters.circuit_toffoli_le frame spec row path
  have cnot := parameters.circuit_cnot_le frame spec row path
  have single := parameters.circuit_singleQubit_le frame spec row path
  have time := parameters.circuit_quantumTime_le frame spec row path
  norm_num [toffoliLimit, cnotLimit, singleQubitLimit, quantumTimeLimit, high, low,
    Chain.Program.Parameters.controlToffoli, Chain.Program.Parameters.controlCnot,
    Chain.Program.Parameters.controlSingle, Chain.Program.Parameters.controlQuantumTime,
    EncodedBit.Word.OneDirtyLayout.gateCount,
    Chain.Program.Parameters.bareQueryToffoliLimit,
    Chain.Program.Parameters.bareQueryCnotLimit,
    Chain.Program.Parameters.bareQuerySingleLimit,
    Chain.Program.Parameters.bareQueryQuantumTimeLimit,
    EncodedBit.WindowLookup.staticCycleCnotLimit] at toffoli cnot single time
  exact ⟨toffoli, cnot, single, time⟩

end

end Driver.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
