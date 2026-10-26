/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Resources.Bounds
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Reflect.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Normal.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Resources

/-!
# Complete same-path resources of the actual six-query point program

The two measured calls, all six complete table queries, every outside
enable toggle, square, normal test, reflection and fixed seed direction
are charged to the same real path. Each query still includes its paid
selected arithmetic body. Native coordinates and classical operations
remain separate. Table construction and the enclosing round cleanup
have their own actual programs outside this point body.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Program.Parameters ctx)

attribute [local irreducible] native query arithmetic
attribute [local irreducible] Inversion.Seed.program
  Native.BorrowedControl.subtractSquareProgram Normal.program Normal.inverseProgram
  Arithmetic.Reflect.program Window.Enable.program Window.Enable.inverseProgram

def queryZeroPath (path : (parameters.circuit (services := services)).Path) :
    (parameters.query (services := services) 0).Path := path.1.2.1

def queryOnePath (path : (parameters.circuit (services := services)).Path) :
    (parameters.query (services := services) 1).Path := path.1.2.2

def queryTwoPath (path : (parameters.circuit (services := services)).Path) :
    (parameters.query (services := services) 2).Path := path.2.2.1.1

def queryThreePath (path : (parameters.circuit (services := services)).Path) :
    (parameters.query (services := services) 3).Path := path.2.2.2.1.1

def queryFourPath (path : (parameters.circuit (services := services)).Path) :
    (parameters.query (services := services) 4).Path := path.2.2.2.2.1

def queryFivePath (path : (parameters.circuit (services := services)).Path) :
    (parameters.query (services := services) 5).Path := path.2.2.2.2.2.1

def divisionCallPath (path : (parameters.circuit (services := services)).Path) :
    (parameters.arithmetic (services := services) .division).Path := path.2.1.2.1

def multiplicationCallPath (path : (parameters.circuit (services := services)).Path) :
    (parameters.arithmetic (services := services) .multiplication).Path :=
  path.2.2.1.2.2.2.2.1

/-- All six pools include each original query's native selected addition and control clearing. -/
def queryPool (path : (parameters.circuit (services := services)).Path) : ResourcePool
    (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  (parameters.query 0).resourcePool (parameters.queryZeroPath path) +
    (parameters.query 1).resourcePool (parameters.queryOnePath path) +
    (parameters.query 2).resourcePool (parameters.queryTwoPath path) +
    (parameters.query 3).resourcePool (parameters.queryThreePath path) +
    (parameters.query 4).resourcePool (parameters.queryFourPath path) +
    (parameters.query 5).resourcePool (parameters.queryFivePath path)

/-- Both physical arithmetic measurements and their actual mask-selected tails remain present. -/
def callPool (path : (parameters.circuit (services := services)).Path) : ResourcePool
    (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  (parameters.arithmetic .division).resourcePool (parameters.divisionCallPath path) +
    (parameters.arithmetic .multiplication).resourcePool (parameters.multiplicationCallPath path)

/-- Exactly the native instructions outside the six queries and two measured calls. -/
def fixedNativePool : ResourcePool
    (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  (Window.suffixProgram Inversion.Seed.program).eventCost BitWord.model services +
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).eventCost
        BitWord.model services +
    (Window.Enable.inverseProgram parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).eventCost
        BitWord.model services +
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).eventCost
        BitWord.model services +
    (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram).eventCost
      BitWord.model services +
    Normal.program.eventCost BitWord.model services +
    (Window.Enable.inverseProgram parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).eventCost
        BitWord.model services +
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).eventCost
        BitWord.model services +
    Normal.inverseProgram.eventCost BitWord.model services +
    (Window.suffixProgram Arithmetic.Reflect.program).eventCost BitWord.model services +
    (Window.Enable.inverseProgram parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).eventCost
        BitWord.model services +
    (Window.suffixProgram
      (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty))).eventCost
        BitWord.model services

private lemma native_resourcePool
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (path : (parameters.native (services := services) body).Path) :
    (parameters.native body).resourcePool path = body.eventCost BitWord.model services := by
  unfold native
  change ResourcePool.ofList
    ((unitaryOfEqualWires _ _ parameters.sameWires body).eventTrace BitWord.model services) = _
  rw [unitaryOfEqualWires_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services]

/-- This equality comes from the actual chronological trace, without dropping any path branch. -/
lemma circuit_resourcePool (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.resourcePool path = parameters.queryPool path + parameters.callPool path +
      parameters.fixedNativePool (services := services) := by
  change
    ((parameters.native (Window.suffixProgram Inversion.Seed.program)).resourcePool path.1.1 +
      ((parameters.query 0).resourcePool path.1.2.1 +
        (parameters.query 1).resourcePool path.1.2.2)) +
    ((parameters.enable.resourcePool path.2.1.1 +
      ((parameters.arithmetic .division).resourcePool path.2.1.2.1 +
        parameters.clearEnable.resourcePool path.2.1.2.2)) +
    (((parameters.query 2).resourcePool path.2.2.1.1 +
      (parameters.enable.resourcePool path.2.2.1.2.1 +
      ((parameters.native
        (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram)).resourcePool
          path.2.2.1.2.2.1 +
      ((parameters.native Normal.program).resourcePool path.2.2.1.2.2.2.1 +
      ((parameters.arithmetic .multiplication).resourcePool path.2.2.1.2.2.2.2.1 +
        parameters.clearEnable.resourcePool path.2.2.1.2.2.2.2.2))))) +
    (((parameters.query 3).resourcePool path.2.2.2.1.1 +
      (parameters.enable.resourcePool path.2.2.2.1.2.1 +
      ((parameters.native Normal.inverseProgram).resourcePool path.2.2.2.1.2.2.1 +
      ((parameters.native (Window.suffixProgram Arithmetic.Reflect.program)).resourcePool
        path.2.2.2.1.2.2.2.1 +
        parameters.clearEnable.resourcePool path.2.2.2.1.2.2.2.2)))) +
    ((parameters.query 4).resourcePool path.2.2.2.2.1 +
      ((parameters.query 5).resourcePool path.2.2.2.2.2.1 +
        (parameters.native (Window.suffixProgram
          (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))).resourcePool
            path.2.2.2.2.2.2))))) = _
  simp only [enable, clearEnable, native_resourcePool, queryPool, callPool,
    fixedNativePool, queryZeroPath, queryOnePath, queryTwoPath, queryThreePath,
    queryFourPath, queryFivePath, divisionCallPath, multiplicationCallPath]
  ac_rfl

def queryQuantumTime (path : (parameters.circuit (services := services)).Path) : Nat :=
  (parameters.query 0).depth Resource.Event.quantumDuration (parameters.queryZeroPath path) +
    (parameters.query 1).depth Resource.Event.quantumDuration (parameters.queryOnePath path) +
    (parameters.query 2).depth Resource.Event.quantumDuration (parameters.queryTwoPath path) +
    (parameters.query 3).depth Resource.Event.quantumDuration (parameters.queryThreePath path) +
    (parameters.query 4).depth Resource.Event.quantumDuration (parameters.queryFourPath path) +
    (parameters.query 5).depth Resource.Event.quantumDuration (parameters.queryFivePath path)

def callQuantumTime (path : (parameters.circuit (services := services)).Path) : Nat :=
  (parameters.arithmetic .division).depth Resource.Event.quantumDuration
      (parameters.divisionCallPath path) +
    (parameters.arithmetic .multiplication).depth Resource.Event.quantumDuration
      (parameters.multiplicationCallPath path)

/-- All twelve outside native fragments retain their own actual dependency schedule. -/
def fixedQuantumTime : Nat :=
  Inversion.Seed.program.evaluatedEventDepth Resource.Event.quantumDuration +
    3 * (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).evaluatedEventDepth
        Resource.Event.quantumDuration +
    3 * (Window.Enable.inverseProgram parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound).evaluatedEventDepth
        Resource.Event.quantumDuration +
    Native.BorrowedControl.subtractSquareProgram.evaluatedEventDepth
      Resource.Event.quantumDuration +
    Normal.program.evaluatedEventDepth Resource.Event.quantumDuration +
    Normal.inverseProgram.evaluatedEventDepth Resource.Event.quantumDuration +
    Arithmetic.Reflect.program.evaluatedEventDepth Resource.Event.quantumDuration +
    (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).evaluatedEventDepth
      Resource.Event.quantumDuration

private lemma native_quantumTime
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (path : (parameters.native (services := services) body).Path) :
    (parameters.native body).depth Resource.Event.quantumDuration path =
      body.evaluatedEventDepth Resource.Event.quantumDuration := by
  unfold native
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((unitaryOfEqualWires _ _ parameters.sameWires body).eventDepth BitWord.model services) = _
  rw [unitaryOfEqualWires_depth,
    UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]

private lemma sequence_quantumTime {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind}
    (first : Circuit model pre mid false) (second : Circuit model mid post false)
    (path : (first.seq second).Path) :
    (first.seq second).depth Resource.Event.quantumDuration path =
      first.depth Resource.Event.quantumDuration path.1 +
        second.depth Resource.Event.quantumDuration path.2 := by
  rcases path with ⟨left, right⟩
  exact Circuit.depth_seq first second Resource.Event.quantumDuration left right

attribute [local irreducible] Circuit.depth UnitaryCircuit.evaluatedEventDepth

section

-- Retained paths use these composition aliases in their dependent input type.
-- Only their Circuit constructors are transparent to the rewrite matcher.
attribute [local implicit_reducible] circuit differences division multiplication
  reflection finish enable clearEnable

/-- Whole-program time follows the same chronological syntax and retained measured paths. -/
lemma circuit_quantumTime (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.depth Resource.Event.quantumDuration path =
      parameters.queryQuantumTime path + parameters.callQuantumTime path +
        parameters.fixedQuantumTime := by
  unfold circuit
  rw [sequence_quantumTime]
  simp only [differences, division, multiplication, reflection, finish,
    enable, clearEnable, sequence_quantumTime, native_quantumTime,
    Window.suffixProgram_quantumTime, queryQuantumTime, callQuantumTime, fixedQuantumTime,
    queryZeroPath, queryOnePath, queryTwoPath, queryThreePath, queryFourPath, queryFivePath,
    divisionCallPath, multiplicationCallPath]
  omega

end

private lemma query_measurement_count (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((parameters.query occurrence).resourcePool path) = 256 := by
  unfold query at *
  exact Window.QueryInsertion.circuit_measurement_count _ _ path

private lemma arithmetic_measurement_count (kind : Arithmetic.Call.Kind)
    (path : (parameters.arithmetic (services := services) kind).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((parameters.arithmetic kind).resourcePool path) = 256 := by
  unfold arithmetic at *
  exact Arithmetic.Call.circuit_measurement_count parameters.sameWires parameters.output
    parameters.mask
    kind parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound path

/-- The six measured query words and two actual arithmetic resets each measure 256 systems. -/
lemma circuit_measurement_count (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      (parameters.circuit.resourcePool path) = 2048 := by
  rw [circuit_resourcePool]
  simp only [queryPool, callPool, fixedNativePool, ResourcePool.count_add,
    query_measurement_count, arithmetic_measurement_count,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]

private lemma native_classical_weight
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (body.eventCost BitWord.model services) = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context body
        BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

private lemma query_classical_weight_le (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((parameters.query occurrence).resourcePool path) ≤
        EncodedBit.WindowLookup.RuntimeTable.runtimeCycleClassicalLimit
          256 parameters.highRemaining parameters.lowWidth := by
  unfold query at *
  exact Window.QueryInsertion.circuit_classical_weight_le _ _ path

private lemma arithmetic_classical_weight (kind : Arithmetic.Call.Kind)
    (path : (parameters.arithmetic (services := services) kind).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((parameters.arithmetic kind).resourcePool path) = 1 := by
  unfold arithmetic at *
  exact Arithmetic.Call.circuit_classical_weight parameters.sameWires parameters.output
    parameters.mask
    kind parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound path

/-- Paid table parity and both actual arithmetic packs keep their own classical coordinate. -/
lemma circuit_classical_weight_le (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (parameters.circuit.resourcePool path) ≤
        6 * EncodedBit.WindowLookup.RuntimeTable.runtimeCycleClassicalLimit
          256 parameters.highRemaining parameters.lowWidth + 2 := by
  have first := parameters.query_classical_weight_le 0 (parameters.queryZeroPath path)
  have second := parameters.query_classical_weight_le 1 (parameters.queryOnePath path)
  have third := parameters.query_classical_weight_le 2 (parameters.queryTwoPath path)
  have fourth := parameters.query_classical_weight_le 3 (parameters.queryThreePath path)
  have fifth := parameters.query_classical_weight_le 4 (parameters.queryFourPath path)
  have sixth := parameters.query_classical_weight_le 5 (parameters.queryFivePath path)
  rw [circuit_resourcePool]
  simp only [queryPool, callPool, fixedNativePool, ResourcePool.weightedCount_add,
    native_classical_weight, arithmetic_classical_weight]
  omega

/-- All real table arrays, scratch cells and the complete physical bank stay in the peak. -/
lemma circuit_spaces (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.peakResidentSpace path = ctx.residentSpace ∧
      parameters.circuit.peakAuxiliarySpace path = ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ path, Circuit.fixed_peakAuxiliarySpace _ path⟩

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
