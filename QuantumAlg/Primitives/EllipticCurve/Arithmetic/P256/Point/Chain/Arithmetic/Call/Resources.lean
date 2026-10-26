/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Resources
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Same-path resources of the two actual measured arithmetic calls

The stored mask on the actual feedback path selects the real native tail.
Native gate coordinates, 256 measurements, one paid classical pack, quantum
duration and unchanged live space are kept separate. No endpoint resource
contract is taken from a different resident producer.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)

/-- The original reset's actual path, including its real pack and selected physical X layer. -/
def resetPath
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    (Reset.circuit (services := services) .numerator sameWires output mask).Path := by
  dsimp only [circuit, Reset.Instrument.circuit, Circuit.Path] at path
  exact path.2.1

/-- This is the real stored value recorded by the feedback branch, with no reachability premise. -/
def tailOutcome
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    Fin (2 ^ 256) := by
  dsimp only [circuit, Reset.Instrument.circuit, Reset.Instrument.feedback, Circuit.Path] at path
  exact resultConstant path.2.2.1

/-- Exact native pools of the same prefix, physical reset and actual selected tail. -/
lemma circuit_resourcePool
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    (circuit sameWires output mask kind stream width bounded).resourcePool path =
      (beforeReset kind stream width bounded).eventCost BitWord.model services +
        ((Reset.circuit .numerator sameWires output mask).resourcePool
          (resetPath sameWires output mask kind stream width bounded path) +
          (tail kind stream width bounded
            (tailOutcome sameWires output mask kind stream width bounded path)).eventCost
              BitWord.model services) := by
  change ResourcePool.ofList
    ((beforeReset kind stream width bounded).eventTrace BitWord.model services ++
      ((Reset.circuit .numerator sameWires output mask).eventTrace
        (resetPath sameWires output mask kind stream width bounded path) ++
        (tail kind stream width bounded
          (tailOutcome sameWires output mask kind stream width bounded path)).eventTrace
            BitWord.model services)) = _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services]
  rfl

/-- The actual reset contributes only its at-most 512 single-qubit H/X gates. -/
lemma circuit_gate_count_le (coordinate : AlgorithmGate.Coordinate)
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) ((circuit sameWires output mask kind stream width bounded).resourcePool
        path) ≤
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
          (beforeReset kind stream width bounded).eventCost +
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
          (tail kind stream width bounded
            (tailOutcome sameWires output mask kind stream width bounded path)).eventCost +
        if AlgorithmGate.Coordinate.singleQubit = coordinate then 512 else 0 := by
  rw [circuit_resourcePool, ResourcePool.count_add, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  have resetBound := Reset.circuit_gate_count_le .numerator sameWires output mask
    (resetPath sameWires output mask kind stream width bounded path) coordinate
  dsimp only
  omega

lemma circuit_measurement_count
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((circuit sameWires output mask kind stream width bounded).resourcePool path) = 256 := by
  rw [circuit_resourcePool, ResourcePool.count_add, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context,
    Reset.circuit_measurement_count, Nat.zero_add, Nat.add_zero]

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

/-- The pack of the same 256 physical outcomes remains one paid native classical operation. -/
lemma circuit_classical_weight
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((circuit sameWires output mask kind stream width bounded).resourcePool path) = 1 := by
  rw [circuit_resourcePool, ResourcePool.weightedCount_add, ResourcePool.weightedCount_add,
    native_classical_weight, native_classical_weight, Reset.circuit_classical_weight,
    Nat.zero_add, Nat.add_zero]

/-- Complete native layer duration, retaining the true selected mask and physical reset depth. -/
lemma circuit_quantumTime
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    (circuit sameWires output mask kind stream width bounded).depth
        Resource.Event.quantumDuration path =
      (beforeReset kind stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration +
        ((Reset.circuit .numerator sameWires output mask).depth Resource.Event.quantumDuration
          (resetPath sameWires output mask kind stream width bounded path) +
          (tail kind stream width bounded
            (tailOutcome sameWires output mask kind stream width bounded path)).evaluatedEventDepth
              Resource.Event.quantumDuration) := by
  change DepthExpr.depthEval Resource.Event.quantumDuration
      ((unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
        (beforeReset kind stream width bounded)).eventDepth BitWord.model services) +
    ((Reset.circuit .numerator sameWires output mask).depth Resource.Event.quantumDuration
      (resetPath sameWires output mask kind stream width bounded path) +
      DepthExpr.depthEval Resource.Event.quantumDuration
        ((unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
          (tail kind stream width bounded
            (tailOutcome sameWires output mask kind stream width bounded path))).eventDepth
              BitWord.model services)) = _
  rw [unitaryOfEqualWires_depth, unitaryOfEqualWires_depth,
    UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context,
    UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]

lemma circuit_quantumTime_le
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    (circuit sameWires output mask kind stream width bounded).depth
        Resource.Event.quantumDuration path ≤
      (beforeReset kind stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration +
        (tail kind stream width bounded
          (tailOutcome sameWires output mask kind stream width bounded path)).evaluatedEventDepth
            Resource.Event.quantumDuration + 2 := by
  rw [circuit_quantumTime]
  have resetBound := Reset.circuit_quantumTime_le .numerator sameWires output mask
    (resetPath sameWires output mask kind stream width bounded path)
  omega

lemma circuit_spaces
    (path : (circuit (services := services) sameWires output mask kind stream width bounded).Path) :
    (circuit sameWires output mask kind stream width bounded).peakResidentSpace path =
        ctx.residentSpace ∧
      (circuit sameWires output mask kind stream width bounded).peakAuxiliarySpace path =
        ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ path, Circuit.fixed_peakAuxiliarySpace _ path⟩

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
