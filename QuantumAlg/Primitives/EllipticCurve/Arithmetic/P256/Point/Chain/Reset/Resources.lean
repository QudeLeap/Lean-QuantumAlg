/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Count
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Ledger

/-! # Native events, quantum time and unchanged live space of the actual original-word reset -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (path : (circuit (services := services) port sameWires output mask).Path)

lemma circuit_measurement_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((circuit port sameWires output mask).resourcePool path) = 256 :=
  measuredResetWordCircuit_measurement_count (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask path

lemma circuit_gate_count_le (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) ((circuit port sameWires output mask).resourcePool path) ≤
        if AlgorithmGate.Coordinate.singleQubit = coordinate then 512 else 0 :=
  measuredResetWordCircuit_gate_count_le (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask coordinate path

/-- Packing 256 actual measurement bits is one paid native classical operation. -/
lemma circuit_classical_weight :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((circuit port sameWires output mask).resourcePool path) = 1 :=
  measuredResetWordCircuit_classical_weight (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask path

lemma circuit_quantumTime_le :
    (circuit (services := services) port sameWires output mask).depth
      Resource.Event.quantumDuration path ≤ 2 :=
  measuredResetWordCircuit_quantumTime_le (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask path

lemma circuit_spaces :
    (circuit (services := services) port sameWires output mask).peakResidentSpace path =
        ctx.residentSpace ∧
      (circuit (services := services) port sameWires output mask).peakAuxiliarySpace path =
        ctx.auxiliarySpace :=
  measuredResetWordCircuit_spaces (QubitLayout.canonical _) sameWires
    (Window.resultWord port) (Window.resultWord_distinct port) output mask path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset
