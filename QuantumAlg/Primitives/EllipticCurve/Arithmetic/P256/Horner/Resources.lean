/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Stage
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Resources

/-! # Native ledger for the actual multiplier-bit latch and selected arithmetic body -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (port : MultiplierPort saved) (outer : EncodedBit saved)
  (outerMultiplier : (operandSavedBit saved outer).wire ≠
    (operandMultiplierBit saved port).wire)

private lemma operandAddition_eventCost :
    (operandAdditionProgram saved).eventCost = Controlled.controlledAdditionProgram.eventCost := by
  rw [operandAdditionProgram, programList_eventCost, operandAdditionGates,
    map_event_prodLeft, Controlled.controlledAdditionProgram, programList_eventCost]

/-- The literal two-Toffoli latch is paid beside the complete controlled native body. -/
lemma stage_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (stageProgram saved port outer outerMultiplier).eventCost = 52348 := by
  rw [stageProgram, Selection.toffoli_count,
    ← programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical (operandEncoding saved).width) (oracles := .empty)]
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (operandAdditionProgram saved).eventCost + 2 = _
  rw [operandAddition_eventCost, Controlled.controlledAddition_toffoli_count]

/-- Original caller placement and coherent bit selection add no CNOT to the controlled body. -/
lemma stage_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (stageProgram saved port outer outerMultiplier).eventCost = 508 := by
  rw [stageProgram, Selection.cnot_count,
    ← programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical (operandEncoding saved).width) (oracles := .empty)]
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
    (operandAdditionProgram saved).eventCost = _
  rw [operandAddition_eventCost, Controlled.controlledAddition_cnot_count]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
