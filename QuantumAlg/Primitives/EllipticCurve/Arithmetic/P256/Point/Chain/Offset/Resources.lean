/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Program
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Native coordinates of the actual selected quantum table-word addition -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

noncomputable section

open EncodedBit GateSpec Horner ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved) (selector : EncodedBit saved)

private lemma body_eventCost :
    (operandAdditionProgram saved).eventCost = Controlled.controlledAdditionProgram.eventCost := by
  rw [operandAdditionProgram, programList_eventCost, operandAdditionGates,
    map_event_prodLeft, Controlled.controlledAdditionProgram, programList_eventCost]

/-- Both real selector-copy instructions are charged beside the same complete addition ledger. -/
lemma program_eventCost :
    (program saved selector).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) +
        (operandAdditionProgram saved).eventCost +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) := by
  have actual := congrArg
    (ResourcePool.ofList (model := .quantum AlgorithmGate.model .empty))
    (program_eventTrace saved selector)
  simpa only [UnitaryCircuit.ofList_eventTrace_eq_eventCost, ResourcePool.ofList_append,
    ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero] using actual

/-- All native controlled-addition Toffolis remain charged; the two copied selectors add none. -/
lemma program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program saved selector).eventCost = 52346 := by
  have different : (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model .empty)) ≠
      .gate .cnot := by
    intro equal
    have coordinates : AlgorithmGate.Coordinate.toffoli = .cnot := Resource.Event.gate.inj equal
    cases coordinates
  rw [program_eventCost, ResourcePool.count_add, ResourcePool.count_add, body_eventCost,
    Controlled.controlledAddition_toffoli_count]
  simp only [ResourcePool.count_singleton_of_ne different, Nat.zero_add, Nat.add_zero]

/-- The actual source CNOTs and both paid selector copies share the same ledger. -/
lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program saved selector).eventCost = 510 := by
  rw [program_eventCost, ResourcePool.count_add, ResourcePool.count_add, body_eventCost,
    Controlled.controlledAddition_cnot_count]
  norm_num [ResourcePool.count_singleton]

/-- This selected-addition syntax has no uncontrolled single-qubit instruction. -/
lemma program_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program saved selector).eventCost = 0 := by
  have different : (.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model .empty)) ≠
      .gate .cnot := by
    intro equal
    have coordinates : AlgorithmGate.Coordinate.singleQubit = .cnot := Resource.Event.gate.inj equal
    cases coordinates
  rw [program_eventCost, ResourcePool.count_add, ResourcePool.count_add, body_eventCost,
    Controlled.controlledAddition_x_count]
  simp only [ResourcePool.count_singleton_of_ne different, Nat.add_zero]

/-- The source body's shared real selector retains its actual sequential quantum schedule. -/
lemma program_quantumTime :
    (program saved selector).evaluatedEventDepth Resource.Event.quantumDuration = 52856 := by
  have scheduled := programList_quantumTime
    (QubitLayout.canonical (operandEncoding saved).width) .empty (gates saved selector)
  have counted := primitiveEventCount_programList
    (QubitLayout.canonical (operandEncoding saved).width) .empty (gates saved selector)
  have native : primitiveEventCount (program saved selector) = 52856 := by
    rw [primitiveEventCount, program_x_count, program_cnot_count, program_toffoli_count]
  exact scheduled.trans (counted.symm.trans native)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset
