/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Exceptional
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Exceptional.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Resources

/-! # Native resources of the actual E and negative N selected quantum-word addition -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

namespace Exceptional

noncomputable section

open EncodedBit GateSpec Horner ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (enable normal : EncodedBit saved) (distinct : enable.wire ≠ normal.wire)

/-- The two actual negative-control guards add two Toffolis to the same source body. -/
lemma program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program saved enable normal distinct).eventCost = 52348 := by
  rw [program, programList_toffoli_count_eq_sum, gates, List.map_append, List.map_append,
    List.sum_append, List.sum_append]
  change 1 + ((operandAdditionGates saved).map toffoliMultiplicity).sum + 1 = 52348
  rw [← programList_toffoli_count_eq_sum
    (layout := QubitLayout.canonical (operandEncoding saved).width) (oracles := .empty)]
  change 1 + ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (operandAdditionProgram saved).eventCost + 1 = 52348
  rw [Offset.body_eventCost, Controlled.controlledAddition_toffoli_count]

/-- Neither real guard adds a CNOT; every CNOT in the native source is retained. -/
lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program saved enable normal distinct).eventCost = 508 := by
  rw [program, programList_cnot_count_eq_sum, gates, List.map_append, List.map_append,
    List.sum_append, List.sum_append]
  change 0 + ((operandAdditionGates saved).map cnotMultiplicity).sum + 0 = 508
  rw [Nat.zero_add, Nat.add_zero, ← programList_cnot_count_eq_sum
    (layout := QubitLayout.canonical (operandEncoding saved).width) (oracles := .empty)]
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
    (operandAdditionProgram saved).eventCost = 508
  rw [Offset.body_eventCost, Controlled.controlledAddition_cnot_count]

/-- Each negative-control mask is paid and restored around its actual native Toffoli. -/
lemma program_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program saved enable normal distinct).eventCost = 4 := by
  rw [program, programList_x_count_eq_sum, gates, List.map_append, List.map_append,
    List.sum_append, List.sum_append]
  change 2 + ((operandAdditionGates saved).map xMultiplicity).sum + 2 = 4
  rw [← programList_x_count_eq_sum
    (layout := QubitLayout.canonical (operandEncoding saved).width) (oracles := .empty)]
  change 2 + ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
    (operandAdditionProgram saved).eventCost + 2 = 4
  rw [Offset.body_eventCost, Controlled.controlledAddition_x_count]

/-- All shared-control conflicts remain in the same actual sequential native schedule. -/
lemma program_quantumTime :
    (program saved enable normal distinct).evaluatedEventDepth
      Resource.Event.quantumDuration = 52860 := by
  have scheduled := programList_quantumTime
    (QubitLayout.canonical (operandEncoding saved).width) .empty
      (gates saved enable normal distinct)
  have counted := primitiveEventCount_programList
    (QubitLayout.canonical (operandEncoding saved).width) .empty
      (gates saved enable normal distinct)
  have native : primitiveEventCount (program saved enable normal distinct) = 52860 := by
    rw [primitiveEventCount, program_x_count, program_cnot_count, program_toffoli_count]
  exact scheduled.trans (counted.symm.trans native)

namespace Placed

lemma program_toffoli_count (ports : PortAssignment) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program ports).eventCost = 52348 :=
  Native.placed_count (Placement.layout ports) _ _ _
    (Exceptional.program_toffoli_count (Placement.savedEncoding ports)
      (Placed.enable ports) (Placed.normal ports) (enable_normal_ne ports))

lemma program_cnot_count (ports : PortAssignment) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program ports).eventCost = 508 :=
  Native.placed_count (Placement.layout ports) _ _ _
    (Exceptional.program_cnot_count (Placement.savedEncoding ports)
      (Placed.enable ports) (Placed.normal ports) (enable_normal_ne ports))

lemma program_x_count (ports : PortAssignment) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program ports).eventCost = 4 :=
  Native.placed_count (Placement.layout ports) _ _ _
    (Exceptional.program_x_count (Placement.savedEncoding ports)
      (Placed.enable ports) (Placed.normal ports) (enable_normal_ne ports))

lemma program_quantumTime (ports : PortAssignment) :
    (program ports).evaluatedEventDepth Resource.Event.quantumDuration = 52860 :=
  ((Placement.layout ports).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Exceptional.program_quantumTime (Placement.savedEncoding ports)
      (Placed.enable ports) (Placed.normal ports) (enable_normal_ne ports))

end Placed

end

end Exceptional

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset
