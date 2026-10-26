/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Direct
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Body

/-!
# Concrete native body and source of each actual original column query

The actual six query occurrences use the same A word as source. Only the
fourth occurrence uses the genuine exceptional selector. These identities
connect the existing program to the ordinary and exceptional native-query
laws, with no expansion of the 256-bit circuits or additional operations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryColumns

noncomputable section

open Execution

/-- Both actual horizontal and vertical placements load the same original A word. -/
lemma assignment_source (occurrence : Fin 6) : (assignment occurrence).source = .work1 := by
  unfold assignment
  split <;> rfl

/-- The actual exceptional body and the five actual ordinary bodies have their original syntax. -/
lemma body_eq_native (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (occurrence : Fin 6) :
    body stream width bounded occurrence =
      if occurrence.val = 3 then
        QueryInsertion.selectedBody stream width bounded
          (Chain.Offset.Exceptional.Placed.program (assignment occurrence))
      else QueryInsertion.ordinaryBody stream width bounded (assignment occurrence) := by
  unfold body
  split <;> rfl

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The real original column query is exactly the same generic source/body/unlookup program. -/
lemma direct_circuit_eq_native (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (same : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays ctx 256
      (2 ^ (highRemaining + lowWidth + 1)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (occurrence : Fin 6) :
    QueryDirect.circuit (services := services) stream highRemaining lowWidth bounded lowBound
        same arrays output mask parity temporary occurrence =
      QueryInsertion.circuit
        ((queryPlacement stream (assignment occurrence).source highRemaining lowWidth bounded
          lowBound same output mask parity temporary).parameters
            (.storage (arrays.column (column occurrence)).toCStorageRef))
        (unitaryOfEqualWires _ _ same
          (if occurrence.val = 3 then
            QueryInsertion.selectedBody stream (highRemaining + lowWidth) bounded
              (Chain.Offset.Exceptional.Placed.program (assignment occurrence))
            else QueryInsertion.ordinaryBody stream (highRemaining + lowWidth) bounded
              (assignment occurrence))) := by
  rw [assignment_source, ← body_eq_native]
  rfl

end

end QueryColumns

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
