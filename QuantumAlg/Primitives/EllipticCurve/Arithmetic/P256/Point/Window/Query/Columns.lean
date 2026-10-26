/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Insertion
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Exceptional.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns

/-!
# Six actual original table columns with their point arithmetic

The fixed order is negative x, negative y, three x, negative exceptional
slope, x plus one, and negative y again. Every value is loaded into A and
retained while it is added to X or Y. Only the exceptional slope uses
E and not N; the other five use E. The point body supplies the arithmetic
between these six query pairs and keeps the same five array lifetimes.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryColumns

noncomputable section

open Execution

/-- Original five-array storage order, including the repeated last negative-y query. -/
def column : Fin 6 → Fin 5 := ![0, 1, 2, 3, 4, 1]

/-- A is always the loaded source, while the other original word is completely retained. -/
def assignment (occurrence : Fin 6) : PortAssignment :=
  if occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4 then
    Chain.Offset.Placed.horizontal else Chain.Offset.Placed.vertical

/-- The exceptional query is controlled by the actual independent N system. -/
def body (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (occurrence : Fin 6) : QueryInsertion.Body :=
  QueryInsertion.selectedBody stream width bounded
    (if occurrence.val = 3 then Chain.Offset.Exceptional.Placed.program (assignment occurrence)
      else Chain.Offset.Placed.program (assignment occurrence))

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The actual same allocated column is used by the loader and paid unlookup. -/
def circuit (scope : OwnedScope ctx) (stream : Fin 2) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays ctx 256
      (2 ^ (highRemaining + lowWidth + 1)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (occurrence : Fin 6) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  QueryInsertion.ownedCircuit scope stream highRemaining lowWidth addressBound lowBound
    (arrays.column (column occurrence)).toCStorageRef output mask parity temporary
    (body stream (highRemaining + lowWidth) addressBound occurrence)

/-- Query arithmetic, physical controls and both query directions allocate no quantum systems. -/
lemma circuit_peakResidentSpace (scope : OwnedScope ctx) (stream : Fin 2)
    (highRemaining lowWidth : Nat) (addressBound : highRemaining + lowWidth ≤ 15)
    (lowBound : lowWidth ≤ 8)
    (arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays ctx 256
      (2 ^ (highRemaining + lowWidth + 1)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (occurrence : Fin 6)
    (path : (circuit scope (services := services) stream highRemaining lowWidth addressBound
      lowBound arrays output mask parity temporary occurrence).Path) :
    (circuit scope stream highRemaining lowWidth addressBound lowBound arrays output mask
      parity temporary occurrence).peakResidentSpace path = ctx.residentSpace :=
  (circuit scope stream highRemaining lowWidth addressBound lowBound arrays output mask
    parity temporary occurrence).fixed_peakResidentSpace path

end

end QueryColumns

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
