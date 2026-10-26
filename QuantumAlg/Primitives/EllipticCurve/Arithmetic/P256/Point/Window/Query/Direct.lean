/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Columns

/-!
# Actual table queries under lexical classical workspace extension

The same complete quantum wires are certified explicitly. Actual table
cells may have been allocated since the outer owned view was chosen, so
no new view keys are inferred from a storage transport. The native query
and its arithmetic act directly on the same whole physical quantum bank.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryDirect

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- Real existing table and classical feedback cells, with the full physical order proved. -/
def parameters (stream : Fin 2) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (same : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit) :=
  (queryPlacement stream .work1 highRemaining lowWidth addressBound lowBound same
    output mask parity temporary).parameters (.storage source)

/-- Same actual load, paid arithmetic/control clearing and same-table measured unlookup. -/
def circuit (stream : Fin 2) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (same : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays ctx 256
      (2 ^ (highRemaining + lowWidth + 1)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (occurrence : Fin 6) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  QueryInsertion.circuit
    (parameters stream highRemaining lowWidth addressBound lowBound same
      (arrays.column (QueryColumns.column occurrence)).toCStorageRef output mask parity temporary)
    (unitaryOfEqualWires _ _ same
      (QueryColumns.body stream (highRemaining + lowWidth) addressBound occurrence))

/-- Every actual path retains the same resident quantum and classical context. -/
lemma circuit_peakResidentSpace (stream : Fin 2) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (same : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays ctx 256
      (2 ^ (highRemaining + lowWidth + 1)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (occurrence : Fin 6)
    (path : (circuit (services := services) stream highRemaining lowWidth addressBound lowBound
      same arrays output mask parity temporary occurrence).Path) :
    (circuit stream highRemaining lowWidth addressBound lowBound same arrays output mask parity
      temporary occurrence).peakResidentSpace path = ctx.residentSpace :=
  (circuit stream highRemaining lowWidth addressBound lowBound same arrays output mask parity
    temporary occurrence).fixed_peakResidentSpace path

end

end QueryDirect

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
