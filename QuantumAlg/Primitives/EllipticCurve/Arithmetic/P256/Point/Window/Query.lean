/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Unlookup
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Owned
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Query

/-!
# The actual stored-table query on the original owned window bank

The table is an existing classical storage reference supplied by its enclosing
construction scope. The allocation-free runtime cycle executes its actual
load, measurement/reset, paid parity feedback and unary adjoint on the literal
full/tail placements. Its original result and shared-pool systems are reused.
The outer table construction and release remain outside this owned view.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open Execution

def queryPlacement {ctx : RuntimeCtx .quantum} (stream : Fin 2) (port : WordPort)
    (highRemaining lowWidth : Nat) (addressBound : highRemaining + lowWidth ≤ 15)
    (lowBound : lowWidth ≤ 8)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit) :
    ClassicalRoutines.EllipticCurve.WindowTables.Outer.QueryPlacement
      encoding ctx 256 lowWidth highRemaining where
  frame := unlookup stream port highRemaining lowWidth addressBound lowBound
  lookup := selector stream (highRemaining + lowWidth) addressBound
  outsideAddress := by
    intro bit label
    exact resultWord_address port bit _
  outsideStack := by
    intro bit label
    exact resultWord_stack port bit stream (highRemaining + lowWidth) addressBound label
  physical := QubitLayout.canonical encoding.width
  sameWires := sameWires
  output := output
  mask := mask
  parity := parity
  temporary := temporary
  height := 8
  covered := by decide

namespace OwnedScope

variable {ctx : RuntimeCtx .quantum} (scope : OwnedScope ctx)

/-- The same original table and writable classical cells are read inside the ordered view. -/
def queryParameters (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit) :
    EncodedBit.WindowLookup.RuntimeTable.CycleParameters
      encoding scope.viewed 256 lowWidth highRemaining :=
  (queryPlacement stream port highRemaining lowWidth addressBound lowBound scope.viewed_wires
    (fun index => scope.writable (output index)) (scope.writable mask)
    (fun index => scope.writable (parity index)) (scope.writable temporary)).parameters
      (.storage (scope.view.storage source))

def queryCircuit {services : ClassicalOracleModel} (stream : Fin 2) (port : WordPort)
    (highRemaining lowWidth : Nat) (addressBound : highRemaining + lowWidth ≤ 15)
    (lowBound : lowWidth ≤ 8)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  .ownedLayoutView scope.view ((scope.queryParameters stream port highRemaining lowWidth
    addressBound lowBound source output mask parity temporary).circuit)

lemma queryCircuit_execute {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (scope.queryCircuit stream port highRemaining lowWidth addressBound lowBound source
      output mask parity temporary).execute environment Reference state =
        scope.view.join ((scope.queryParameters stream port highRemaining lowWidth addressBound
          lowBound source output mask parity temporary).circuit.execute environment Reference
            (scope.view.split state)) :=
  Circuit.execute_ownedLayoutView scope.view _ environment Reference state

/-- This is the same real stored array; no transformed table value selects circuit syntax. -/
lemma queryParameters_source_read (stream : Fin 2) (port : WordPort)
    (highRemaining lowWidth : Nat) (addressBound : highRemaining + lowWidth ≤ 15)
    (lowBound : lowWidth ≤ 8)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (store : Store ctx) :
    (scope.view.store store).read
        (scope.queryParameters stream port highRemaining lowWidth addressBound lowBound
          source output mask parity temporary).source = store.read (.storage source) :=
  scope.view.store_read store source

end OwnedScope

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
