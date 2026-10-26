/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Owned
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Correctness

/-!
# Actual arithmetic between one runtime load and its same-table unlookup

The actual source array is read by both original query directions. The
loaded A word is used while the paid whole-digit enable is live; the
literal inverse clears that enable before the full-pool unlookup. Every
instruction acts inside the same existing owned bank and classical Store.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {lowWidth highRemaining : Nat}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

abbrev Body := UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical encoding.width).toQuantum

/-- The same paid actual selector toggle and its own inverse bracket the native arithmetic. -/
def selectedBody (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (body : Native.Circuit) : Body :=
  (Enable.program stream width bounded).seq
    ((Window.program stream body).seq (Enable.inverseProgram stream width bounded))

/-- Both targets consume the existing quantum A word through the original native addition. -/
def ordinaryBody (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) : Body :=
  selectedBody stream width bounded (Chain.Offset.Placed.program ports)

/-- The original literal runtime loader remains before the actual inserted body. -/
def load (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining) :
    Circuit Model ctx ctx false :=
  RuntimeTable.lookupCircuit parameters.source parameters.lookup
    (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
      parameters.outsideStack) parameters.physical parameters.sameWires parameters.height

/-- The same source reference supplies every paid parity feedback row after the inserted body. -/
def unlookup (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining) :
    Circuit Model ctx ctx false :=
  RuntimeUnlookup.circuit parameters.frame parameters.physical parameters.sameWires
    parameters.output parameters.mask parameters.parity parameters.temporary
    (RuntimeTable.splitInputs parameters.source)

/-- The body is physically executed between load and unlookup, without an extra allocation. -/
def circuit (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout) :
    Circuit Model ctx ctx false :=
  (load parameters).seq ((Circuit.unitary body).seq (unlookup parameters))

variable (scope : OwnedScope ctx)

/-- Retain the original source array and outcome cells in one complete owned view. -/
def ownedCircuit (stream : Fin 2) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (body : Body) : Circuit Model ctx ctx false :=
  .ownedLayoutView scope.view
    (circuit (scope.queryParameters stream .work1 highRemaining lowWidth addressBound lowBound
      source output mask parity temporary)
      (unitaryOfEqualWires _ _ scope.viewed_wires body))

/-- Complete Store, service state, History and arbitrary Reference use the same actual child. -/
lemma ownedCircuit_execute
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (stream : Fin 2) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (body : Body) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (ownedCircuit scope stream highRemaining lowWidth addressBound lowBound source output mask
      parity temporary body).execute environment Reference state =
        scope.view.join ((circuit
          (scope.queryParameters stream .work1 highRemaining lowWidth addressBound lowBound
            source output mask parity temporary)
          (unitaryOfEqualWires _ _ scope.viewed_wires body)).execute environment Reference
            (scope.view.split state)) :=
  Circuit.execute_ownedLayoutView scope.view _ environment Reference state

/-- Real inserted arithmetic and both query directions retain the existing resident space. -/
lemma ownedCircuit_peakResidentSpace (stream : Fin 2) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (source : CStorageRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord 256)))
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (body : Body)
    (path : (ownedCircuit scope (services := services) stream highRemaining lowWidth addressBound
      lowBound source output mask parity temporary body).Path) :
    (ownedCircuit scope stream highRemaining lowWidth addressBound lowBound source output mask
      parity temporary body).peakResidentSpace path = ctx.residentSpace :=
  (ownedCircuit scope stream highRemaining lowWidth addressBound lowBound source output mask
    parity temporary body).fixed_peakResidentSpace path

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
