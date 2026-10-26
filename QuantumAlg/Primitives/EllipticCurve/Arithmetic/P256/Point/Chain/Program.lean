/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Reflect.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Normal
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Seed
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Direct

/-!
# Actual measured point operation with six queries of the same five tables

All fragments execute on the same existing physical quantum bank and
classical storage. The two arithmetic measurements and the six unlookups
are retained in the real Circuit paths. Paid enable toggles clear the
whole pool before each query and resident inversion. The genuine second
difference normal flag survives the multiplication and exceptional query.

This program includes the fixed quantum seed preparation and its own
adjoint. Arithmetic correctness and good-prefix workspace restoration
are separate obligations; the adjoint alone does not reset arbitrary
bad-branch workspace. The enclosing sampler must perform its actual
whole-bank cleanup before reinitializing a round.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- References to the actual existing bank, table arrays and sequentially reused feedback cells. -/
structure Parameters (ctx : RuntimeCtx .quantum) where
  stream : Fin 2
  highRemaining : Nat
  lowWidth : Nat
  addressBound : highRemaining + lowWidth ≤ 15
  lowBound : lowWidth ≤ 8
  sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
    ctx.quantumLayout.wires
  arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays ctx 256
    (2 ^ (highRemaining + lowWidth + 1))
  output : Fin 256 → CWriteRef ctx (.finite 2)
  mask : CWriteRef ctx (.bits 256)
  parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit
  temporary : CWriteRef ctx .bit

namespace Parameters

variable (parameters : Parameters ctx)

/-- Exact ordered physical wires carry every native instruction of the supplied whole-bank body. -/
def native (body : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical Window.encoding.width).toQuantum) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  .unitary (unitaryOfEqualWires _ _ parameters.sameWires body)

/-- Same actual column for both load and measured unlookup, with the real paid selected addition. -/
def query (occurrence : Fin 6) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  Window.QueryDirect.circuit parameters.stream parameters.highRemaining parameters.lowWidth
    parameters.addressBound parameters.lowBound parameters.sameWires parameters.arrays
    parameters.output parameters.mask parameters.parity parameters.temporary occurrence

def enable : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  parameters.native (Window.Enable.program parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)

def clearEnable :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  parameters.native (Window.Enable.inverseProgram parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)

def arithmetic (kind : Arithmetic.Call.Kind) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  Arithmetic.Call.circuit parameters.sameWires parameters.output parameters.mask kind
    parameters.stream (parameters.highRemaining + parameters.lowWidth) parameters.addressBound

/-- Paid fixed source initialization and both first-difference table additions. -/
def differences :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (parameters.native (Window.suffixProgram Inversion.Seed.program)).seq
    ((parameters.query 0).seq (parameters.query 1))

/-- The first real measured call returns lambda and the original first X difference. -/
def division :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  parameters.enable.seq ((parameters.arithmetic .division).seq parameters.clearEnable)

/-- The second difference is formed before its genuine normal selector and measured product. -/
def multiplication :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (parameters.query 2).seq
    (parameters.enable.seq
      ((parameters.native
        (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram)).seq
        ((parameters.native Normal.program).seq
          ((parameters.arithmetic .multiplication).seq parameters.clearEnable))))

/-- The exceptional query keeps X, so the actual inverse normal test sees its original predicate. -/
def reflection :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (parameters.query 3).seq
    (parameters.enable.seq
      ((parameters.native Normal.inverseProgram).seq
        ((parameters.native (Window.suffixProgram Arithmetic.Reflect.program)).seq
          parameters.clearEnable)))

/-- Qx+1 follows p-1-X, then negative Qy; the actual fixed source preparation is reversed. -/
def finish :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (parameters.query 4).seq
    ((parameters.query 5).seq
      (parameters.native (Window.suffixProgram
        (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))))

/-- The full actual six-query, two-mask point operation on one unchanged resident bank. -/
def circuit :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  parameters.differences.seq
    (parameters.division.seq
      (parameters.multiplication.seq (parameters.reflection.seq parameters.finish)))

/-- Every reachable path has the same resident space, independently of arithmetic validity. -/
lemma circuit_peakResidentSpace
    (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.peakResidentSpace path = ctx.residentSpace :=
  parameters.circuit.fixed_peakResidentSpace path

end Parameters

end

end Program

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
