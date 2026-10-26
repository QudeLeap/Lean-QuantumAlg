/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Scope.Quantum

/-!
# Actual constructed-table scope around the measured point operation

Five fresh arrays are allocated and populated by the paid original table
builder. The same arrays supply every query of the actual measured point
kernel. Classical feedback cells are structurally transported from the
caller; all quantum wires keep their complete original ordered sequence.
Only the original classical table scope permits allocation. The actual
native/measured point kernel does not allocate any quantum system.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- Original caller references before the five shorter-lived arrays are allocated. -/
structure Parameters (ctx : RuntimeCtx .quantum) where
  stream : Fin 2
  highRemaining : Nat
  lowWidth : Nat
  addressBound : highRemaining + lowWidth ≤ 15
  lowBound : lowWidth ≤ 8
  sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires
  output : Fin 256 → CWriteRef ctx (.finite 2)
  mask : CWriteRef ctx (.bits 256)
  parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit
  temporary : CWriteRef ctx .bit

/-- Existing caller cells and quantum wires accompany exactly the newly built arrays. -/
def kernelParameters (parameters : Parameters ctx) {inner : RuntimeCtx .quantum}
    (lift : Transport ctx inner) (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
    (arrays : ClassicalRoutines.EllipticCurve.WindowTables.Arrays inner 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1))) :
    Chain.Program.Parameters inner where
  stream := parameters.stream
  highRemaining := parameters.highRemaining
  lowWidth := parameters.lowWidth
  addressBound := parameters.addressBound
  lowBound := parameters.lowBound
  sameWires := parameters.sameWires.trans same
  arrays := arrays
  output := fun index => lift.liftWrite (parameters.output index)
  mask := lift.liftWrite parameters.mask
  parity := fun index => lift.liftWrite (parameters.parity index)
  temporary := lift.liftWrite parameters.temporary

/-- Real five-array construction, complete measured point execution and lexical array release. -/
def circuit (parameters : Parameters ctx)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256)
    (spec : ModulusSpec 256) (row : Fin 34) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx :=
  frame.withConstructedQuantumTables spec row (fun lift same table =>
    (kernelParameters parameters lift same table.arrays).circuit)

end

end Driver

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
