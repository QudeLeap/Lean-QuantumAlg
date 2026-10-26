/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Scope
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program
import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model

/-!
# Original sampler inputs beside genuinely fresh feedback storage

The input record contains only original physical wires, retained Fourier
results, classical table preparation ports and the actual public arithmetic
parameters. Point feedback destinations are obtained from the lexical scope,
not supplied by the caller. Its freshness proves separation from all original
Fourier result cells.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve

/-- Actual original inputs; no replaced or ignored feedback references are accepted. -/
structure Inputs (ctx : RuntimeCtx .quantum) where
  sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires
  results : Fourier.Results ctx
  frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256
  modulus : ModulusSpec 256
  curve : CurveSpec 256
  order : ModulusSpec 260
  base : CInputRef ctx (PointShape 256)
  target : CInputRef ctx (PointShape 256)
  seedX : Fin (2 ^ 256)
  seedY : Fin (2 ^ 256)

namespace Inputs

variable {outer inner : RuntimeCtx .quantum} (original : Inputs outer)

/-- Structural transport retains every original cell and ordered physical wire. -/
def transport (lift : Transport outer inner)
    (same : outer.quantumLayout.wires = inner.quantumLayout.wires) : Inputs inner where
  sameWires := original.sameWires.trans same
  results := {
    cells := fun position => lift.liftWrite (original.results.cells position)
    distinct := by
      intro first second equal
      apply original.results.distinct
      simpa only [Transport.liftWrite_key] using equal }
  frame := original.frame.transport lift
  modulus := original.modulus
  curve := original.curve
  order := original.order
  base := lift.liftInput original.base
  target := lift.liftInput original.target
  seedX := original.seedX
  seedY := original.seedY

/-- The real allocated feedback cells instantiate the unchanged chronological sampler. -/
def samplerParameters (lift : Transport outer inner)
    (same : outer.quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift) :
    Sampling.Parameters inner where
  sameWires := original.sameWires.trans same
  results := (original.transport lift same).results
  output := scratch.output
  mask := scratch.mask
  parity := scratch.parity
  temporary := scratch.temporary
  output_separate := by
    intro bit position
    simpa only [transport, Transport.liftWrite_input, CInputRef.storageKeys,
      List.mem_singleton] using
      fresh.output bit (.storage (original.results.cells position).toCStorageRef)
  mask_separate := by
    intro position
    simpa only [transport, Transport.liftWrite_input, CInputRef.storageKeys,
      List.mem_singleton] using
      fresh.mask (.storage (original.results.cells position).toCStorageRef)
  parity_separate := by
    intro bit position
    simpa only [transport, Transport.liftWrite_input, CInputRef.storageKeys,
      List.mem_singleton] using
      fresh.parity bit (.storage (original.results.cells position).toCStorageRef)
  temporary_separate := by
    intro position
    simpa only [transport, Transport.liftWrite_input, CInputRef.storageKeys,
      List.mem_singleton] using
      fresh.temporary (.storage (original.results.cells position).toCStorageRef)
  frame := original.frame.transport lift
  modulus := original.modulus

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
