/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Protection

/-!
# Internally certified runtime query storage for the fresh feedback frame

The allocator supplies same-shaped cell distinctness. Different classical
shape constructors cannot share a live key. Together these facts certify the
actual parity reads and writes against the packed measurement mask and the
real table arrays, including arbitrary structural row and column indices.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

open Execution ClassicalWorkspace EncodedBit.WindowLookup

private lemma differentShape_key_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {firstShape secondShape : CShape} (first : CStorageRef ctx firstShape)
    (second : CStorageRef ctx secondShape) (different : firstShape ≠ secondShape) :
    first.key ≠ second.key :=
  fun same => different (CStorageRef.storageRef_shape_eq_of_key first second same)

namespace Frame

variable {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    {wordWidth parityCount : Nat} (frame : Frame outer wordWidth parityCount)

/-- Further real table allocation preserves all fresh feedback identities and key laws. -/
def transport (lift : Transport outer inner) : Frame inner wordWidth parityCount where
  output := fun index => lift.liftWrite (frame.output index)
  mask := lift.liftWrite frame.mask
  parity := fun index => lift.liftWrite (frame.parity index)
  temporary := lift.liftWrite frame.temporary
  outputDistinct := by
    intro first second same
    apply frame.outputDistinct
    simpa only [Transport.liftWrite_key] using same
  parityDistinct := by
    intro first second same
    apply frame.parityDistinct
    simpa only [Transport.liftWrite_key] using same
  temporaryDifferent := by
    intro index
    simpa only [Transport.liftWrite_key] using frame.temporaryDifferent index

variable {ctx : RuntimeCtx .quantum} (scratch : Frame ctx wordWidth parityCount)

/-- Measurement destinations cannot overwrite any cell of the actual stored table array. -/
lemma output_table_free {tableSize : Nat}
    (source : CStorageRef ctx (.fixedVector tableSize (.unsignedWord wordWidth)))
    (output : Fin wordWidth) (column : Fin tableSize) :
    (scratch.output output).key ∉
      (CInputRef.vectorGet (.storage source) column).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using
    differentShape_key_ne (scratch.output output).toCStorageRef source (by intro same; cases same)

/-- The packed measured mask and table array have distinct real live keys. -/
lemma mask_table_free {tableSize : Nat}
    (source : CStorageRef ctx (.fixedVector tableSize (.unsignedWord wordWidth)))
    (column : Fin tableSize) :
    scratch.mask.key ∉ (CInputRef.vectorGet (.storage source) column).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using
    differentShape_key_ne scratch.mask.toCStorageRef source (by intro same; cases same)

/-- Restrict the genuinely allocated parity bank to the actual finite feedback columns. -/
lemma rowProtection {columns tableSize : Nat} {Rows : Type}
    (position : Fin columns → Fin parityCount) (injective : Function.Injective position)
    (source : CStorageRef ctx (.fixedVector tableSize (.unsignedWord wordWidth)))
    (index : Rows → Fin columns → Fin tableSize) :
    RuntimeRow.Protection (.storage scratch.mask.toCStorageRef)
      (fun column => scratch.parity (position column)) scratch.temporary
      (fun row column => .vectorGet (.storage source) (index row column)) where
  parityDistinct := by
    intro first second same
    exact injective (scratch.parityDistinct same)
  temporaryDifferent := fun column => scratch.temporaryDifferent (position column)
  maskFree := by
    intro column
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      differentShape_key_ne (scratch.parity (position column)).toCStorageRef
        scratch.mask.toCStorageRef (by intro same; cases same)
  temporaryMaskFree := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      differentShape_key_ne scratch.temporary.toCStorageRef scratch.mask.toCStorageRef
        (by intro same; cases same)
  tableFree := by
    intro column row selected
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      differentShape_key_ne (scratch.parity (position column)).toCStorageRef source
        (by intro same; cases same)
  temporaryTableFree := by
    intro row column
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      differentShape_key_ne scratch.temporary.toCStorageRef source (by intro same; cases same)

end Frame

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
