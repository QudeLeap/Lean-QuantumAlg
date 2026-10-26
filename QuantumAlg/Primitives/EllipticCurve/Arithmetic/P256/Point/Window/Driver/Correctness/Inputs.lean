/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Protection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Point

/-!
# The actual feedback frame supplies the point's table separation

The allocated frame's original distinct cells and their storage shapes
establish the query and table-read conditions. Restricting its parity bank
keeps the original indices and references. These are internal storage laws;
no quantum action, affine domain, table value or probability is assumed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver

noncomputable section

open Sampling

open Execution EncodedBit.WindowLookup
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {parityCount : Nat}
    (parameters : Chain.Program.Parameters ctx) (scratch : Storage.Frame ctx 256 parityCount)
    (position : Fin (2 ^ parameters.lowWidth) → Fin parityCount)
    (positionDistinct : Function.Injective position)
    (outputSame : parameters.output = scratch.output)
    (maskSame : parameters.mask = scratch.mask)
    (paritySame : parameters.parity = fun index => scratch.parity (position index))
    (temporarySame : parameters.temporary = scratch.temporary)

include positionDistinct outputSame maskSame paritySame temporarySame in
/-- The same allocated feedback cells protect each actual complete selected table column. -/
lemma pointQuerySeparation_of_frame (occurrence : Fin 6) :
    parameters.QueryFieldSeparation occurrence where
  distinct := by
    rw [outputSame]
    exact scratch.outputDistinct
  protection := by
    rw [maskSame, paritySame, temporarySame]
    change RuntimeRow.Protection (.storage scratch.mask.toCStorageRef)
      (fun index => scratch.parity (position index)) scratch.temporary
      (fun row : Bool × Fin (2 ^ parameters.highRemaining) => fun column =>
        CInputRef.vectorGet (.storage (parameters.querySource occurrence))
          (RuntimeTable.index row.1 (joinedAddress row.2 column)))
    exact scratch.rowProtection position positionDistinct (parameters.querySource occurrence)
      (fun row : Bool × Fin (2 ^ parameters.highRemaining) =>
        fun column => RuntimeTable.index row.1 (joinedAddress row.2 column))
  outputFree := by
    intro index top high low
    simpa only [outputSame, RuntimeTable.splitInputs] using
      scratch.output_table_free (parameters.querySource occurrence) index
        (RuntimeTable.index top (joinedAddress high low))
  maskFree := by
    intro top high low
    simpa only [maskSame, RuntimeTable.splitInputs] using
      scratch.mask_table_free (parameters.querySource occurrence)
        (RuntimeTable.index top (joinedAddress high low))

/-- Typed actual feedback references cannot overwrite a complete stored table array. -/
private lemma feedback_table_free {shape : CShape} {length : Nat}
    (feedback : CWriteRef ctx shape)
    (table : CWriteRef ctx (.fixedVector length (.unsignedWord 256)))
    (different : shape ≠ .fixedVector length (.unsignedWord 256)) :
    feedback.key ∉ (CInputRef.storage table.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using
    Storage.differentShape_key_ne feedback.toCStorageRef table.toCStorageRef different

/-- Actual frame references discharge every internal table-separation field. -/
def pointFieldInputs_of_frame
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (table : TableFrame ctx 256 (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus)
    (arraysSame : parameters.arrays = table.arrays) :
    Chain.Program.Parameters.PointFieldTableInputs parameters where
  curve := curve
  frame := table
  point := point
  sameModulus := sameModulus
  arrays := arraysSame
  distinct := by
    rw [outputSame]
    exact scratch.outputDistinct
  separation := pointQuerySeparation_of_frame parameters scratch position positionDistinct
    outputSame maskSame paritySame temporarySame
  outputFree := fun index column => feedback_table_free
    (parameters.output index) (table.finishColumns column) (by intro same; cases same)
  maskFree := fun column => feedback_table_free
    parameters.mask (table.finishColumns column) (by intro same; cases same)
  parityFree := fun index column => feedback_table_free
    (parameters.parity index) (table.finishColumns column) (by intro same; cases same)
  temporaryFree := fun column => feedback_table_free
    parameters.temporary (table.finishColumns column) (by intro same; cases same)

end

end Driver

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
