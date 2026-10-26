/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Inputs.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Tangent.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Preservation

/-!
# Original coordinates and inputs through the actual final denominator traversal

The real negative-tangent preparation writes only its selected C row and
the two existing scalar working words. Every original coordinate and loaded
input survives the whole chronological traversal on its actual Store.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Every actual array outside C retains every word through one real tangent record. -/
lemma tangentRecord_read_array_row (spec : ModulusSpec width) (selected : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) (row : Fin length)
    (denominatorFree : frame.arrays.c.key ≠ array.key) :
    (frame.tangentRecord spec selected environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  apply frame.tangentRecord_read_other
  · change frame.work.product.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.work.temporary.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.arrays.c.key ∉ [array.key]
    simpa only [List.mem_singleton] using denominatorFree

variable {window : Nat} (frame : TableFrame ctx width (2 ^ window))

/-- Every actual structural read outside the three real output cells survives the full pass. -/
lemma finalDenominatorsRecord_read_other (spec : ModulusSpec width)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (denominatorFree : frame.arrays.c.key ∉ observed.storageKeys) :
    (frame.finalDenominatorsRecord spec environment before).1.1.read observed =
      before.1.read observed := by
  exact Circuit.forRangeRecord_invariant (2 ^ window - 1)
    (fun index => frame.tangentDenominatorRow (nonzeroRow window index))
    (fun index => frame.tangentRecord spec (nonzeroRow window index) environment)
    (fun _ current => current.1.read observed = before.1.read observed)
    (fun index current established =>
      (frame.tangentRecord_read_other spec (nonzeroRow window index) environment current
        observed productFree temporaryFree denominatorFree).trans established)
    before rfl

/-- No original coordinate word is overwritten by the complete final denominator traversal. -/
lemma finalDenominatorsRecord_read_array_row (spec : ModulusSpec width)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector (2 ^ window) (.unsignedWord width)))
    (row : Fin (2 ^ window)) (denominatorFree : frame.arrays.c.key ≠ array.key) :
    (frame.finalDenominatorsRecord spec environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  apply frame.finalDenominatorsRecord_read_other
  · change frame.work.product.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.work.temporary.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.arrays.c.key ∉ [array.key]
    simpa only [List.mem_singleton] using denominatorFree

/-- The same original modulus, constants, curve and base inputs survive every actual step. -/
lemma finalDenominatorsRecord_originalInputs (spec : ModulusSpec width)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1
      (frame.finalDenominatorsRecord spec environment before).1.1 := by
  exact Circuit.forRangeRecord_invariant (2 ^ window - 1)
    (fun index => frame.tangentDenominatorRow (nonzeroRow window index))
    (fun index => frame.tangentRecord spec (nonzeroRow window index) environment)
    (fun _ current => OriginalInputs frame before.1 current.1)
    (fun index current established => OriginalInputs.trans frame before.1 current.1 _
      established (frame.tangentRecord_originalInputs spec (nonzeroRow window index)
        environment current)) before (OriginalInputs.refl frame before.1)

/-- Complete canonical group-coordinate values survive the original final tangent traversal. -/
lemma finalDenominatorsRecord_rowsValue (curve : CurveSpec width)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (bound : Nat)
    (rows : frame.CoordinateRowsValue curve point bound before.1) :
    frame.CoordinateRowsValue curve point bound
      (frame.finalDenominatorsRecord curve.field environment before).1.1 := by
  intro row positive below
  rw [frame.finalDenominatorsRecord_read_array_row curve.field environment before
      frame.arrays.x row
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 0 (by decide)),
    frame.finalDenominatorsRecord_read_array_row curve.field environment before
      frame.arrays.y row
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 1 (by decide))]
  exact rows row positive below

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
