/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Denominators
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Batch
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns

/-!
# Full coordinate values retained through the actual C/D inverse stages

The actual denominator traversal changes only C and one scalar word. The
actual total batch changes only C/D and its original scalar words. Every
coordinate word therefore remains identical at both chronological stage
boundaries, with no assumption on old destination or working values.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The actual denominator traversal retains every word of any original array outside C. -/
lemma layerDenominatorsRecord_read_array_row (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector (2 ^ window) (.unsignedWord width)))
    (row : Fin (2 ^ window)) (denominatorFree : frame.arrays.c.key ≠ array.key) :
    (frame.layerDenominatorsRecord level environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  apply frame.layerDenominatorsRecord_read_other
  · change frame.work.temporary.key ∉ [array.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.arrays.c.key ∉ [array.key]
    simpa only [List.mem_singleton] using denominatorFree

/-- Every previously constructed canonical group coordinate survives the real denominator pass. -/
lemma layerDenominatorsRecord_rowsValue (curve : CurveSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (bound : Nat)
    (rows : frame.CoordinateRowsValue curve point bound before.1) :
    frame.CoordinateRowsValue curve point bound
      (frame.layerDenominatorsRecord level environment before).1.1 := by
  intro row positive below
  rw [frame.layerDenominatorsRecord_read_array_row level environment before frame.arrays.x row
    (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 0 (by decide)),
    frame.layerDenominatorsRecord_read_array_row level environment before frame.arrays.y row
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 1 (by decide))]
  exact rows row positive below

/-- The same canonical group coordinates survive the original complete C/D batch inverse. -/
lemma batchRecord_rowsValue (curve : CurveSpec width) (count : Nat) (fits : count < 2 ^ window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (bound : Nat)
    (rows : frame.CoordinateRowsValue curve point bound before.1) :
    frame.CoordinateRowsValue curve point bound
      (frame.batch.valueRecord curve.field count fits environment before).1.1 := by
  intro row positive below
  rw [frame.batchRecord_read_array_row curve.field count fits environment before frame.arrays.x row
    (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 0 (by decide))
    (by simpa [Arrays.column] using frame.arrays.column_key_ne 3 0 (by decide)),
    frame.batchRecord_read_array_row curve.field count fits environment before frame.arrays.y row
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 1 (by decide))
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 3 1 (by decide))]
  exact rows row positive below

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
