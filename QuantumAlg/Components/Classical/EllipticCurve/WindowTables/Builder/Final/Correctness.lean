/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Final.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Identity

/-!
# Actual complete five-table construction has the original canonical group values

The existing binary layers, real negative-tangent pass, paid C/D batch,
original final-row traversal and literal five-zero identity clear are
composed through the same actual predecessor Stores and retained paths.
Every requested table entry is therefore attached to the actual native
construction record, including address zero and window width zero.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Each of the five actual identity-row overwrites retains the original protected inputs. -/
lemma clearIdentityRecord_originalInputs (row : Fin length)
    (before : Store ctx × model.HiddenState) :
    OriginalInputs frame before.1 (frame.clearIdentityRecord (model := model) row before).1.1 := by
  have written (column : Fin 5) : (frame.arrays.column column).key ∈ frame.outputKeys := by
    fin_cases column <;> simp [Arrays.column, outputKeys]
  exact Circuit.forRangeRecord_invariant 5
    (frame.clearIdentityBody row) (frame.clearIdentityStep row)
    (fun _ current => OriginalInputs frame before.1 current.1)
    (fun column current established => by
      rw [frame.clearIdentityStep_store]
      constructor
      · exact (Store.read_applyOp_of_not_mem_storageKeys current.1
          (rowWriteOp (frame.arrays.column column) row frame.zero) (wordRead frame.modulus)
          (frame.outputKey_modulus_free _ (written column))).trans established.modulus
      · intro input member
        exact (Store.read_applyOp_of_not_mem_storageKeys current.1
          (rowWriteOp (frame.arrays.column column) row frame.zero) input
          (frame.outputKey_free _ (written column) input member)).trans
            (established.inputs input member)) before (OriginalInputs.refl frame before.1)

variable {window : Nat} (frame : TableFrame ctx width (2 ^ window))

attribute [local irreducible] coordinateLayersRecord finalDenominatorsRecord finishRowsRecord
attribute [local irreducible] BatchFrame.valueRecord clearIdentityRecord

/-- The actual unchanged original full program constructs all five canonical group-table words. -/
lemma circuitRecord_tableValue (curve : CurveSpec width) (environment : model.Environment)
    (before : Store ctx × model.HiddenState) (point : Point curve) (order : Nat)
    (prime : order.Prime) (large : 3 < order) (original : addOrderOf point = order)
    (tableFits : 2 ^ window < order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (zero : (before.1.read frame.zero).toNat = 0)
    (one : (before.1.read frame.one).toNat = 1)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (baseValue : CoordinateValue curve (before.1.read frame.baseX)
      (before.1.read frame.baseY) point) :
    let returned := (frame.circuitRecord curve.field environment before).1.1
    OriginalInputs frame before.1 returned ∧ TableValue curve frame point returned := by
  let coordinates := (frame.coordinateLayersRecord curve.field environment before).1
  let denominators := (frame.finalDenominatorsRecord curve.field environment coordinates).1
  let inverted := (frame.batch.valueRecord curve.field (2 ^ window - 1) finalBatchFits
    environment denominators).1
  let finished := (frame.finishRowsRecord curve.field environment inverted).1
  let cleared := (frame.clearIdentityRecord (model := model) ⟨0, Nat.two_pow_pos window⟩ finished).1
  have coordinateValues := frame.coordinateLayersRecord_values curve environment before point
    order prime large original tableFits loaded one curveValue baseValue
  have denominatorInputs := frame.finalDenominatorsRecord_originalInputs curve.field
    environment coordinates
  have batchInputs := frame.batchRecord_originalInputs curve.field (2 ^ window - 1)
    finalBatchFits environment denominators
  have invertedInputs : OriginalInputs frame before.1 inverted.1 :=
    OriginalInputs.trans frame before.1 denominators.1 inverted.1
      (OriginalInputs.trans frame before.1 coordinates.1 denominators.1
        coordinateValues.1 denominatorInputs) batchInputs
  have denominatorValues := frame.finalDenominatorsRecord_rowsValue curve environment
    coordinates point (2 ^ window) coordinateValues.2
  have invertedValues := frame.batchRecord_rowsValue curve (2 ^ window - 1) finalBatchFits
    environment denominators point (2 ^ window) denominatorValues
  have yRetained (row : Fin (2 ^ window)) :
      inverted.1.read (rowRead frame.arrays.y row) =
        coordinates.1.read (rowRead frame.arrays.y row) :=
    (frame.batchRecord_read_array_row curve.field (2 ^ window - 1) finalBatchFits
      environment denominators frame.arrays.y row
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 1 (by decide))
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 3 1 (by decide))).trans
      (frame.finalDenominatorsRecord_read_array_row curve.field environment coordinates
        frame.arrays.y row
        (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 1 (by decide)))
  have inverses (row : Fin (2 ^ window)) (positive : 0 < row.val) :
      ((inverted.1.read (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) =
        (-((2 : ZMod curve.field.modulus) *
          (inverted.1.read (rowRead frame.arrays.y row)).toNat))⁻¹ := by
    have bounded : row.val - 1 < 2 ^ window - 1 := by have := row.isLt; omega
    let index : Fin (2 ^ window - 1) := ⟨row.val - 1, bounded⟩
    have same : nonzeroRow window index = row := Fin.ext (by
      dsimp only [nonzeroRow, index]
      omega)
    rw [yRetained, ← same]
    exact frame.finalInvertedRecord_inverse curve environment coordinates point order prime large
      original tableFits (coordinateValues.1.modulus.trans loaded)
      (by rw [coordinateValues.1.inputs frame.zero (by simp)]; exact zero)
      (by rw [coordinateValues.1.inputs frame.one (by simp)]; exact one)
      coordinateValues.2 index
  have finishValues := frame.finishRowsRecord_values curve environment inverted point order
    prime large original tableFits (invertedInputs.modulus.trans loaded)
    (by rw [invertedInputs.inputs frame.zero (by simp)]; exact zero)
    (by rw [invertedInputs.inputs frame.one (by simp)]; exact one)
    (by rw [invertedInputs.inputs frame.curveA (by simp)]; exact curveValue)
    invertedValues inverses
  have finishInputs := OriginalInputs.trans frame before.1 inverted.1 finished.1
    invertedInputs finishValues.1
  have clearInputs := frame.clearIdentityRecord_originalInputs ⟨0, Nat.two_pow_pos window⟩
    finished
  change OriginalInputs frame before.1 cleared.1 ∧ TableValue curve frame point cleared.1
  refine ⟨OriginalInputs.trans frame before.1 finished.1 cleared.1 finishInputs clearInputs, ?_⟩
  intro row column
  by_cases identity : row.val = 0
  · have same : row = ⟨0, Nat.two_pow_pos window⟩ := Fin.ext identity
    subst row
    have actual := frame.clearIdentityRecord_values ⟨0, Nat.two_pow_pos window⟩ finished column
    have zeroValue : finished.1.read frame.zero = pointFiveWords curve (0 • point) column := by
      have numbers : (finished.1.read frame.zero).toNat =
          (pointFiveWords curve (0 • point) column).toNat := by
        rw [pointFiveWords_toNat]
        simpa only [zero_nsmul, pointFiveColumns, ZMod.val_zero] using
          (congrArg CShape.Value.toNat (finishInputs.inputs frame.zero (by simp))).trans zero
      exact unsignedWord_toNat_injective numbers
    exact actual.trans zeroValue
  · have positive : 0 < row.val := Nat.pos_of_ne_zero identity
    have different : row ≠ ⟨0, Nat.two_pow_pos window⟩ := by
      intro same
      have values : row.val = 0 :=
        congrArg (fun selected : Fin (2 ^ window) => selected.val) same
      exact identity values
    exact (frame.clearIdentityRecord_read_other_row ⟨0, Nat.two_pow_pos window⟩ finished
      (frame.finishColumns column) row different).trans (finishValues.2 row positive column)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
