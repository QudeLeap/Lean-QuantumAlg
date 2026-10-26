/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Final.Inversion
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Preservation

/-!
# Canonical group-table words in the actual final conversion traversal

Every real row consumes its preceding actual Store. Unvisited rows keep
their original coordinates and real inverse words, while finished rows
keep all five canonical requested values. Only the four original scalar
working words are used by the unchanged native programs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The original finish traversal writes every positive original address's five requested words. -/
lemma finishRowsRecord_values (curve : CurveSpec width) (environment : model.Environment)
    (before : Store ctx × model.HiddenState) (point : Point curve) (order : Nat)
    (prime : order.Prime) (large : 3 < order) (original : addOrderOf point = order)
    (tableFits : 2 ^ window < order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (zero : (before.1.read frame.zero).toNat = 0)
    (one : (before.1.read frame.one).toNat = 1)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (rows : frame.CoordinateRowsValue curve point (2 ^ window) before.1)
    (inverses : ∀ row : Fin (2 ^ window), 0 < row.val →
      ((before.1.read (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) =
        (-((2 : ZMod curve.field.modulus) *
          (before.1.read (rowRead frame.arrays.y row)).toNat))⁻¹) :
    let returned := (frame.finishRowsRecord curve.field environment before).1.1
    OriginalInputs frame before.1 returned ∧
      ∀ row : Fin (2 ^ window), 0 < row.val → ∀ column : Fin 5,
        returned.read (rowRead (frame.finishColumns column) row) =
          pointFiveWords curve (row.val • point) column := by
  let invariant := fun processed (current : Store ctx × model.HiddenState) =>
    OriginalInputs frame before.1 current.1 ∧
      (∀ queried : Fin (2 ^ window - 1), processed ≤ queried.val → ∀ column : Fin 5,
        current.1.read (rowRead (frame.finishColumns column) (nonzeroRow window queried)) =
          before.1.read (rowRead (frame.finishColumns column) (nonzeroRow window queried))) ∧
      ∀ queried : Fin (2 ^ window - 1), queried.val < processed → ∀ column : Fin 5,
        current.1.read (rowRead (frame.finishColumns column) (nonzeroRow window queried)) =
          pointFiveWords curve ((nonzeroRow window queried).val • point) column
  have completed := Circuit.forRangeRecord_invariant (2 ^ window - 1)
    (fun selected => frame.finishRow (nonzeroRow window selected))
    (fun selected => frame.finishRecord curve.field (nonzeroRow window selected) environment)
    invariant (fun selected current established => by
      have xRead : current.1.read (rowRead frame.arrays.x (nonzeroRow window selected)) =
          before.1.read (rowRead frame.arrays.x (nonzeroRow window selected)) :=
        established.2.1 selected (Nat.le_refl _) 0
      have yRead : current.1.read (rowRead frame.arrays.y (nonzeroRow window selected)) =
          before.1.read (rowRead frame.arrays.y (nonzeroRow window selected)) :=
        established.2.1 selected (Nat.le_refl _) 1
      have cRead : current.1.read (rowRead frame.arrays.c (nonzeroRow window selected)) =
          before.1.read (rowRead frame.arrays.c (nonzeroRow window selected)) :=
        established.2.1 selected (Nat.le_refl _) 2
      have positive : 0 < (nonzeroRow window selected).val := by
        change 0 < selected.val + 1
        omega
      have input : CoordinateValue curve
          (current.1.read (rowRead frame.arrays.x (nonzeroRow window selected)))
          (current.1.read (rowRead frame.arrays.y (nonzeroRow window selected)))
          ((nonzeroRow window selected).val • point) := by
        rw [xRead, yRead]
        exact rows _ positive (nonzeroRow window selected).isLt
      have selectedLarge : 3 < addOrderOf ((nonzeroRow window selected).val • point) := by
        rw [prime_order_nsmul point order _ prime original positive
          (lt_trans (nonzeroRow window selected).isLt tableFits)]
        exact large
      have currentInverse :
          ((current.1.read (rowRead frame.arrays.c (nonzeroRow window selected))).toNat :
            ZMod curve.field.modulus) =
          (-((2 : ZMod curve.field.modulus) *
            (current.1.read (rowRead frame.arrays.y (nonzeroRow window selected))).toNat))⁻¹ := by
        rw [cRead, yRead]
        exact inverses _ positive
      have value := frame.finishRecord_rowValue curve (nonzeroRow window selected)
        environment current ((nonzeroRow window selected).val • point)
        (established.1.modulus.trans loaded)
        (by rw [established.1.inputs frame.zero (by simp)]; exact zero)
        (by rw [established.1.inputs frame.one (by simp)]; exact one)
        (by rw [established.1.inputs frame.curveA (by simp)]; exact curveValue)
        input selectedLarge currentInverse
      have wordValue (column : Fin 5) :
          (frame.finishRecord curve.field (nonzeroRow window selected) environment current).1.1.read
              (rowRead (frame.finishColumns column) (nonzeroRow window selected)) =
            pointFiveWords curve ((nonzeroRow window selected).val • point) column :=
        FinishedRowValue.words curve frame (nonzeroRow window selected) _ _ _ _ input value column
      refine ⟨OriginalInputs.trans frame before.1 current.1 _ established.1
        (frame.finishRecord_originalInputs curve.field (nonzeroRow window selected)
          environment current), ?_, ?_⟩
      · intro queried remaining column
        have different : nonzeroRow window queried ≠ nonzeroRow window selected := by
          intro same
          have equal := nonzeroRow_injective window same
          have equalValues := congrArg
            (fun index : Fin (2 ^ window - 1) => index.val) equal
          omega
        rw [frame.finishRecord_read_other_row curve.field (nonzeroRow window selected)
          environment current (frame.finishColumns column) (nonzeroRow window queried) different]
        exact established.2.1 queried (by omega) column
      · intro queried visited column
        by_cases same : queried = selected
        · subst queried
          exact wordValue column
        · rw [frame.finishRecord_read_other_row curve.field (nonzeroRow window selected)
            environment current (frame.finishColumns column) (nonzeroRow window queried)
            (fun equal => same (nonzeroRow_injective window equal))]
          exact established.2.2 queried (by
            have unequal : queried.val ≠ selected.val := fun equal => same (Fin.ext equal)
            omega) column) before ⟨OriginalInputs.refl frame before.1,
              fun _ _ _ => rfl, fun _ impossible => by omega⟩
  refine ⟨completed.1, ?_⟩
  intro row positive column
  have bounded : row.val - 1 < 2 ^ window - 1 := by have := row.isLt; omega
  let queried : Fin (2 ^ window - 1) := ⟨row.val - 1, bounded⟩
  have same : nonzeroRow window queried = row := Fin.ext (by
    dsimp only [nonzeroRow, queried]
    omega)
  rw [← same]
  exact completed.2.2 queried queried.isLt column

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
