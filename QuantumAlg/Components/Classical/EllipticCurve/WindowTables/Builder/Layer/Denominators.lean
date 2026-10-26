/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Denominator.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Actual original secant words throughout a binary denominator pass

The chronological pass preserves every x coordinate and the actual loaded
modulus. Each visited C row receives the seed x word minus its own earlier
x word, evaluated from that same incoming Store. No denominator is supplied
by a host callback or detached from the actual subtraction program.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- A structural read outside the two actual denominator outputs survives the entire pass. -/
lemma layerDenominatorsRecord_read_other (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (denominatorFree : frame.arrays.c.key ∉ observed.storageKeys) :
    (frame.layerDenominatorsRecord level environment before).1.1.read observed =
      before.1.read observed := by
  exact Circuit.forRangeRecord_invariant (layerCount level)
    (fun index => frame.denominatorRow (layerSeed window level) (oldRow level index))
    (fun index => Circuit.preserveHiddenRecord
      (frame.denominatorRecord (layerSeed window level) (oldRow level index) environment))
    (fun _ current => current.1.read observed = before.1.read observed)
    (fun index current established =>
      (frame.denominatorRecord_read_other (layerSeed window level) (oldRow level index)
        environment current.1 observed temporaryFree denominatorFree).trans established)
    before rfl

/-- Every original visited C word is exactly the subtraction of its original coordinate words. -/
lemma layerDenominatorsRecord_read_result (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (index : Fin (layerCount level)) :
    (frame.layerDenominatorsRecord level environment before).1.1.read
      (rowRead frame.arrays.c (oldRow level index)) =
      subValue (before.1.read (rowRead frame.arrays.x (layerSeed window level)))
        (before.1.read (rowRead frame.arrays.x (oldRow level index)))
        (before.1.read (wordRead frame.modulus)) := by
  let invariant := fun processed (current : Store ctx × model.HiddenState) =>
    current.1.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      (∀ row, current.1.read (rowRead frame.arrays.x row) =
        before.1.read (rowRead frame.arrays.x row)) ∧
      ∀ queried : Fin (layerCount level), queried.val < processed →
        current.1.read (rowRead frame.arrays.c (oldRow level queried)) =
          subValue (before.1.read (rowRead frame.arrays.x (layerSeed window level)))
            (before.1.read (rowRead frame.arrays.x (oldRow level queried)))
            (before.1.read (wordRead frame.modulus))
  have completed := Circuit.forRangeRecord_invariant (layerCount level)
    (fun selected => frame.denominatorRow (layerSeed window level) (oldRow level selected))
    (fun selected => Circuit.preserveHiddenRecord
      (frame.denominatorRecord (layerSeed window level) (oldRow level selected) environment))
    invariant (fun selected current established => by
      refine ⟨?_, ?_, ?_⟩
      · exact (frame.denominatorRecord_read_other (layerSeed window level) (oldRow level selected)
          environment current.1 (wordRead frame.modulus) (by
            change frame.work.temporary.key ∉ [frame.modulus.key]
            simpa only [List.mem_singleton] using
              Ne.symm (modulus_word_key_ne frame.modulus frame.work.temporary)) (by
            change frame.arrays.c.key ∉ [frame.modulus.key]
            simpa only [List.mem_singleton] using
              Ne.symm (modulus_array_key_ne frame.modulus frame.arrays.c))).trans established.1
      · intro row
        exact (frame.denominatorRecord_read_other (layerSeed window level) (oldRow level selected)
          environment current.1 (rowRead frame.arrays.x row) (by
            change frame.work.temporary.key ∉ [frame.arrays.x.key]
            simpa only [List.mem_singleton] using word_array_key_ne _ _) (by
            change frame.arrays.c.key ∉ [frame.arrays.x.key]
            simpa [Arrays.column] using frame.arrays.column_key_ne 2 0 (by decide))).trans
              (established.2.1 row)
      · intro queried visited
        by_cases same : queried = selected
        · subst queried
          change (frame.denominatorRecord (layerSeed window level) (oldRow level selected)
            environment current.1).1.read _ = _
          rw [frame.denominatorRecord_store, frame.denominatorStore_read_result,
            established.2.1, established.2.1, established.1]
        · have different : oldRow level queried ≠ oldRow level selected := by
            intro equal
            apply same
            have values := congrArg (fun row : Fin (2 ^ window) => row.val) equal
            apply Fin.ext
            dsimp only [oldRow] at values
            omega
          change (frame.denominatorRecord (layerSeed window level) (oldRow level selected)
            environment current.1).1.read _ = _
          rw [frame.denominatorRecord_read_other_row (layerSeed window level)
            (oldRow level selected) environment current.1 frame.arrays.c
            (oldRow level queried) different]
          exact established.2.2 queried (by
            have unequal : queried.val ≠ selected.val := fun equal => same (Fin.ext equal)
            omega)) before ⟨rfl, fun _ => rfl, fun _ impossible => by omega⟩
  exact completed.2.2 index index.isLt

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
