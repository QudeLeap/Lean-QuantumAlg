/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Final.Preservation

/-!
# Every actual final C word is its original negative-tangent denominator

Each complete chronological row reads its real predecessor, computes the
paid doubling and subtraction, and overwrites that same C row. The full
traversal retains the original y words and protected zero input, so every
visited result has the original mathematical value before the paid batch.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The original positive-address enumeration is injective without modular truncation. -/
lemma nonzeroRow_injective (window : Nat) : Function.Injective (nonzeroRow window) := by
  intro first second same
  apply Fin.ext
  have values := congrArg (fun row : Fin (2 ^ window) => row.val) same
  dsimp only [nonzeroRow] at values
  omega

/-- Every final denominator is the actual original y value multiplied by negative two. -/
lemma finalDenominatorsRecord_read_result (spec : ModulusSpec width)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord)
    (zero : (before.1.read frame.zero).toNat = 0)
    (index : Fin (2 ^ window - 1)) :
    (((frame.finalDenominatorsRecord spec environment before).1.1.read
        (rowRead frame.arrays.c (nonzeroRow window index))).toNat : ZMod spec.modulus) =
      -((2 : ZMod spec.modulus) *
        (before.1.read (rowRead frame.arrays.y (nonzeroRow window index))).toNat) := by
  let invariant := fun processed (current : Store ctx × model.HiddenState) =>
    OriginalInputs frame before.1 current.1 ∧
      (∀ row, current.1.read (rowRead frame.arrays.y row) =
        before.1.read (rowRead frame.arrays.y row)) ∧
      ∀ queried : Fin (2 ^ window - 1), queried.val < processed →
        ((current.1.read (rowRead frame.arrays.c (nonzeroRow window queried))).toNat :
          ZMod spec.modulus) = -((2 : ZMod spec.modulus) *
            (before.1.read (rowRead frame.arrays.y (nonzeroRow window queried))).toNat)
  have completed := Circuit.forRangeRecord_invariant (2 ^ window - 1)
    (fun selected => frame.tangentDenominatorRow (nonzeroRow window selected))
    (fun selected => frame.tangentRecord spec (nonzeroRow window selected) environment)
    invariant (fun selected current established => by
      refine ⟨OriginalInputs.trans frame before.1 current.1 _ established.1
        (frame.tangentRecord_originalInputs spec (nonzeroRow window selected)
          environment current), ?_, ?_⟩
      · intro row
        exact (frame.tangentRecord_read_array_row spec (nonzeroRow window selected)
          environment current frame.arrays.y row
          (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 1 (by decide))).trans
            (established.2.1 row)
      · intro queried visited
        by_cases same : queried = selected
        · subst queried
          rw [frame.tangentRecord_store]
          have currentZero : (current.1.read frame.zero).toNat = 0 := by
            rw [established.1.inputs frame.zero (by simp)]
            exact zero
          have actual := frame.tangentStore_result_cast spec (nonzeroRow window selected)
            current.1 (established.1.modulus.trans loaded) currentZero
          rw [established.2.1] at actual
          exact actual
        · rw [frame.tangentRecord_read_other_row spec (nonzeroRow window selected)
            environment current frame.arrays.c (nonzeroRow window queried)
            (fun equal => same (nonzeroRow_injective window equal))]
          exact established.2.2 queried (by
            have unequal : queried.val ≠ selected.val := fun equal => same (Fin.ext equal)
            omega)) before ⟨OriginalInputs.refl frame before.1, fun _ => rfl,
              fun _ impossible => by omega⟩
  exact completed.2.2 index index.isLt

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
