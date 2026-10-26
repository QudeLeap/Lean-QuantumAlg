/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Blocks

/-!
# Exact secant slope word from the actual preceding inverse row

The original subtraction reads both actual y coordinates. The next paid
multiply consumes that result and the same original C row, before either
coordinate destination is changed. Old working words remain unrestricted.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- The real first two slots give the original finite-word secant slope. -/
lemma extendFirstStore_read_slope (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.extendFirstStore spec seed row store).read (wordRead frame.work.slope) =
      multiplyValue (subValue (store.read (rowRead frame.arrays.y seed))
        (store.read (rowRead frame.arrays.y row)) (.unsignedWord spec.extendedWord))
        (store.read (rowRead frame.arrays.c row)) (.unsignedWord spec.extendedWord) := by
  let first := store.write frame.work.temporary
    (subValue (store.read (rowRead frame.arrays.y seed))
      (store.read (rowRead frame.arrays.y row)) (store.read (wordRead frame.modulus)))
  have firstTemporary : first.read (wordRead frame.work.temporary) =
      subValue (store.read (rowRead frame.arrays.y seed))
        (store.read (rowRead frame.arrays.y row)) (store.read (wordRead frame.modulus)) :=
    Store.read_write_same _ _ _
  have firstC : first.read (rowRead frame.arrays.c row) =
      store.read (rowRead frame.arrays.c row) := wordWrite_read_row _ _ _ store _
  have firstModulus : first.read (wordRead frame.modulus) =
      store.read (wordRead frame.modulus) := wordWrite_read_modulus _ _ store _
  change (first.write frame.work.slope
    (multiplyValue (first.read (wordRead frame.work.temporary))
      (first.read (rowRead frame.arrays.c row))
      (first.read (wordRead frame.modulus)))).read (wordRead frame.work.slope) = _
  rw [wordWrite_read_same, firstTemporary, firstC, firstModulus, loaded]

/-- Every structural read outside the two actual secant-prefix outputs survives unchanged. -/
lemma extendFirstStore_read_other (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (slopeFree : frame.work.slope.key ∉ observed.storageKeys) :
    (frame.extendFirstStore spec seed row store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> first | exact temporaryFree | exact slopeFree

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
