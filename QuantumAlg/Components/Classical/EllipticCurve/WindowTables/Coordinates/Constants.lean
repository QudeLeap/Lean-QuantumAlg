/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Store

/-!
# Exact actual modulus and curve-input preservation through doubling

The real widened modulus cannot alias any narrower scalar or coordinate
array. The supplied curve coefficient is protected from all six physical
outputs by the original frame. These same read values persist through
the complete actual doubling record, including in-place destination writes.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The actual original widened modulus survives every original doubling slot. -/
lemma doubleStore_read_modulus (spec : ModulusSpec width) (source destination : Fin length)
    (store : Store ctx) :
    (frame.doubleStore spec source destination store).read (wordRead frame.modulus) =
      store.read (wordRead frame.modulus) := by
  apply frame.doubleStore_read_other
  · change frame.x.key ∉ [frame.modulus.key]
    simpa only [List.mem_singleton] using Ne.symm (modulus_array_key_ne frame.modulus frame.x)
  · change frame.y.key ∉ [frame.modulus.key]
    simpa only [List.mem_singleton] using Ne.symm (modulus_array_key_ne frame.modulus frame.y)
  all_goals exact frame.scalar_modulus_free _

/-- The actual protected curve-coefficient input survives all original six-output updates. -/
lemma doubleStore_read_curveA (spec : ModulusSpec width) (source destination : Fin length)
    (store : Store ctx) :
    (frame.doubleStore spec source destination store).read frame.curveA =
      store.read frame.curveA := by
  apply frame.doubleStore_read_other
  all_goals exact frame.protectedCoefficient _ (by simp)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : CoordinateFrame ctx width length)

/-- The complete real chronological record retains exactly that same original stored modulus. -/
lemma doubleRecord_read_modulus (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.doubleRecord spec source destination environment before).1.1.read
      (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) := by
  rw [frame.doubleRecord_store]
  exact frame.doubleStore_read_modulus spec source destination before.1

/-- The complete real chronological record retains exactly that same protected curve input. -/
lemma doubleRecord_read_curveA (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.doubleRecord spec source destination environment before).1.1.read frame.curveA =
      before.1.read frame.curveA := by
  rw [frame.doubleRecord_store]
  exact frame.doubleStore_read_curveA spec source destination before.1

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
