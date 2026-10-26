/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Seed
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Seed
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Order
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Preservation

/-!
# Exact original power-of-two value of every actual layer seed

At level zero the two actual copies give the original base point. Later
levels consume the preceding actual seed and apply the original paid
doubling. The same odd prime order proves every required nonvertical
domain. All other physical rows retain their original coordinate words.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The original actual public-level conditional returns exactly its power-of-two group point. -/
lemma prepareSeedRecord_coordinateValue (curve : CurveSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (baseValue : CoordinateValue curve (before.1.read frame.baseX)
      (before.1.read frame.baseY) point)
    (previous : level.val ≠ 0 → CoordinateValue curve
      (before.1.read (rowRead frame.arrays.x (previousSeed window level)))
      (before.1.read (rowRead frame.arrays.y (previousSeed window level)))
      ((2 ^ (level.val - 1)) • point)) :
    let returned := (frame.prepareSeedRecord curve.field level environment before).1.1
    CoordinateValue curve (returned.read (rowRead frame.arrays.x (layerSeed window level)))
      (returned.read (rowRead frame.arrays.y (layerSeed window level)))
      ((2 ^ level.val) • point) := by
  dsimp only
  by_cases initial : level.val = 0
  · rw [frame.prepareSeedRecord_initial_state curve.field level environment before initial]
    have actual := frame.coordinates.seedRecord_coordinateValue curve frame.baseX frame.baseY
      (layerSeed window level) before point
      (frame.protectedReads frame.baseY (by simp) frame.arrays.x.key (by simp)) baseValue
    rw [show frame.coordinates.x = frame.arrays.x from rfl,
      show frame.coordinates.y = frame.arrays.y from rfl] at actual
    simpa only [initial, pow_zero, one_nsmul] using actual
  · rw [frame.prepareSeedRecord_later_state curve.field level environment before initial]
    have actual := frame.coordinates.doubleRecord_coordinateValue curve
      (previousSeed window level) (layerSeed window level) environment before
      ((2 ^ (level.val - 1)) • point) loaded curveValue (previous initial)
      (pow_two_nsmul_double_ne_zero point order (level.val - 1) prime large original)
    have exponent : level.val - 1 + 1 = level.val := by omega
    have scalar : (2 ^ (level.val - 1)) • point + (2 ^ (level.val - 1)) • point =
        (2 ^ level.val) • point := by
      rw [← two_nsmul, ← mul_nsmul, ← pow_succ, exponent]
    rw [show frame.coordinates.x = frame.arrays.x from rfl,
      show frame.coordinates.y = frame.arrays.y from rfl, scalar] at actual
    exact actual

/-- Every unvisited array row survives either branch of the actual original seed preparation. -/
lemma prepareSeedRecord_read_other_row (spec : ModulusSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector (2 ^ window) (.unsignedWord width)))
    (row : Fin (2 ^ window)) (different : row ≠ layerSeed window level) :
    (frame.prepareSeedRecord spec level environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  by_cases initial : level.val = 0
  · rw [frame.prepareSeedRecord_initial_state spec level environment before initial]
    exact frame.coordinates.seedRecord_read_other_row frame.baseX frame.baseY
      (layerSeed window level) before array row different
  · rw [frame.prepareSeedRecord_later_state spec level environment before initial]
    exact frame.coordinates.doubleRecord_read_other_row spec (previousSeed window level)
      (layerSeed window level) environment before array row different

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
