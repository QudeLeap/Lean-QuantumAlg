/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Seed.Values

/-!
# Canonical group values of the original growing coordinate rows

Only positive rows below the stated natural bound are constrained. The
identity row and all old working words remain unrestricted. The actual
seed record extends this invariant by its original two copies or paid
doubling while retaining every previously constructed row.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Actual positive coordinate rows below a natural construction frontier
represent their indices. -/
def CoordinateRowsValue (curve : CurveSpec width) (point : Point curve) (bound : Nat)
    (store : Store ctx) : Prop :=
  ∀ row : Fin length, 0 < row.val → row.val < bound →
    CoordinateValue curve (store.read (rowRead frame.arrays.x row))
      (store.read (rowRead frame.arrays.y row)) (row.val • point)

/-- Before the first real layer there is no positive row below the initial frontier. -/
lemma coordinateRowsValue_initial (curve : CurveSpec width) (point : Point curve)
    (store : Store ctx) : frame.CoordinateRowsValue curve point 1 store := by
  intro row positive below
  omega

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The actual original seed branch adds its own row to all previously constructed coordinates. -/
lemma prepareSeedRecord_rowsValue (curve : CurveSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (baseValue : CoordinateValue curve (before.1.read frame.baseX)
      (before.1.read frame.baseY) point)
    (rows : frame.CoordinateRowsValue curve point (2 ^ level.val) before.1) :
    frame.CoordinateRowsValue curve point (2 ^ level.val + 1)
      (frame.prepareSeedRecord curve.field level environment before).1.1 := by
  have seedValue := frame.prepareSeedRecord_coordinateValue curve level environment before point
    order prime large original loaded curveValue baseValue (fun later => by
      apply rows
      · exact Nat.two_pow_pos _
      · change 2 ^ (level.val - 1) < 2 ^ level.val
        exact Nat.pow_lt_pow_right (by decide) (by omega))
  intro row positive below
  by_cases same : row = layerSeed window level
  · subst row
    exact seedValue
  · rw [frame.prepareSeedRecord_read_other_row curve.field level environment before
      frame.arrays.x row same,
      frame.prepareSeedRecord_read_other_row curve.field level environment before
        frame.arrays.y row same]
    apply rows row positive
    have different : row.val ≠ 2 ^ level.val := fun equal => same (Fin.ext equal)
    omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
