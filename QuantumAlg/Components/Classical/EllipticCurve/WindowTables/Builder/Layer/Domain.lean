/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Point

/-!
# Original nonexceptional domain of every binary-layer addition

The real old row is positive and below its power-of-two seed. Their sum
is the original new-row address, strictly below the complete table size.
An original base point whose order exceeds that size therefore gives
separate affine x coordinates and a nonzero actual secant denominator.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {width window : Nat} {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Every original old-row address is positive and strictly below its current seed. -/
lemma layer_old_positive_below_seed (level : Fin window) (index : Fin (layerCount level)) :
    0 < (oldRow level index).val ∧
      (oldRow level index).val < (layerSeed window level).val := by
  have bounded := index.isLt
  have positive := Nat.two_pow_pos level.val
  dsimp only [oldRow, layerSeed, layerCount] at *
  omega

/-- Every literal new-row scalar sum is below the original base-point order. -/
lemma layer_scalar_sum_below_order (level : Fin window) (index : Fin (layerCount level))
    (order : Nat) (large : 2 ^ window < order) :
    (layerSeed window level).val + (oldRow level index).val < order := by
  have bounded := (newRow level index).isLt
  dsimp only [newRow, layerSeed, oldRow] at *
  omega

/-- The two original canonical coordinate rows in each actual layer have different affine x. -/
lemma layer_coordinate_x_ne (curve : CurveSpec width)
    (frame : TableFrame ctx width (2 ^ window)) (level : Fin window)
    (index : Fin (layerCount level)) (store : Store ctx) (point : Point curve)
    (large : 2 ^ window < addOrderOf point)
    (seed : CoordinateValue curve
      (store.read (rowRead frame.arrays.x (layerSeed window level)))
      (store.read (rowRead frame.arrays.y (layerSeed window level)))
      ((layerSeed window level).val • point))
    (old : CoordinateValue curve (store.read (rowRead frame.arrays.x (oldRow level index)))
      (store.read (rowRead frame.arrays.y (oldRow level index)))
      ((oldRow level index).val • point)) :
    ((store.read (rowRead frame.arrays.x (layerSeed window level))).toNat :
      ZMod curve.field.modulus) ≠
      (store.read (rowRead frame.arrays.x (oldRow level index))).toNat :=
  scalar_finite_x_ne curve point _ _ (layer_old_positive_below_seed level index).1
    (layer_old_positive_below_seed level index).2
    (layer_scalar_sum_below_order level index (addOrderOf point) large)
    _ _ _ _ seed.finite old.finite seed.represents old.represents

/-- The real destination index represents exactly the old-row point plus its current seed. -/
lemma layer_scalar_sum {G : Type*} [AddCommMonoid G] (point : G) (level : Fin window)
    (index : Fin (layerCount level)) :
    (oldRow level index).val • point + (layerSeed window level).val • point =
      (newRow level index).val • point := by
  change (index.val + 1) • point + (2 ^ level.val) • point =
    (2 ^ level.val + (index.val + 1)) • point
  exact (add_comm _ _).trans (add_nsmul point (2 ^ level.val) (index.val + 1)).symm

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
