/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Finite
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Residue

/-!
# One actual selected affine point supplies all five original columns

The original active full digit and base-point order provide the finite
point internally. Its actual group value determines every selected table
column at once. Values retain the existing natural-value cast into the
physical field, without adding a modulus-transport or arithmetic premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Tables

noncomputable section

open ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve.WindowTables

attribute [local irreducible] modulus

/-- The same enabled original scalar point supplies one affine witness and all five columns. -/
lemma selectedAffinePoint_columns (curve : CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Window.Raw) (order : Nat)
    (original : addOrderOf point = order) (tableFits : 2 ^ (width + 1) < order)
    (active : Window.QueryInsertion.querySelected stream width bounded false state = true) :
    ∃ selected : AffinePoint curve.curve,
      selected.toMathlib = (Window.Tables.selectedRow stream width bounded state).val • point ∧
        ∀ column : Fin 5,
          Window.Tables.selectedFieldColumn curve point stream width bounded state column =
            ((fiveColumns curve selected.x selected.y column).val : ZMod modulus) := by
  obtain ⟨x, y, finite, same⟩ := Window.Tables.selectedPoint_finite curve point
    stream width bounded state order original tableFits active
  refine ⟨⟨x, y, finite⟩, same.symm, ?_⟩
  intro column
  change ((pointFiveColumns curve
    ((Window.Tables.selectedRow stream width bounded state).val • point) column).val :
      ZMod modulus) = ((fiveColumns curve x y column).val : ZMod modulus)
  exact congrArg (fun actual : ClassicalAlgorithms.EllipticCurve.Point curve =>
    ((pointFiveColumns curve actual column).val : ZMod modulus)) same

end

end Tables

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
