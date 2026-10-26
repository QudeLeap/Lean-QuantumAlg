/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Tables.Point
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field.Columns.Transport

/-!
# Actual selected table columns on the same transported curve and point

The original active row still supplies its same affine point and exact
scalar identity. Only the existing modulus equality is used to identify
its five actual field columns with the same transported point's tuple.
Identity row zero remains in the original inactive sector.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Tables

noncomputable section

open ClassicalAlgorithms.EllipticCurve

attribute [local irreducible] modulus

/-- The same original selected point and scalar identity give all five target-field columns. -/
lemma selectedAffinePoint_fieldColumns (curve : CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Window.Raw) (order : Nat)
    (original : addOrderOf point = order) (tableFits : 2 ^ (width + 1) < order)
    (active : Window.QueryInsertion.querySelected stream width bounded false state = true) :
    ∃ selected : AffinePoint curve.curve,
      selected.toMathlib = (Window.Tables.selectedRow stream width bounded state).val • point ∧
        let targetCurve := MeasuredPointAddition.curveAtModulus curve sameModulus
        let targetPoint := MeasuredPointAddition.affineAtModulus curve sameModulus selected
        letI : Fact modulus.Prime := ⟨targetCurve.prime⟩
        ∀ column : Fin 5,
          Window.Tables.selectedFieldColumn curve point stream width bounded state column =
            ![-targetPoint.x, -targetPoint.y, 3 * targetPoint.x,
              -MeasuredPointAddition.exceptionalSlope targetCurve targetPoint,
              targetPoint.x + 1] column := by
  obtain ⟨selected, represents, columns⟩ := selectedAffinePoint_columns curve point
    stream width bounded state order original tableFits active
  refine ⟨selected, represents, ?_⟩
  dsimp only
  intro column
  exact (columns column).trans
    (MeasuredPointAddition.fiveColumns_cast_modulus curve modulus sameModulus selected column)

end

end Tables

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
