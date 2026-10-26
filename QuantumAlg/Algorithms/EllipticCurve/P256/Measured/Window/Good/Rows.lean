/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prefix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Index
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Input

/-!
# Chronological table-row value from the paired base families

The two certified row families in one returned Store determine the exact
chronological point value requested by the P-256 window driver. This lemma
does not construct the Store or assert that signed-row preparation has run.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalRoutines.EllipticCurve.WindowTables

/-- Row equality transports only the two Store word reads. -/
private lemma paired_row_read_eq {ctx : RuntimeCtx .quantum}
    (frame : Outer.Frame ctx 256) (returned : Store ctx)
    {fromRow toRow : Fin 34} (same : fromRow = toRow) :
    returned.read (rowRead frame.coordinates.x fromRow) =
        returned.read (rowRead frame.coordinates.x toRow) ∧
      returned.read (rowRead frame.coordinates.y fromRow) =
        returned.read (rowRead frame.coordinates.y toRow) := by
  cases same
  exact ⟨rfl, rfl⟩

/-- Transport one canonical word bound along an equality of Store reads. -/
private lemma canonical_of_word_eq {width : Nat}
    (spec : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    {left right : CShape.Word width} (same : left = right)
    (canonical : right.toNat < spec.field.modulus) :
    left.toNat < spec.field.modulus := by
  cases same
  exact canonical

/-- Transport only the two coordinate arguments of nonsingularity. -/
private lemma finite_of_word_eq {width : Nat}
    (spec : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    {leftX leftY rightX rightY : CShape.Word width}
    (sameX : leftX = rightX) (sameY : leftY = rightY)
    (finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular
      (rightX.toNat : ZMod spec.field.modulus)
      (rightY.toNat : ZMod spec.field.modulus)) :
    spec.curve.toWeierstrassCurve.toAffine.Nonsingular
      (leftX.toNat : ZMod spec.field.modulus)
      (leftY.toNat : ZMod spec.field.modulus) := by
  cases sameX
  cases sameY
  exact finite

/-- Transport the complete dependent point-value proof together with its finite witness. -/
private lemma coordinateValue_transport {width : Nat}
    (spec : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    {leftX leftY rightX rightY : CShape.Word width}
    {leftPoint rightPoint : ClassicalAlgorithms.EllipticCurve.Point spec}
    (sameX : leftX = rightX) (sameY : leftY = rightY)
    (samePoint : leftPoint = rightPoint)
    (value : CoordinateValue spec rightX rightY rightPoint) :
    CoordinateValue spec leftX leftY leftPoint := by
  cases sameX
  cases sameY
  cases samePoint
  exact value

/-- Apply the certified first family before entering the combined 34-row goal. -/
private lemma first_family_value_rev
    {ctx : RuntimeCtx .quantum} (I : DomainParameters.PublicKeyInstance)
    (frame : Outer.Frame ctx 256) (returned : Store ctx) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (firstBaseRows row)))
      (returned.read (rowRead frame.coordinates.y (firstBaseRows row)))
      ((2 ^ (16 * row.val)) •
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib)) →
    ∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (firstBaseRows row.rev)))
      (returned.read (rowRead frame.coordinates.y (firstBaseRows row.rev)))
      ((2 ^ (16 * row.rev.val)) •
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  intro firstRows row
  exact firstRows row.rev

/-- Apply the certified second family before entering the combined 34-row goal. -/
private lemma second_family_value_rev
    {ctx : RuntimeCtx .quantum} (I : DomainParameters.PublicKeyInstance)
    (frame : Outer.Frame ctx 256) (returned : Store ctx) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (secondBaseRows row)))
      (returned.read (rowRead frame.coordinates.y (secondBaseRows row)))
      ((2 ^ (16 * row.val)) • (-I.publicKey.toMathlib))) →
    ∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (secondBaseRows row.rev)))
      (returned.read (rowRead frame.coordinates.y (secondBaseRows row.rev)))
      ((2 ^ (16 * row.rev.val)) • (-I.publicKey.toMathlib)) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  intro secondRows row
  exact secondRows row.rev

/-- The first certified family supplies the chronological first half. -/
private lemma first_branch_value
    {ctx : RuntimeCtx .quantum} (I : DomainParameters.PublicKeyInstance)
    (frame : Outer.Frame ctx 256) (returned : Store ctx) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (∀ index : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (firstBaseRows index)))
      (returned.read (rowRead frame.coordinates.y (firstBaseRows index)))
      ((2 ^ (16 * index.val)) •
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib)) →
    ∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x
        (Sampling.chronologicalIndex (row.castAdd 17)).row))
      (returned.read (rowRead frame.coordinates.y
        (Sampling.chronologicalIndex (row.castAdd 17)).row))
      (chronologicalBasePoint I (row.castAdd 17)) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  intro firstRows row
  have sameRow : (Sampling.chronologicalIndex (row.castAdd 17)).row =
      firstBaseRows row.rev := by
    rw [Sampling.chronologicalIndex_row,
      Nat.FixedWidth.Window.Chronology.paired_first]
    rfl
  obtain ⟨sameX, sameY⟩ := paired_row_read_eq frame returned sameRow
  let value := first_family_value_rev I frame returned firstRows row
  have samePoint : chronologicalBasePoint I (row.castAdd 17) =
      ((2 ^ (16 * row.rev.val)) •
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib) := by
    simp only [chronologicalBasePoint, Fin.addCases_left]
  exact coordinateValue_transport (actualCurveSpec I) sameX sameY samePoint value


/-- The second certified family supplies the chronological second half. -/
private lemma second_branch_value
    {ctx : RuntimeCtx .quantum} (I : DomainParameters.PublicKeyInstance)
    (frame : Outer.Frame ctx 256) (returned : Store ctx) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (∀ index : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (secondBaseRows index)))
      (returned.read (rowRead frame.coordinates.y (secondBaseRows index)))
      ((2 ^ (16 * index.val)) •
        (-I.publicKey.toMathlib))) →
    ∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x
        (Sampling.chronologicalIndex (row.natAdd 17)).row))
      (returned.read (rowRead frame.coordinates.y
        (Sampling.chronologicalIndex (row.natAdd 17)).row))
      (chronologicalBasePoint I (row.natAdd 17)) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  intro secondRows row
  have sameRow : (Sampling.chronologicalIndex (row.natAdd 17)).row =
      secondBaseRows row.rev := by
    rw [Sampling.chronologicalIndex_row,
      Nat.FixedWidth.Window.Chronology.paired_second]
    rfl
  obtain ⟨sameX, sameY⟩ := paired_row_read_eq frame returned sameRow
  let value := second_family_value_rev I frame returned secondRows row
  have samePoint : chronologicalBasePoint I (row.natAdd 17) =
      ((2 ^ (16 * row.rev.val)) •
        (-I.publicKey.toMathlib)) := by
    simp only [chronologicalBasePoint, Fin.addCases_right]
  exact coordinateValue_transport (actualCurveSpec I) sameX sameY samePoint value


/-- The two already certified seventeen-row families in one returned Store
give the chronological physical row's exact point value. -/
lemma chronologicalBasePoint_coordinateValue_of_paired_rows
    {ctx : RuntimeCtx .quantum} (I : DomainParameters.PublicKeyInstance)
    (frame : Outer.Frame ctx 256) (returned : Store ctx) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (firstBaseRows row)))
      (returned.read (rowRead frame.coordinates.y (firstBaseRows row)))
      ((2 ^ (16 * row.val)) •
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib)) →
    (∀ row : Fin 17, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x (secondBaseRows row)))
      (returned.read (rowRead frame.coordinates.y (secondBaseRows row)))
      ((2 ^ (16 * row.val)) • (-I.publicKey.toMathlib))) →
    ∀ position : Fin 34, CoordinateValue (actualCurveSpec I)
      (returned.read (rowRead frame.coordinates.x
        (Sampling.chronologicalIndex position).row))
      (returned.read (rowRead frame.coordinates.y
        (Sampling.chronologicalIndex position).row))
      (chronologicalBasePoint I position) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  intro firstRows secondRows position
  refine Fin.addCases (m := 17) (n := 17) (fun row => ?_) (fun row => ?_) position
  · exact first_branch_value I frame returned firstRows row
  · exact second_branch_value I frame returned secondRows row

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
