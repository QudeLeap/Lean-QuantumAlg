/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Framing
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Common.Cascade
import all QuantumAlg.Core.Execution.Context.Union.Unitary

/-!
# Four literal coordinate conversions on the same complete dirty arithmetic bank

The real runtime conversion matrix acts on the full original Numerator register. All
original exponents, the selector and arbitrary Reference are preserved by their exact
identity deltas. Both forward and both inverse conversion calls remain in their original
order around each real measured point path. No arithmetic input, Store, path, conversion
inverse law or old/new instrument equality is assumed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Converted

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement
open Recovery.Reference.Measured Recovery.Reference.Measured.CommonBank
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The actual full arithmetic conversion, with the selector and arbitrary Reference intact. -/
def bankCoordinateOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) : Matrix (Bank width Reference) (Bank width Reference) ℂ :=
  fun row column =>
    ((Encoding.runtimeProgram width modulus coefficient coordinate).matrix environment.quantum)
      row.1 column.1 *
      (if row.2.1 = column.2.1 then 1 else 0) *
      (if row.2.2 = column.2.2 then 1 else 0)

/-- Splitting the actual indexed basis loses no exponent or selector equality. -/
private lemma indexed_coordinates_equal (width count : Nat) (Reference : Register)
    (left right : Exponents count) (row column : Bank width Reference) :
    (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
      (indexedContext width (List.range (count + 1)) List.nodup_range)
      (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
      ((coordinates width count Reference).symm (left, row)).1).2 =
    (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
      (indexedContext width (List.range (count + 1)) List.nodup_range)
      (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
      ((coordinates width count Reference).symm (right, column)).1).2 ↔
        left = right ∧ row.2.1 = column.2.1 := by
  let indexed := (rangeBasis width (count + 1)).trans
    (Fin.snocEquiv (fun _ : Fin (count + 1) => Fin 2)).symm
  let physicalRow := (coordinates width count Reference).symm (left, row)
  let physicalColumn := (coordinates width count Reference).symm (right, column)
  let union := ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
  have mappedRow : indexed (union physicalRow.1).2 = (row.2.1, left) := by
    apply Prod.ext
    · change (coordinates width count Reference physicalRow).2.2.1 = row.2.1
      simp only [physicalRow, Equiv.apply_symm_apply]
    · change (coordinates width count Reference physicalRow).1 = left
      simp only [physicalRow, Equiv.apply_symm_apply]
  have mappedColumn : indexed (union physicalColumn.1).2 = (column.2.1, right) := by
    apply Prod.ext
    · change (coordinates width count Reference physicalColumn).2.2.1 = column.2.1
      simp only [physicalColumn, Equiv.apply_symm_apply]
    · change (coordinates width count Reference physicalColumn).1 = right
      simp only [physicalColumn, Equiv.apply_symm_apply]
  change (union physicalRow.1).2 = (union physicalColumn.1).2 ↔ _
  constructor
  · intro same
    have mapped := congrArg indexed same
    rw [mappedRow, mappedColumn] at mapped
    exact ⟨congrArg (fun pair : Fin 2 × Exponents count => pair.2) mapped,
      congrArg (fun pair : Fin 2 × Exponents count => pair.1) mapped⟩
  · rintro ⟨sameExponent, sameSelector⟩
    apply indexed.injective
    rw [mappedRow, mappedColumn, sameExponent, sameSelector]

/-- The indexed identity separates into its complete exponent and selector identities. -/
private lemma split_indexed_identity (whole exponent selector reference : Prop)
    {wholeDecision : Decidable whole} {exponentDecision : Decidable exponent}
    {selectorDecision : Decidable selector} {referenceDecision : Decidable reference}
    (coefficient : ℂ) (same : whole ↔ exponent ∧ selector) :
    coefficient * (@ite ℂ whole wholeDecision 1 0) *
        (@ite ℂ reference referenceDecision 1 0) =
      @ite ℂ exponent exponentDecision
        (coefficient * (@ite ℂ selector selectorDecision 1 0) *
          (@ite ℂ reference referenceDecision 1 0)) 0 := by
  by_cases he : exponent <;> by_cases hs : selector <;> simp_all

/-- Each real conversion preserves all exponent coherences on the same dirty bank. -/
lemma coordinateOperator_common_entry (width count : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ)
    (coordinate : MeasuredPointAddition.Coordinate) (Reference : Register)
    (left right : Exponents count) (row column : Bank width Reference) :
    (Encoding.coordinateOperator (environment := environment) width count modulus coefficient
      coordinate Reference :
        Matrix _ _ ℂ)
      ((coordinates width count Reference).symm (left, row))
      ((coordinates width count Reference).symm (right, column)) =
        if left = right then
          bankCoordinateOperator (environment := environment) width modulus coefficient coordinate
            Reference row column
        else 0 := by
  let physicalRow := (coordinates width count Reference).symm (left, row)
  let physicalColumn := (coordinates width count Reference).symm (right, column)
  let union := ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
  have rowArithmetic : (union physicalRow.1).1 = row.1 := by
    simpa only [physicalRow, Equiv.apply_symm_apply, sharedBasis] using
      (coordinates_arithmetic width count Reference physicalRow).symm
  have columnArithmetic : (union physicalColumn.1).1 = column.1 := by
    simpa only [physicalColumn, Equiv.apply_symm_apply, sharedBasis] using
      (coordinates_arithmetic width count Reference physicalColumn).symm
  have rowReference : physicalRow.2 = row.2.2 := by
    simpa only [physicalRow, Equiv.apply_symm_apply] using
      (coordinates_reference width count Reference physicalRow).symm
  have columnReference : physicalColumn.2 = column.2.2 := by
    simpa only [physicalColumn, Equiv.apply_symm_apply] using
      (coordinates_reference width count Reference physicalColumn).symm
  have δ : (union physicalRow.1).2 = (union physicalColumn.1).2 ↔
      left = right ∧ row.2.1 = column.2.1 :=
    indexed_coordinates_equal width count Reference left right row column
  have entry := ContextUnion.contextUnion_frameUnitary_reference_entry
      (environment := environment.quantum)
    (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    (Encoding.runtimeProgram width modulus coefficient coordinate)
    physicalRow.1 physicalColumn.1 physicalRow.2 physicalColumn.2
  change (Encoding.coordinateOperator (environment := environment) width count modulus coefficient
    coordinate Reference :
      Matrix _ _ ℂ) physicalRow physicalColumn =
    (((Encoding.runtimeProgram width modulus coefficient coordinate).matrix environment.quantum)
      (union physicalRow.1).1 (union physicalColumn.1).1 *
        (if (union physicalRow.1).2 = (union physicalColumn.1).2 then 1 else 0)) *
      (if physicalRow.2 = physicalColumn.2 then 1 else 0) at entry
  change (Encoding.coordinateOperator (environment := environment) width count modulus coefficient
    coordinate Reference :
    Matrix _ _ ℂ) physicalRow physicalColumn = _
  rw [entry, rowArithmetic, columnArithmetic, rowReference, columnReference]
  unfold bankCoordinateOperator
  apply split_indexed_identity
  exact δ

/-- The common-bank representation of one real conversion is an actual exponent block diagonal. -/
lemma coordinateOperator_bankFirst (width count : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ)
    (coordinate : MeasuredPointAddition.Coordinate) (Reference : Register) :
    (Encoding.coordinateOperator (environment := environment) width count modulus coefficient
      coordinate Reference :
        Matrix _ _ ℂ).submatrix
      (bankFirst width count Reference).symm (bankFirst width count Reference).symm =
        Matrix.blockDiagonal (fun _ : Exponents count =>
          bankCoordinateOperator (environment := environment) width modulus coefficient coordinate
            Reference) := by
  ext row column
  change (Encoding.coordinateOperator (environment := environment) width count modulus coefficient
    coordinate Reference :
      Matrix _ _ ℂ)
    ((coordinates width count Reference).symm (row.2, row.1))
    ((coordinates width count Reference).symm (column.2, column.1)) =
      if row.2 = column.2 then
        bankCoordinateOperator (environment := environment) width modulus coefficient coordinate
          Reference row.1 column.1 else 0
  exact coordinateOperator_common_entry width count modulus coefficient coordinate Reference
    row.2 column.2 row.1 column.1

/-- The actual pair conversion is X followed by Y on this same complete bank. -/
def bankPairOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    Matrix (Bank width Reference) (Bank width Reference) ℂ :=
  bankCoordinateOperator (environment := environment) width modulus coefficient .y Reference *
    bankCoordinateOperator (environment := environment) width modulus coefficient .x Reference

/-- The two real conversion instructions use the same exponent-independent bank operator. -/
lemma pairOperator_bankFirst (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    (Encoding.pairOperator (environment := environment) width count modulus coefficient Reference
      : Matrix _ _ ℂ).submatrix
      (bankFirst width count Reference).symm (bankFirst width count Reference).symm =
        Matrix.blockDiagonal (fun _ : Exponents count =>
          bankPairOperator (environment := environment) width modulus coefficient Reference) := by
  let basis := bankFirst width count Reference
  let x : HilbertOperator ((readyContext width count).register.prod Reference) :=
    Encoding.coordinateOperator (environment := environment) width count modulus coefficient .x
      Reference
  let y : HilbertOperator ((readyContext width count).register.prod Reference) :=
    Encoding.coordinateOperator (environment := environment) width count modulus coefficient .y
      Reference
  have xLaw := coordinateOperator_bankFirst (environment := environment) width count modulus
    coefficient .x Reference
  have yLaw := coordinateOperator_bankFirst (environment := environment) width count modulus
    coefficient .y Reference
  change x.submatrix basis.symm basis.symm = Matrix.blockDiagonal
    (fun _ : Exponents count =>
      bankCoordinateOperator (environment := environment) width modulus coefficient .x Reference)
        at xLaw
  change y.submatrix basis.symm basis.symm = Matrix.blockDiagonal
    (fun _ : Exponents count =>
      bankCoordinateOperator (environment := environment) width modulus coefficient .y Reference)
        at yLaw
  change (y * x).submatrix basis.symm basis.symm = _
  rw [← Matrix.submatrix_mul_equiv y x basis.symm basis.symm basis.symm,
    yLaw, xLaw, ← Matrix.blockDiagonal_mul]
  rfl

/-- All four real conversions surround the unchanged measured word on one complete dirty bank. -/
def convertedBankWord {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (length : Nat) (indices : Fin length → Fin count)
    (path : Fin length → Branch p.size count) (exponent : Exponents count) :
    Matrix (Bank p.size Reference) (Bank p.size Reference) ℂ :=
  bankPairOperator (environment := environment) p.size (InPlaceTarget.modulusWord p) coefficient
    Reference *
    bankWord (environment := environment) E points Reference length indices path exponent *
    bankPairOperator (environment := environment) p.size (InPlaceTarget.modulusWord p)
      coefficient⁻¹ Reference

end

end Converted
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
