/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Common.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Stored.Step
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Fibers
import Mathlib.Data.Matrix.Block

/-!
# Original indexed kernels on the same bank for every exponent and active index

The ambient identity is the existing original pointKraus_memory_entry, not an
observation of exponents. The active-control delta and all ambient physical deltas
combine into one all-exponent delta. Both arithmetic measurement labels are common to
ket and bra. No point matrix or arithmetic factor changes order.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Measured.CommonBank

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The existing point block now acts on one fixed arithmetic/selector/Reference bank. -/
def bankKraus {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (Reference : Register)
    (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (readyContext p.size count)) (bit : Fin 2) :
    Matrix (Bank p.size Reference) (Bank p.size Reference) ℂ :=
  Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference division
    (pointStore p.size active
    stored).1 bit

private lemma point_label_entry {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register)
    (division stored : Store (MeasuredPointAddition.context p.size))
    (left right : Fin 2) (row column : Bank p.size Reference) :
    Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference division stored
        (MeasuredPointAddition.label p.size left row.2.1 row.1, row.2.2)
        (MeasuredPointAddition.label p.size right column.2.1 column.1, column.2.2) =
      if left = right then
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
          division stored left row column
          else 0 := by
  simpa only [Recovery.Point.Instrument.fiberBasis_symm] using
    Recovery.Point.Instrument.pointKraus_fiber_entry E Q Reference division stored left right
      row column

/-- Control and retained-register deltas select exactly the original complete fiber. -/
private lemma matching_fibers_mul (coefficient : ℂ) {control retained complete : Prop}
    [Decidable control] [Decidable retained] [Decidable complete]
    (same : complete ↔ control ∧ retained) :
    (if control then coefficient else 0) * (if retained then 1 else 0) =
      if complete then coefficient else 0 := by
  by_cases selected : complete
  · have parts := same.mp selected
    simp only [if_pos parts.1, if_pos parts.2, if_pos selected, mul_one]
  · by_cases active : control
    · have absent : ¬ retained := fun value => selected (same.mpr ⟨active, value⟩)
      simp only [if_pos active, if_neg absent, if_neg selected, mul_zero]
    · simp only [if_neg active, if_neg selected, zero_mul]

/-- Every actual original exponent is preserved by the full same-outcome kernel. -/
lemma stepKraus_common_entry {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (Reference : Register)
    (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (readyContext p.size count))
    (left right : Exponents count) (row column : Bank p.size Reference) :
    stepKraus (environment := environment) E Q active Reference division stored
        ((coordinates p.size count Reference).symm (left, row))
        ((coordinates p.size count Reference).symm (right, column)) =
      if left = right then
        bankKraus (environment := environment) E Q active Reference division stored (left active)
          row column else 0 := by
  let physicalRow := (coordinates p.size count Reference).symm (left, row)
  let physicalColumn := (coordinates p.size count Reference).symm (right, column)
  have rowPoint : (stepCoordinates p.size active Reference physicalRow).1 =
      MeasuredPointAddition.label p.size (left active) row.2.1 row.1 := by
    simpa only [physicalRow, Equiv.apply_symm_apply] using
      stepCoordinates_point p.size active Reference physicalRow
  have columnPoint : (stepCoordinates p.size active Reference physicalColumn).1 =
      MeasuredPointAddition.label p.size (right active) column.2.1 column.1 := by
    simpa only [physicalColumn, Equiv.apply_symm_apply] using
      stepCoordinates_point p.size active Reference physicalColumn
  have rowReference : physicalRow.2 = row.2.2 := by
    simpa only [physicalRow, Equiv.apply_symm_apply] using
      (coordinates_reference p.size count Reference physicalRow).symm
  have columnReference : physicalColumn.2 = column.2.2 := by
    simpa only [physicalColumn, Equiv.apply_symm_apply] using
      (coordinates_reference p.size count Reference physicalColumn).symm
  have δ : left = right ↔
      left active = right active ∧
        (pointBasis p.size active physicalRow.1).2 =
          (pointBasis p.size active physicalColumn.1).2 := by
    simpa only [physicalRow, physicalColumn, Equiv.apply_symm_apply] using
      exponents_equal_iff p.size active Reference physicalRow physicalColumn
  change stepKraus (environment := environment) E Q active Reference division stored physicalRow
    physicalColumn = _
  rw [stepKraus_original_point, Matrix.submatrix_apply]
  change Recovery.Point.Instrument.pointKraus (environment := environment) E Q
      ((ambientContext p.size active).register.prod Reference) division
      (pointStore p.size active stored).1
      ((stepCoordinates p.size active Reference physicalRow).1,
        ((pointBasis p.size active physicalRow.1).2, physicalRow.2))
      ((stepCoordinates p.size active Reference physicalColumn).1,
        ((pointBasis p.size active physicalColumn.1).2, physicalColumn.2)) = _
  rw [Recovery.Point.Instrument.pointKraus_memory_entry, rowPoint, columnPoint,
    rowReference, columnReference,
    point_label_entry E Q Reference division (pointStore p.size active stored).1
      (left active) (right active) row column]
  change (if left active = right active then
      bankKraus (environment := environment) E Q active Reference division stored (left active)
        row column else 0) *
      (if (pointBasis p.size active physicalRow.1).2 =
          (pointBasis p.size active physicalColumn.1).2 then 1 else 0) = _
  exact matching_fibers_mul
    (bankKraus (environment := environment) E Q active Reference division stored (left active) row
      column) δ

/-- The product swap is mathematical coordinates only; no circuit permutation is added. -/
def bankFirst (width count : Nat) (Reference : Register) :
    ((readyContext width count).register.prod Reference).Index ≃
      Bank width Reference × Exponents count :=
  (coordinates width count Reference).trans (Equiv.prodComm _ _)

/-- Mathlib's blockDiagonal records the exact all-exponent quantum delta. -/
lemma stepKraus_bankFirst {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (Reference : Register)
    (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (readyContext p.size count)) :
    (stepKraus (environment := environment) E Q active Reference division stored).submatrix
        (bankFirst p.size count Reference).symm (bankFirst p.size count Reference).symm =
      Matrix.blockDiagonal (fun exponent : Exponents count =>
        bankKraus (environment := environment) E Q active Reference division stored (exponent
          active)) := by
  ext row column
  change stepKraus (environment := environment) E Q active Reference division stored
      ((coordinates p.size count Reference).symm (row.2, row.1))
      ((coordinates p.size count Reference).symm (column.2, column.1)) =
    if row.2 = column.2 then
      bankKraus (environment := environment) E Q active Reference division stored (row.2 active)
        row.1 column.1 else 0
  exact stepKraus_common_entry E Q active Reference division stored row.2 column.2 row.1 column.1

/-- One block diagonal operator preserves arbitrary off-diagonal exponent blocks. -/
private lemma blockDiagonal_sandwich {Exponent Arithmetic : Type}
    [Fintype Exponent] [Fintype Arithmetic] [DecidableEq Exponent]
    (operators : Exponent → Matrix Arithmetic Arithmetic ℂ)
    (density : Matrix (Arithmetic × Exponent) (Arithmetic × Exponent) ℂ)
    (left right : Exponent) :
    (Matrix.blockDiagonal operators * density *
      (Matrix.blockDiagonal operators).conjTranspose).submatrix
        (fun bank => (bank, left)) (fun bank => (bank, right)) =
      operators left * density.submatrix (fun bank => (bank, left))
        (fun bank => (bank, right)) * (operators right).conjTranspose := by
  classical
  ext row column
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal_apply, Fintype.sum_prod_type, apply_ite]

/-- Coordinate pullback keeps both exponent labels and arbitrary Reference cross entries. -/
lemma physical_sandwich_offdiagonal {width count : Nat} (Reference : Register)
    (operator : Matrix ((readyContext width count).register.prod Reference).Index
      ((readyContext width count).register.prod Reference).Index ℂ)
    (operators : Exponents count → Matrix (Bank width Reference) (Bank width Reference) ℂ)
    (diagonal : operator.submatrix
        (bankFirst width count Reference).symm (bankFirst width count Reference).symm =
      Matrix.blockDiagonal operators)
    (density : Matrix ((readyContext width count).register.prod Reference).Index
      ((readyContext width count).register.prod Reference).Index ℂ)
    (left right : Exponents count) :
    (operator * density * operator.conjTranspose).submatrix
        (fun bank => (coordinates width count Reference).symm (left, bank))
        (fun bank => (coordinates width count Reference).symm (right, bank)) =
      operators left * density.submatrix
        (fun bank => (coordinates width count Reference).symm (left, bank))
        (fun bank => (coordinates width count Reference).symm (right, bank)) *
          (operators right).conjTranspose := by
  let basis := bankFirst width count Reference
  have pulled : (operator * density * operator.conjTranspose).submatrix
      basis.symm basis.symm =
      Matrix.blockDiagonal operators * density.submatrix basis.symm basis.symm *
        (Matrix.blockDiagonal operators).conjTranspose := by
    change operator.submatrix basis.symm basis.symm = Matrix.blockDiagonal operators at diagonal
    rw [← Matrix.submatrix_mul_equiv (operator * density) operator.conjTranspose
        basis.symm basis.symm basis.symm,
      ← Matrix.submatrix_mul_equiv operator density basis.symm basis.symm basis.symm,
      ← Matrix.conjTranspose_submatrix]
    rw [diagonal]
  ext row column
  have entry := congrArg (fun matrix => matrix (row, left) (column, right)) pulled
  have blocks := blockDiagonal_sandwich operators
    (density.submatrix basis.symm basis.symm) left right
  exact entry.trans (congrArg (fun matrix => matrix row column) blocks)

end

end Measured.CommonBank
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
