/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Converted.BankGoodColumns
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.OriginalGroupEndpoint
import all QuantumAlg.Util.EllipticCurve.Representation

/-!
# Prepared actual bank labels retain exactly the original group kernel

The unchanged unit coefficient preserves both affine coordinates. Equality of
prepared output-bank labels is therefore precisely equality of finite group
points and the original external Reference labels. A separate matrix identity
computes the full Gram entry of two literal delta columns without omitting any
bank coordinate. The later actual outcome sum and Fourier event are separate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace PreparedBankGroupKernel

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open MeasuredPointAddition
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

/-- The original coefficient cannot merge distinct finite affine points. -/
lemma encodedWords_point_injective (coefficient : (ZMod p)ˣ) :
    Function.Injective (fun P : AffinePoint E =>
      ConvertedBankGoodColumns.encodedWords coefficient P.x P.y) := by
  intro P Q same
  have xValues := congrArg (fun words : Fin (2 ^ p.size) × Fin (2 ^ p.size) =>
    words.1.val) same
  have yValues := congrArg (fun words : Fin (2 ^ p.size) × Fin (2 ^ p.size) =>
    words.2.val) same
  change ((coefficient : ZMod p) * P.x).val =
    ((coefficient : ZMod p) * Q.x).val at xValues
  change ((coefficient : ZMod p) * P.y).val =
    ((coefficient : ZMod p) * Q.y).val at yValues
  exact AffinePoint.ext_coordinates P Q
    ((Units.mul_right_inj coefficient).mp (ZMod.val_injective p xValues))
    ((Units.mul_right_inj coefficient).mp (ZMod.val_injective p yValues))

/-- The actual prepared output bank has exactly the original finite-group and Reference kernel. -/
lemma preparedBank_eq_iff_group (coefficient : (ZMod p)ˣ) (Reference : Register)
    (P Q : AffinePoint E) (left right : Reference.Index) :
    PointBankGoodColumns.preparedBank p Reference
        (ConvertedBankGoodColumns.encodedWords coefficient P.x P.y) left =
      PointBankGoodColumns.preparedBank p Reference
        (ConvertedBankGoodColumns.encodedWords coefficient Q.x Q.y) right ↔
      P.toGroupPoint = Q.toGroupPoint ∧ left = right := by
  constructor
  · intro same
    have arithmetic := congrArg Prod.fst same
    have assembly := (InPlaceTarget.frameEquiv p.size).injective arithmetic
    have words := congrArg Prod.snd assembly
    have points : P = Q := encodedWords_point_injective coefficient words
    exact ⟨congrArg AffinePoint.toGroupPoint points,
      congrArg (fun bank : Recovery.Point.Instrument.FiberBank p.size Reference => bank.2.2) same⟩
  · rintro ⟨groupSame, referenceSame⟩
    have points : P = Q := AffinePoint.toGroupPoint_injective groupSame
    cases points
    cases referenceSame
    rfl

/-- Full Gram multiplication of two actual delta columns retains their relative complex scalar. -/
lemma gram_delta_columns {Bank : Type} [Fintype Bank]
    (first second : Matrix Bank Bank ℂ) (inputLeft inputRight outputLeft outputRight : Bank)
    (firstScalar secondScalar : ℂ)
    (firstColumn : ∀ row, first row inputLeft =
      firstScalar * if row = outputLeft then 1 else 0)
    (secondColumn : ∀ row, second row inputRight =
      secondScalar * if row = outputRight then 1 else 0) :
    (first.conjTranspose * second) inputLeft inputRight =
      (star firstScalar * secondScalar) * if outputLeft = outputRight then 1 else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, firstColumn, secondColumn,
    apply_ite (fun value : ℂ => star value), star_zero,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fintype.sum_ite_eq']
  simp only [eq_comm]

end

end PreparedBankGroupKernel
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
