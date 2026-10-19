/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.Coefficients
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.TwoBankFourier
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Converted.CommonBank
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.CoherentContraction
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.InitializedFourier

/-!
# Full-bank reindexing and coherent weighted-word algebra

Removing an explicitly empty quantum frame preserves both ordered conversion
operators. Fixed left and right matrices distribute over a coherent weighted
sum without moving across any bank-word factor or combining measured paths.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Fourier
namespace WeightedWords

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

private lemma coordinate_entry_indicator_congr (entry : ℂ) (selector left right : Prop)
    (selectorLeft selectorRight : Decidable selector)
    (referenceLeft : Decidable left) (referenceRight : Decidable right)
    (sameReference : left ↔ right) :
    entry * (@ite ℂ selector selectorLeft 1 0) * (@ite ℂ left referenceLeft 1 0) =
      entry * (@ite ℂ selector selectorRight 1 0) * (@ite ℂ right referenceRight 1 0) := by
  cases propext sameReference
  cases Subsingleton.elim selectorLeft selectorRight
  cases Subsingleton.elim referenceLeft referenceRight
  rfl

open QuantumAlg QuantumAlg.Execution
open Recovery.Stage.PointCoordinates (ResidualReference)
open Recovery.Reference.Measured.CommonBank.CoherentContraction (weightedWord)
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Actual conversion on the bank loses only the explicitly empty quantum cell frame. -/
lemma coordinate_empty_frame (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) :
    (Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
      modulus coefficient coordinate
        (ResidualReference width m Reference)).submatrix
        (Recovery.Layout.Reference.bankBasis width m Reference).symm
        (Recovery.Layout.Reference.bankBasis width m Reference).symm =
      Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
        modulus coefficient coordinate
        Reference := by
  ext row column
  have referenceSame :
      (((Recovery.Layout.Reference.frameBasis width m).symm (), row.2.2) :
          (ResidualReference width m Reference).Index) =
        ((Recovery.Layout.Reference.frameBasis width m).symm (), column.2.2) ↔
      row.2.2 = column.2.2 := by
    constructor
    · intro same
      exact congrArg
        (fun value : (ResidualReference width m Reference).Index =>
          (value.2 : Reference.Index)) same
    · intro same
      exact Prod.ext rfl same
  simp only [Recovery.Reference.Converted.bankCoordinateOperator, Matrix.submatrix_apply,
    Recovery.Layout.Reference.bankBasis_symm]
  exact coordinate_entry_indicator_congr _ _ _ _ _ _ _ _ referenceSame

/-- The original X then Y conversion keeps its product order after that exact bank reindexing. -/
lemma pair_empty_frame (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
      coefficient
        (ResidualReference width m Reference)).submatrix
        (Recovery.Layout.Reference.bankBasis width m Reference).symm
        (Recovery.Layout.Reference.bankBasis width m Reference).symm =
      Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
        coefficient Reference := by
  unfold Recovery.Reference.Converted.bankPairOperator
  rw [← Matrix.submatrix_mul_equiv _ _
    (Recovery.Layout.Reference.bankBasis width m Reference).symm
    (Recovery.Layout.Reference.bankBasis width m Reference).symm
    (Recovery.Layout.Reference.bankBasis width m Reference).symm,
    coordinate_empty_frame, coordinate_empty_frame]

/-- Conversion factors distribute over coherent inputs without moving across any bank word. -/
lemma weighted_surrounded {Exponent Bank : Type} [Fintype Exponent] [Fintype Bank]
    (amplitude rowCoefficient : Exponent → ℂ)
    (operators : Exponent → Matrix Bank Bank ℂ) (left right : Matrix Bank Bank ℂ) :
    weightedWord amplitude rowCoefficient
        (fun exponent => left * operators exponent * right) =
      left * weightedWord amplitude rowCoefficient operators * right := by
  simp only [weightedWord, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

end

end WeightedWords
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Fourier
