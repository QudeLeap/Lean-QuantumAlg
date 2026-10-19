/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division.Basis
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication.Basis
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target.Basis
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target.Agreement

/-!
# Actual stored operators agree with the independent complete-state targets

On each original-domain prepared basis column, every actual stored branch
is the independent multiplication or division unitary times the real
Hadamard amplitude. The complete auxiliary state and external reference
are included in both sides [LYL+26, sec_point_add/sec_point_add.tex:24-36,45-105,119-122].

The hypotheses are precisely 0<X<p and Y<p for prime p; Y may be zero.
No condition is imposed on the stored finite result. Density extension
and aggregation of the actual classical source fibers are separate from
these exact operator-column equations.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceOperatorAgreement

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

private lemma prepared_vec (modulus : Nat) (value numerator : Fin (2 ^ modulus.size))
    {Reference : Register} (reference : Reference.Index) :
    (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
      (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec =
      (NumeratorFrameBasis.ket modulus.size
        (InitialPortProgram.inputFrame modulus value, numerator) reference).vec := by
  have label := InPlaceTarget.preparedBasis_eq_native modulus value numerator
  exact congrArg
    (fun basis : (context modulus.size).register.Index =>
      (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
        (basis, reference)).vec) label

/-- Each actual division branch is the independent reference target with its exact amplitude. -/
lemma division_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (reference : Reference.Index) :
    HilbertOperator.applyVec
      (InPlaceDivisionConjugation.operator environment modulus prime Reference stored)
      (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
        (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec =
      WalshHadamard.invSqrtCard modulus.size •
        (InPlaceTarget.jointOperator .division modulus prime Reference).applyVec
          (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
            (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec := by
  have actual := (congrArg
    (HilbertOperator.applyVec
      (InPlaceDivisionConjugation.operator environment modulus prime Reference stored))
    (prepared_vec modulus value numerator reference)).trans
      (InPlaceDivisionBasis.operator_ket modulus prime value numerator
        positive bounded numeratorBound stored reference)
  have output := congrArg
    (fun result : Fin (2 ^ modulus.size) =>
      (NumeratorFrameBasis.ket modulus.size
        (InitialPortProgram.inputFrame modulus value, result) reference).vec)
    (InPlaceTargetAgreement.division_saved modulus prime value numerator
      positive bounded numeratorBound)
  have result := output.trans (prepared_vec modulus value
    (InPlaceTarget.resultWord .division modulus prime value numerator) reference).symm
  have target := InPlaceTarget.prepared_operator_ket .division modulus prime
    value numerator reference
  exact actual.trans (congrArg
    (fun vector : HilbertVector (Register.prod (context modulus.size).register Reference) =>
      WalshHadamard.invSqrtCard modulus.size • vector) (result.trans target.symm))

/-- Every division column retains arbitrary output and input reference coordinates exactly. -/
lemma division_column (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (reference : Reference.Index)
    (row : (Register.prod (context modulus.size).register Reference).Index) :
    InPlaceDivisionConjugation.operator environment modulus prime Reference stored row
      (InPlaceTarget.preparedBasis modulus value numerator, reference) =
      WalshHadamard.invSqrtCard modulus.size *
        InPlaceTarget.jointOperator .division modulus prime Reference row
          (InPlaceTarget.preparedBasis modulus value numerator, reference) := by
  have values := congrArg
    (fun vector : HilbertVector (Register.prod (context modulus.size).register Reference) =>
      vector row) (division_ket (environment := environment) modulus prime value numerator
        positive bounded numeratorBound stored reference)
  change HilbertOperator.applyVec
    (InPlaceDivisionConjugation.operator environment modulus prime Reference stored)
    (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
      (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec row =
    WalshHadamard.invSqrtCard modulus.size * HilbertOperator.applyVec
      (InPlaceTarget.jointOperator .division modulus prime Reference :
        HilbertOperator (Register.prod (context modulus.size).register Reference))
      (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
        (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec row at values
  rw [HilbertOperator.applyVec_ket, HilbertOperator.applyVec_ket] at values
  exact values

/-- Each actual multiplication branch is the independent target with its measured amplitude. -/
lemma multiplication_ket (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (reference : Reference.Index) :
    HilbertOperator.applyVec
      (InPlaceMultiplicationConjugation.operator environment modulus prime Reference stored)
      (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
        (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec =
      WalshHadamard.invSqrtCard modulus.size •
        (InPlaceTarget.jointOperator .multiplication modulus prime Reference).applyVec
          (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
            (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec := by
  have actual := (congrArg
    (HilbertOperator.applyVec
      (InPlaceMultiplicationConjugation.operator environment modulus prime Reference stored))
    (prepared_vec modulus value numerator reference)).trans
      (InPlaceMultiplicationBasis.operator_ket modulus prime value numerator
        positive bounded numeratorBound stored reference)
  have output := congrArg
    (fun result : Fin (2 ^ modulus.size) =>
      (NumeratorFrameBasis.ket modulus.size
        (InitialPortProgram.inputFrame modulus value, result) reference).vec)
    (InPlaceTargetAgreement.multiplication_saved modulus prime value numerator
      positive bounded numeratorBound)
  have result := output.trans (prepared_vec modulus value
    (InPlaceTarget.resultWord .multiplication modulus prime value numerator) reference).symm
  have target := InPlaceTarget.prepared_operator_ket .multiplication modulus prime
    value numerator reference
  exact actual.trans (congrArg
    (fun vector : HilbertVector (Register.prod (context modulus.size).register Reference) =>
      WalshHadamard.invSqrtCard modulus.size • vector) (result.trans target.symm))

/-- Every multiplication column retains both reference indices, including off-diagonal entries. -/
lemma multiplication_column (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus)
    {Reference : Register} (stored : Store (context modulus.size))
    (reference : Reference.Index)
    (row : (Register.prod (context modulus.size).register Reference).Index) :
    InPlaceMultiplicationConjugation.operator environment modulus prime Reference stored row
      (InPlaceTarget.preparedBasis modulus value numerator, reference) =
      WalshHadamard.invSqrtCard modulus.size *
        InPlaceTarget.jointOperator .multiplication modulus prime Reference row
          (InPlaceTarget.preparedBasis modulus value numerator, reference) := by
  have values := congrArg
    (fun vector : HilbertVector (Register.prod (context modulus.size).register Reference) =>
      vector row) (multiplication_ket (environment := environment) modulus prime value numerator
        positive bounded numeratorBound stored reference)
  change HilbertOperator.applyVec
    (InPlaceMultiplicationConjugation.operator environment modulus prime Reference stored)
    (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
      (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec row =
    WalshHadamard.invSqrtCard modulus.size * HilbertOperator.applyVec
      (InPlaceTarget.jointOperator .multiplication modulus prime Reference :
        HilbertOperator (Register.prod (context modulus.size).register Reference))
      (NormalizedVector.ket (R := Register.prod (context modulus.size).register Reference)
        (InPlaceTarget.preparedBasis modulus value numerator, reference)).vec row at values
  rw [HilbertOperator.applyVec_ket, HilbertOperator.applyVec_ket] at values
  exact values

end

end QuantumAlg.MeasuredUncompute.InPlaceOperatorAgreement
