/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.BankWords
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Exponents.Matrices
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import Lean.Elab.Tactic.Omega

/-!
# Paired input and ordered bank-word coordinates

The paired finite-word basis agrees with the explicit first-then-second
bit-tuple function. Its full-bank reindexing preserves every Reference and
dirty arithmetic coordinate. The scalar preparation amplitudes retain all
padded zeros, including width zero, without any input-state premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Fourier
namespace PairedExponents

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.QuantumFourierTransform QuantumFourierTransform.Semiclassical
open ScalarMultiplication.MeasuredPlacement ScalarMultiplication.MeasuredPlacement.Allocation
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open QuantumAlg.FiniteCyclicDLP ConcreteCircuitAccess
open Recovery.Reference.Measured.CommonBank
open MAU.Inversion.SharedEEA

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Both original physical bit tuples retain their complete native finite labels. -/
def tuplePair (m : Nat) : (Bits m × Bits m) ≃ Recovery.Reference.Exponents.Pair m :=
  (binaryEquiv m).prodCongr (binaryEquiv m)

private lemma bool_encode_symm (value : Bool) :
    BinaryLabelEncoding.bool.encode value = finTwoEquiv.symm value := by
  cases value <;> rfl

private lemma physical_bit_tuple (m : Nat) (input : Bits m) (current : Fin m) :
    BinaryLabelEncoding.bool.encode
        ((binaryEquiv m input).val.testBit (m - 1 - current.val)) =
      tupleCoordinates m input current := by
  have reversed : current.rev.val = m - 1 - current.val := by
    rw [Fin.val_rev]
    omega
  rw [bool_encode_symm, ← reversed]
  exact (BinaryBasis.bigEndianEquiv_symm_value m (binaryEquiv m input) current).symm

private lemma pairBasis_tuple_position_left (modulus m : Nat) (first second : Bits m)
    (current : Fin m) :
    Recovery.Reference.Exponents.pairBasis modulus m (tuplePair m (first, second))
        (ActualFeedback.position false current) = tupleCoordinates m first current := by
  have slot : ActualFeedback.position false current =
      (⟨current.val, by omega⟩ : Fin (2 * m)) := by
    apply Fin.ext
    rw [ActualFeedback.position_val]
    rfl
  have native := congrFun (Recovery.Reference.Exponents.pairBasis_apply modulus m
    (tuplePair m (first, second))) (ActualFeedback.position false current)
  have coordinate := pairedExponentInput_left modulus m
    (binaryEquiv m first, binaryEquiv m second) current
  have positioned := congrArg (rangeBasis modulus.size (2 * m)
    (pairedExponentInput modulus m (tuplePair m (first, second)))) slot
  exact native.trans (positioned.trans (coordinate.trans (physical_bit_tuple m first current)))

private lemma pairBasis_tuple_position_right (modulus m : Nat) (first second : Bits m)
    (current : Fin m) :
    Recovery.Reference.Exponents.pairBasis modulus m (tuplePair m (first, second))
        (ActualFeedback.position true current) = tupleCoordinates m second current := by
  have slot : ActualFeedback.position true current =
      (⟨m + current.val, by omega⟩ : Fin (2 * m)) := by
    apply Fin.ext
    rw [ActualFeedback.position_val]
    rfl
  have native := congrFun (Recovery.Reference.Exponents.pairBasis_apply modulus m
    (tuplePair m (first, second))) (ActualFeedback.position true current)
  have coordinate := pairedExponentInput_right modulus m
    (binaryEquiv m first, binaryEquiv m second) current
  have positioned := congrArg (rangeBasis modulus.size (2 * m)
    (pairedExponentInput modulus m (tuplePair m (first, second)))) slot
  exact native.trans (positioned.trans (coordinate.trans (physical_bit_tuple m second current)))

/-- Each original native control occupies the same first or second physical tuple position. -/
lemma pairBasis_tuple_position (modulus m : Nat) (first second : Bits m)
    (secondBlock : Bool) (current : Fin m) :
    Recovery.Reference.Exponents.pairBasis modulus m (tuplePair m (first, second))
        (ActualFeedback.position secondBlock current) =
      tupleCoordinates m (if secondBlock then second else first) current := by
  cases secondBlock with
  | false => exact pairBasis_tuple_position_left modulus m first second current
  | true => exact pairBasis_tuple_position_right modulus m first second current

/-- The actual old native pairBasis is exactly the original two-tuple exponent function. -/
lemma pairBasis_tuple (modulus m : Nat) (first second : Bits m) :
    Recovery.Reference.Exponents.pairBasis modulus m (tuplePair m (first, second)) =
      Recovery.Layout.BankWords.pairedExponent m first second := by
  have atPosition (secondBlock : Bool) (current : Fin m) :
      Recovery.Reference.Exponents.pairBasis modulus m (tuplePair m (first, second))
          (ActualFeedback.position secondBlock current) =
        Recovery.Layout.BankWords.pairedExponent m first second
          (ActualFeedback.position secondBlock current) := by
    rw [pairBasis_tuple_position]
    cases secondBlock <;>
      simp only [Bool.false_eq_true, ↓reduceIte,
        Recovery.Layout.BankWords.pairedExponent_position_false,
          Recovery.Layout.BankWords.pairedExponent_position_true]
  have atIndex (index : Fin (m + m)) :
      Recovery.Reference.Exponents.pairBasis modulus m (tuplePair m (first, second))
          (Fin.cast (Nat.two_mul m).symm index) =
        Recovery.Layout.BankWords.pairedExponent m first second
          (Fin.cast (Nat.two_mul m).symm index) := by
    refine Fin.addCases (fun current => ?_) (fun current => ?_) index
    · simpa only [ActualFeedback.position, StageWord.blockIndex_original_order,
        Bool.false_eq_true, ↓reduceIte] using atPosition false current
    · simpa only [ActualFeedback.position, StageWord.blockIndex_original_order,
        ↓reduceIte] using atPosition true current
  funext index
  exact atIndex (Fin.cast (Nat.two_mul m) index)

/-- Reindex paired words without changing the bank or Reference. -/
def tupleBankBasis (modulus m : Nat) (Reference : Register) :
    (Recovery.Reference.Measured.CommonBank.Bank modulus.size Reference × (Bits m × Bits m)) ≃
      (Recovery.Reference.Measured.CommonBank.Bank modulus.size Reference ×
        Recovery.Reference.Exponents.Pair m) :=
  (Equiv.refl (Recovery.Reference.Measured.CommonBank.Bank modulus.size Reference)).prodCongr
    (tuplePair m)

/-- The actual old arithmetic bank word now uses its original native exponent pair directly. -/
lemma old_native_bankWord_eq_exponentPair {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → StageWord.PathWord.PathDensity.Branch p.size m)
    (first second : Bits m) :
    Recovery.Reference.Measured.CommonBank.bankWord (environment := environment) E points
      Reference (2 * m) id
        (Recovery.Layout.BankWords.oldPath p m (2 * m) path)
        (Recovery.Reference.Exponents.pairBasis p m (tuplePair m (first, second))) =
      (OrderedBankWord.exponentPair
        (ActualFeedback.pathBankAction (environment := environment) E points Reference path false)
        (ActualFeedback.pathBankAction (environment := environment) E points Reference path true)
        m (binaryEquiv m first).val (binaryEquiv m second).val).submatrix
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm := by
  rw [pairBasis_tuple]
  exact Recovery.Layout.BankWords.old_bankWord_eq_exponentPair E points Reference path first second

universe u
variable {G : Type u} [Group G]

/-- Both literal finite range preparations retain every padded zero coefficient as well. -/
lemma preparation_tuple_amplitude (problem : KnownOrderProblem G)
    (first second : Bits (orderWidth problem)) :
    Recovery.Reference.Exponents.preparationAmplitude problem
        (tuplePair (orderWidth problem) (first, second)) =
      (if (binaryEquiv (orderWidth problem) first).val < problem.order then
        OrderPreparation.invSqrtOrder problem.order else 0) *
      (if (binaryEquiv (orderWidth problem) second).val < problem.order then
        OrderPreparation.invSqrtOrder problem.order else 0) :=
  Recovery.Reference.Exponents.preparationAmplitude_apply problem _

end

end PairedExponents
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Fourier
