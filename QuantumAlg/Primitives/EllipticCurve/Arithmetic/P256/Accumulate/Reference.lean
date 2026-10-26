/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Correctness
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # Entire actual arbitrary-accumulator MAC with an arbitrary external Reference -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit Horner
open scoped BigOperators

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

def referenceOperator (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
      Reference) :=
  UnitaryOperator.prodTensor
    ((program saved multiplier outer outerMultiplier).matrix environment)
    (1 : UnitaryOperator Reference)

lemma reference_ket (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target) (retained : Saved)
    {Reference : Register} (reference : Reference.Index) :
    (referenceOperator saved multiplier outer outerMultiplier environment Reference).applyVec
        (NormalizedVector.ket
          (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
            Reference)
          ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
            ((((source, target), false), (false, false)), retained)), reference)).vec =
      (NormalizedVector.ket
        (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
          Reference)
        ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
          ((((source, accumulatedWord source (multiplier.value retained) target
            (outer.get retained)), false), (false, false)), retained)), reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (program_canonical saved multiplier outer outerMultiplier environment source target
      sourceCanonical targetCanonical retained)
  change UnitaryOperator.applyVec
    ((program saved multiplier outer outerMultiplier).matrix environment)
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((operandEncoding saved).encode
        ((((source, target), false), (false, false)), retained)))).vec = _ at actual
  change (UnitaryOperator.prodTensor
    ((program saved multiplier outer outerMultiplier).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- Source, multiplier, arbitrary accumulator and caller correlations
all have the exact MAC action. -/
lemma coherent_reference (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (source target : Index → Word) (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index)) (retained : Index → Saved)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (referenceOperator saved multiplier outer outerMultiplier environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket
            (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
              Reference)
            ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
              ((((source index, target index), false), (false, false)), retained index)),
                reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket
          (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
            Reference)
          ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
            ((((source index, accumulatedWord (source index) (multiplier.value (retained index))
              (target index) (outer.get (retained index))), false), (false, false)),
                retained index)), reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    reference_ket saved multiplier outer outerMultiplier environment (source index) (target index)
      (sourceCanonical index) (targetCanonical index) (retained index) (reference index)]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
