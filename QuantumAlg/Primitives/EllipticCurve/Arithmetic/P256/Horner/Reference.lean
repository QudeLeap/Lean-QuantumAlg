/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Product
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # Entire actual quantum-operand Horner multiplication beside an arbitrary Reference -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit
open scoped BigOperators

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : QuantumMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (multiplier.ports index)).wire)

/-- The actual full native matrix tensored with identity on the external Reference. -/
def referenceOperator (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
      Reference) :=
  UnitaryOperator.prodTensor
    ((cleanProgram saved multiplier outer outerMultiplier).matrix environment)
    (1 : UnitaryOperator Reference)

lemma reference_ket (environment : OracleModel.empty.Interpretation)
    (source : Word) (canonical : Canonical source) (retained : Saved)
    {Reference : Register} (reference : Reference.Index) :
    (referenceOperator saved multiplier outer outerMultiplier environment Reference).applyVec
        (NormalizedVector.ket
          (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
            Reference)
          ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
            ((((source, zeroWord), false), (false, false)), retained)), reference)).vec =
      (NormalizedVector.ket
        (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
          Reference)
        ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
          ((((source, productWord source (multiplier.value source retained)
            (outer.get retained)), false), (false, false)), retained)), reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (cleanProgram_product saved multiplier outer outerMultiplier environment source canonical
      retained)
  change UnitaryOperator.applyVec
    ((cleanProgram saved multiplier outer outerMultiplier).matrix environment)
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((operandEncoding saved).encode
        ((((source, zeroWord), false), (false, false)), retained)))).vec = _ at actual
  change (UnitaryOperator.prodTensor
    ((cleanProgram saved multiplier outer outerMultiplier).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- Arbitrary quantum operand, selector, caller and external-Reference correlations are retained. -/
lemma coherent_reference (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (source : Index → Word) (canonical : ∀ index, Canonical (source index))
    (retained : Index → Saved) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (referenceOperator saved multiplier outer outerMultiplier environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket
            (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
              Reference)
            ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
              ((((source index, zeroWord), false), (false, false)), retained index)),
                reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket
          (R := (QubitLayout.canonical (operandEncoding saved).width).toQuantum.register.prod
            Reference)
          ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode
            ((((source index, productWord (source index)
              (multiplier.value (source index) (retained index)) (outer.get (retained index))),
                false), (false, false)), retained index)), reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    reference_ket saved multiplier outer outerMultiplier environment (source index)
      (canonical index) (retained index) (reference index)]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
