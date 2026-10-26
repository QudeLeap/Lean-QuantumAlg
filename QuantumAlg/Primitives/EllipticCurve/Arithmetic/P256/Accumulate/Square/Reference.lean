/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Square.Program
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # Paid original-word square subtraction with arbitrary coherent input and Reference -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square

noncomputable section

open QuantumAlg.EncodedBit Horner
open scoped BigOperators

variable {Rest : Type} (rest : BinaryLabelEncoding Rest) (outer : EncodedBit rest)

def referenceOperator (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical
      (operandEncoding (savedEncoding rest)).width).toQuantum.register.prod Reference) :=
  UnitaryOperator.prodTensor ((program rest outer).matrix environment)
    (1 : UnitaryOperator Reference)

lemma reference_ket (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target) (retained : Rest)
    {Reference : Register} (reference : Reference.Index) :
    (referenceOperator rest outer environment Reference).applyVec
        (NormalizedVector.ket
          (R := (QubitLayout.canonical
            (operandEncoding (savedEncoding rest)).width).toQuantum.register.prod Reference)
          ((QubitLayout.canonical _).basisEquiv.symm
            ((operandEncoding (savedEncoding rest)).encode
              ((((source, target), false), (false, false)), (zeroWord, retained))),
              reference)).vec =
      (NormalizedVector.ket
        (R := (QubitLayout.canonical
          (operandEncoding (savedEncoding rest)).width).toQuantum.register.prod Reference)
        ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding (savedEncoding rest)).encode
            ((((source, Inverse.differenceWord source source target (outer.get retained)), false),
              (false, false)), (zeroWord, retained))), reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (program_canonical rest outer environment source target sourceCanonical targetCanonical
      retained)
  change UnitaryOperator.applyVec ((program rest outer).matrix environment)
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((operandEncoding (savedEncoding rest)).encode
        ((((source, target), false), (false, false)), (zeroWord, retained))))).vec = _ at actual
  change (UnitaryOperator.prodTensor ((program rest outer).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- The existing copy word is cleared beside all source, accumulator,
selector and Ref correlations. -/
lemma coherent_reference (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (source target : Index → Word) (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index)) (retained : Index → Rest)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (referenceOperator rest outer environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket
            (R := (QubitLayout.canonical
              (operandEncoding (savedEncoding rest)).width).toQuantum.register.prod Reference)
            ((QubitLayout.canonical _).basisEquiv.symm
              ((operandEncoding (savedEncoding rest)).encode
                ((((source index, target index), false), (false, false)),
                  (zeroWord, retained index))), reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket
          (R := (QubitLayout.canonical
            (operandEncoding (savedEncoding rest)).width).toQuantum.register.prod Reference)
          ((QubitLayout.canonical _).basisEquiv.symm
            ((operandEncoding (savedEncoding rest)).encode
              ((((source index, Inverse.differenceWord (source index) (source index)
                (target index) (outer.get (retained index))), false), (false, false)),
                  (zeroWord, retained index))), reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    reference_ket rest outer environment (source index) (target index) (sourceCanonical index)
      (targetCanonical index) (retained index) (reference index)]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square
