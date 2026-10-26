/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Square.Copy
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Correctness

/-!
# Paid original-word copy, inverse quantum MAC and complete copy restoration

The arbitrary original accumulator receives the selected negative square.
The existing original copy word is genuinely zero at entry and restored to
zero at exit. The source and the complete caller complement are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner

variable {Rest : Type} (rest : BinaryLabelEncoding Rest) (outer : EncodedBit rest)

/-- The square multiplier copy is an existing original word, never an allocation. -/
def program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding (savedEncoding rest)).width).toQuantum :=
  UnitaryCircuit.seq (copyProgram rest)
    (UnitaryCircuit.seq
      (Inverse.program (savedEncoding rest) (multiplier rest) (outerBit rest outer)
        (outer_multiplier_ne rest outer)) (uncopyProgram rest))

/-- Complete actual square subtraction admits every canonical original accumulator. -/
lemma program_canonical (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target) (retained : Rest) :
    (program rest outer).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding (savedEncoding rest)).encode
            ((((source, target), false), (false, false)), (zeroWord, retained))))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding (savedEncoding rest)).encode
          ((((source, Inverse.differenceWord source source target (outer.get retained)), false),
            (false, false)), (zeroWord, retained)))) := by
  let ket := fun state => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((operandEncoding (savedEncoding rest)).encode state))
  have copied : (copyProgram rest).applyNormalized environment
      (ket ((((source, target), false), (false, false)), (zeroWord, retained))) =
        ket ((((source, target), false), (false, false)), (source, retained)) :=
    ((copy_realizes rest environment).apply_encoded_ket _).trans
      (congrArg ket (copy_clean rest _ retained))
  have subtracted := Inverse.program_canonical (savedEncoding rest) (multiplier rest)
    (outerBit rest outer) (outer_multiplier_ne rest outer) environment source target
    sourceCanonical targetCanonical (source, retained)
  have cleared : (uncopyProgram rest).applyNormalized environment
      (ket ((((source, Inverse.differenceWord source source target (outer.get retained)), false),
        (false, false)), (source, retained))) =
      ket ((((source, Inverse.differenceWord source source target (outer.get retained)), false),
        (false, false)), (zeroWord, retained)) :=
    ((uncopy_realizes rest environment).apply_encoded_ket _).trans
      (congrArg ket (uncopy_clean rest _ retained))
  exact UnitaryCircuit.applyNormalized_seq_of_eq copied
    (UnitaryCircuit.applyNormalized_seq_of_eq subtracted cleared)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square
