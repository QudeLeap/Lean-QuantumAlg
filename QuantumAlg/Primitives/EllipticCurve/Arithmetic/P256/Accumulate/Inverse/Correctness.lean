/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Arithmetic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Correctness

/-! # Actual subtract-product action of the complete native MAC adjoint -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse

noncomputable section

open QuantumAlg.EncodedBit Horner

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

private lemma inverse_of_forward {count : Nat} {layout : QuantumLayout count}
    (first inverse : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation)
    (inverseLaw : inverse.matrix environment = (first.matrix environment)⁻¹)
    (initial final : NormalizedVector layout.register)
    (actual : first.applyNormalized environment initial = final) :
    inverse.applyNormalized environment final = initial :=
  (congrArg (inverse.applyNormalized environment) actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized first inverse inverseLaw
      initial)

lemma program_image (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target) (retained : Saved) :
    (program saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, accumulatedWord source (multiplier.value retained) target
              (outer.get retained)), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, target), false), (false, false)), retained))) :=
  inverse_of_forward (Accumulate.program saved multiplier outer outerMultiplier)
    (program saved multiplier outer outerMultiplier) environment
    (matrix_inverse saved multiplier outer outerMultiplier environment) _ _
    (Accumulate.program_canonical saved multiplier outer outerMultiplier environment source target
      sourceCanonical targetCanonical retained)

/-- Every original canonical accumulator is admitted; the selected product is subtracted
and the source, saved multiplier, entire caller frame and all clean bits are restored. -/
lemma program_canonical (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target) (retained : Saved) :
    (program saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, target), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, differenceWord source (multiplier.value retained) target
            (outer.get retained)), false), (false, false)), retained))) := by
  have image := program_image saved multiplier outer outerMultiplier environment source
    (differenceWord source (multiplier.value retained) target (outer.get retained)) sourceCanonical
    (differenceWord_canonical source (multiplier.value retained) target (outer.get retained)
      targetCanonical) retained
  have actual := accumulated_difference source (multiplier.value retained) target
    (outer.get retained) targetCanonical
  have inputMatch := congrArg (fun result : Word =>
    (program saved multiplier outer outerMultiplier).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, result), false), (false, false)), retained))))) actual
  exact inputMatch.symm.trans image

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse
