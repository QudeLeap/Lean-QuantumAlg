/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Correctness

/-! # Actual selected modular-product output in the complete original Horner frame -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit

def productWord (source multiplier : Word) (selected : Bool) : Word :=
  ⟨if selected then (multiplier.val * source.val) % modulus else 0, by
    cases selected with
    | false => exact Nat.two_pow_pos width
    | true => exact (Nat.mod_lt _ modulus_positive).trans modulus_lt_capacity⟩

lemma prefixWord_eq_product (source multiplier : Word) (selected : Bool) :
    prefixWord source multiplier selected width = productWord source multiplier selected :=
  Fin.ext (prefixWord_full source multiplier selected)

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : QuantumMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (multiplier.ports index)).wire)

/-- Both outer branches have the literal product output, with all other original fields restored. -/
lemma clean_product (source : Word) (canonical : Canonical source) (retained : Saved) :
    cleanStep saved multiplier outer outerMultiplier
        ((((source, zeroWord), false), (false, false)), retained) =
      ((((source, productWord source (multiplier.value source retained)
        (outer.get retained)), false), (false, false)), retained) :=
  (clean_canonical saved multiplier outer outerMultiplier source canonical retained).trans
    (congrArg (fun result : Word => ((((source, result), false), (false, false)), retained))
      (prefixWord_eq_product source (multiplier.value source retained) (outer.get retained)))

/-- Actual native execution, without phase loss, produces the selected modular product. -/
lemma cleanProgram_product (environment : OracleModel.empty.Interpretation)
    (source : Word) (canonical : Canonical source) (retained : Saved) :
    (cleanProgram saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, zeroWord), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, productWord source (multiplier.value source retained)
            (outer.get retained)), false), (false, false)), retained))) :=
  ((clean_realizes saved multiplier outer outerMultiplier environment).apply_encoded_ket _).trans
    (congrArg (fun state => NormalizedVector.ket
      ((QubitLayout.canonical _).basisEquiv.symm ((operandEncoding saved).encode state)))
        (clean_product saved multiplier outer outerMultiplier source canonical retained))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
