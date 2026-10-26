/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Reference

/-!
# Complete original point-frame action of quantum table-word addition

The loaded A word and every original complementary system are retained.
The real whole-digit selector F560 controls the target addition and the
original three arithmetic flags are restored. Inactive sectors permit
arbitrary binary operands; coherent mixed sectors retain all references.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

noncomputable section

open EncodedBit Horner

private lemma raw_apply {Saved : Type} (saved : BinaryLabelEncoding Saved)
    (selector : EncodedBit saved) (environment : OracleModel.empty.Interpretation)
    (source target : Word) (retained : Saved)
    (sourceCanonical : selector.get retained = true → Canonical source)
    (targetCanonical : selector.get retained = true → Canonical target) :
    (program saved selector).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, target), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, if selector.get retained then ModularAddition.modularSumWord source target
            else target), false), (false, false)), retained))) :=
  ((program_realizes saved selector environment).apply_encoded_ket _).trans
    (congrArg (fun state => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((operandEncoding saved).encode state)))
        (gates_admitted saved selector source target retained sourceCanonical targetCanonical))

namespace Placed

/-- The same loaded A word is the source; X is the target and all of Y is retained. -/
def horizontal : PortAssignment where
  source := .work1
  target := .work2
  multiplier := .numerator
  source_target := by decide
  source_multiplier := by decide
  target_multiplier := by decide

/-- The same loaded A word is the source; Y is the target and all of X is retained. -/
def vertical : PortAssignment where
  source := .work1
  target := .numerator
  multiplier := .work2
  source_target := by decide
  source_multiplier := by decide
  target_multiplier := by decide

/-- The real F bit resides in the complete retained component of either assignment. -/
def selector (ports : PortAssignment) : EncodedBit (Placement.savedEncoding ports) :=
  Native.BorrowedControl.outerBit ports

/-- The actual selected addition on the existing complete point bank, with no allocation. -/
def program (ports : PortAssignment) : Native.Circuit :=
  (Placement.layout ports).place
    (Offset.program (Placement.savedEncoding ports) (selector ports))

/-- Complete exact basis action includes source A, the third word, all flags and all Rest. -/
lemma program_apply (ports : PortAssignment) (environment : OracleModel.empty.Interpretation)
    (source target third : Word) (retained : Placement.Rest ports)
    (sourceCanonical : (Native.BorrowedControl.controlBit ports).get retained = true →
      Canonical source)
    (targetCanonical : (Native.BorrowedControl.controlBit ports).get retained = true →
      Canonical target) :
    (program ports).applyNormalized environment
        (Native.ket (Native.arithmeticState ports source target third retained)) =
      Native.ket (Native.arithmeticState ports source
        (if (Native.BorrowedControl.controlBit ports).get retained then
          ModularAddition.modularSumWord source target else target) third retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (raw_apply (Placement.savedEncoding ports) (selector ports) environment source target
      (third, retained) sourceCanonical targetCanonical)

/-- The same actual native body preserves arbitrary Reference and mixed coherent F sectors. -/
lemma program_reference (ports : PortAssignment) (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (source target third : Index → Word)
    (retained : Index → Placement.Rest ports)
    (sourceCanonical : ∀ index, (Native.BorrowedControl.controlBit ports).get (retained index) =
      true → Canonical (source index))
    (targetCanonical : ∀ index, (Native.BorrowedControl.controlBit ports).get (retained index) =
      true → Canonical (target index)) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (Native.referenceOperator (program ports) environment Reference)
        (Native.referenceVector (fun index => Native.arithmeticState ports (source index)
          (target index) (third index) (retained index)) reference amplitude) =
      Native.referenceVector (fun index => Native.arithmeticState ports (source index)
        (if (Native.BorrowedControl.controlBit ports).get (retained index) then
          ModularAddition.modularSumWord (source index) (target index) else target index)
        (third index) (retained index)) reference amplitude :=
  Native.coherent_of_basis _ environment _ _ (fun index => program_apply ports environment
    (source index) (target index) (third index) (retained index)
    (sourceCanonical index) (targetCanonical index)) reference amplitude

end Placed

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset
