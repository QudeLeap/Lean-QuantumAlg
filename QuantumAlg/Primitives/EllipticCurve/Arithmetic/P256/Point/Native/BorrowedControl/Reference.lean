/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Reference

/-!
# Exact F560 arithmetic on complete coherent and external-reference families

Every original retained physical bit, including F, C/N/W, padding and all
unselected pool positions, keeps the same label and all its correlations.
The inactive clean-target theorem has no canonical-source premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

namespace BorrowedControl

noncomputable section

/-- All original word, work, selector, caller and external-Reference correlations are retained. -/
lemma cleanProgram_reference (ports : PortAssignment) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source multiplier : Index → Word)
    (canonical : ∀ index, Canonical (source index)) (retained : Index → Placement.Rest ports)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (cleanProgram ports choice) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) Horner.zeroWord
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Horner.productWord (source index)
          ((quantumMultiplier ports choice).value (source index) (multiplier index, retained index))
          ((controlBit ports).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => cleanProgram_canonical ports choice
    environment (source index) (multiplier index) (canonical index) (retained index))
    reference amplitude

lemma macProgram_reference (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index))
    (retained : Index → Placement.Rest ports) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator (macProgram ports) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Accumulate.accumulatedWord (source index) (multiplier index) (target index)
          ((controlBit ports).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => macProgram_canonical ports environment
    (source index) (target index) (multiplier index) (sourceCanonical index) (targetCanonical index)
    (retained index)) reference amplitude

lemma inverseMacProgram_reference (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index))
    (retained : Index → Placement.Rest ports) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (inverseMacProgram ports) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Accumulate.Inverse.differenceWord (source index) (multiplier index) (target index)
          ((controlBit ports).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => inverseMacProgram_canonical ports
    environment (source index) (target index) (multiplier index) (sourceCanonical index)
    (targetCanonical index) (retained index)) reference amplitude

/-- The actual original A copy word is cleared beside arbitrary accumulator and Ref correlations. -/
lemma subtractSquareProgram_reference
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target : Index → Word)
    (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index))
    (retained : Index → Placement.Rest squarePorts) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (subtractSquareProgram) environment Reference)
        (referenceVector (fun index => arithmeticState squarePorts (source index) (target index)
          Horner.zeroWord (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState squarePorts (source index)
        (Accumulate.Inverse.differenceWord (source index) (source index) (target index)
          ((controlBit squarePorts).get (retained index)))
        Horner.zeroWord (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => subtractSquareProgram_canonical
    environment (source index) (target index) (sourceCanonical index) (targetCanonical index)
    (retained index)) reference amplitude

/-- Inactive coherent/reference families admit arbitrary original source and multiplier labels. -/
lemma cleanProgram_inactive_reference (ports : PortAssignment) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source multiplier : Index → Word)
    (retained : Index → Placement.Rest ports)
    (disabled : ∀ index, (controlBit ports).get (retained index) = false)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator (cleanProgram ports choice) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) Horner.zeroWord
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index) Horner.zeroWord
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _
    (fun index => cleanProgram_inactive ports choice environment (source index) (multiplier index)
      (retained index) (disabled index)) reference amplitude

end

end BorrowedControl

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
