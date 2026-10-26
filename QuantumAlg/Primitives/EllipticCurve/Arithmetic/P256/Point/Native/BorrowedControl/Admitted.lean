/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl.Inactive

/-!
# The same actual arithmetic on coherent active and inactive labels

Canonical arithmetic inputs are required only on active labels. Inactive
labels retain arbitrary original binary words. One basis equation for the
same actual body extends linearly to arbitrary correlated Reference families;
the selector is never replaced by a classical probabilistic mixture.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

namespace BorrowedControl

noncomputable section

private lemma admitted_cases {Result : Type} (actual expected : Result) (selected : Bool)
    (Premise : Prop) (admitted : selected = true → Premise)
    (active : Premise → actual = expected) (inactive : selected = false → actual = expected) :
    actual = expected := by
  cases selected with
  | false => exact inactive rfl
  | true => exact active (admitted rfl)

private lemma target_congr (ports : PortAssignment) (source multiplier : Word)
    (retained : Placement.Rest ports) {initial final : Word} (same : initial = final) :
    ket (arithmeticState ports source initial multiplier retained) =
      ket (arithmeticState ports source final multiplier retained) :=
  congrArg (fun word : Word => ket (arithmeticState ports source word multiplier retained)) same

private lemma product_false (source multiplier : Word) :
    Horner.productWord source multiplier false = Horner.zeroWord := by
  apply Fin.ext
  rfl

lemma cleanProgram_admitted (ports : PortAssignment) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word)
    (retained : Placement.Rest ports)
    (sourceAdmitted : (controlBit ports).get retained = true → Canonical source) :
    (cleanProgram ports choice).applyNormalized environment
        (ket (arithmeticState ports source Horner.zeroWord multiplier retained)) =
      ket (arithmeticState ports source
        (Horner.productWord source
          ((quantumMultiplier ports choice).value source (multiplier, retained))
          ((controlBit ports).get retained)) multiplier retained) := by
  apply admitted_cases _ _ ((controlBit ports).get retained) _
  · exact sourceAdmitted
  · intro canonical
    exact cleanProgram_canonical ports choice environment source multiplier canonical retained
  · intro enabled
    have output : Horner.productWord source
        ((quantumMultiplier ports choice).value source (multiplier, retained))
        ((controlBit ports).get retained) = Horner.zeroWord := by
      rw [enabled]
      exact product_false _ _
    exact (cleanProgram_inactive ports choice environment source multiplier retained
      enabled).trans (target_congr ports source multiplier retained output).symm

lemma macProgram_admitted (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (retained : Placement.Rest ports)
    (sourceAdmitted : (controlBit ports).get retained = true → Canonical source)
    (targetAdmitted : (controlBit ports).get retained = true → Canonical target) :
    (macProgram ports).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source
        (Accumulate.accumulatedWord source multiplier target ((controlBit ports).get retained))
        multiplier retained) := by
  apply admitted_cases _ _ ((controlBit ports).get retained)
    (Canonical source ∧ Canonical target)
  · intro enabled
    exact ⟨sourceAdmitted enabled, targetAdmitted enabled⟩
  · intro canonical
    exact macProgram_canonical ports environment source target multiplier
      canonical.1 canonical.2 retained
  · intro enabled
    have output : Accumulate.accumulatedWord source multiplier target
        ((controlBit ports).get retained) = target := by
      rw [enabled]
      rfl
    exact (macProgram_inactive ports environment source target multiplier retained enabled).trans
      (target_congr ports source multiplier retained output).symm

lemma inverseMacProgram_admitted (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (retained : Placement.Rest ports)
    (sourceAdmitted : (controlBit ports).get retained = true → Canonical source)
    (targetAdmitted : (controlBit ports).get retained = true → Canonical target) :
    (inverseMacProgram ports).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source
        (Accumulate.Inverse.differenceWord source multiplier target
          ((controlBit ports).get retained)) multiplier retained) := by
  apply admitted_cases _ _ ((controlBit ports).get retained)
    (Canonical source ∧ Canonical target)
  · intro enabled
    exact ⟨sourceAdmitted enabled, targetAdmitted enabled⟩
  · intro canonical
    exact inverseMacProgram_canonical ports environment source target multiplier
      canonical.1 canonical.2 retained
  · intro enabled
    have output : Accumulate.Inverse.differenceWord source multiplier target
        ((controlBit ports).get retained) = target := by
      rw [enabled]
      rfl
    exact (inverseMacProgram_inactive ports environment source target multiplier retained
      enabled).trans
      (target_congr ports source multiplier retained output).symm

lemma subtractSquareProgram_admitted (environment : OracleModel.empty.Interpretation)
    (source target : Word) (retained : Placement.Rest squarePorts)
    (sourceAdmitted : (controlBit squarePorts).get retained = true → Canonical source)
    (targetAdmitted : (controlBit squarePorts).get retained = true → Canonical target) :
    subtractSquareProgram.applyNormalized environment
        (ket (arithmeticState squarePorts source target Horner.zeroWord retained)) =
      ket (arithmeticState squarePorts source
        (Accumulate.Inverse.differenceWord source source target
          ((controlBit squarePorts).get retained)) Horner.zeroWord retained) := by
  apply admitted_cases _ _ ((controlBit squarePorts).get retained)
    (Canonical source ∧ Canonical target)
  · intro enabled
    exact ⟨sourceAdmitted enabled, targetAdmitted enabled⟩
  · intro canonical
    exact subtractSquareProgram_canonical environment source target
      canonical.1 canonical.2 retained
  · intro enabled
    have output : Accumulate.Inverse.differenceWord source source target
        ((controlBit squarePorts).get retained) = target := by
      rw [enabled]
      rfl
    exact (subtractSquareProgram_inactive environment source target retained enabled).trans
      (target_congr squarePorts source Horner.zeroWord retained output).symm

/-- All original word, work, selector, caller and external-Reference correlations are retained. -/
lemma cleanProgram_admitted_reference (ports : PortAssignment) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source multiplier : Index → Word)
    (retained : Index → Placement.Rest ports)
    (canonical : ∀ index, (controlBit ports).get (retained index) = true → Canonical (source index))
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
  coherent_of_basis _ environment _ _ (fun index => cleanProgram_admitted ports choice
    environment (source index) (multiplier index) (retained index) (canonical index))
    reference amplitude

lemma macProgram_admitted_reference (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (retained : Index → Placement.Rest ports)
    (sourceCanonical : ∀ index, (controlBit ports).get (retained index) = true →
      Canonical (source index))
    (targetCanonical : ∀ index, (controlBit ports).get (retained index) = true →
      Canonical (target index)) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator (macProgram ports) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Accumulate.accumulatedWord (source index) (multiplier index) (target index)
          ((controlBit ports).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => macProgram_admitted ports environment
    (source index) (target index) (multiplier index) (retained index)
    (sourceCanonical index) (targetCanonical index)) reference amplitude

lemma inverseMacProgram_admitted_reference (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (retained : Index → Placement.Rest ports)
    (sourceCanonical : ∀ index, (controlBit ports).get (retained index) = true →
      Canonical (source index))
    (targetCanonical : ∀ index, (controlBit ports).get (retained index) = true →
      Canonical (target index)) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (inverseMacProgram ports) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Accumulate.Inverse.differenceWord (source index) (multiplier index) (target index)
          ((controlBit ports).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => inverseMacProgram_admitted ports
    environment (source index) (target index) (multiplier index) (retained index)
    (sourceCanonical index) (targetCanonical index)) reference amplitude

/-- The actual original A copy word is cleared beside arbitrary accumulator and Ref correlations. -/
lemma subtractSquareProgram_admitted_reference
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target : Index → Word)
    (retained : Index → Placement.Rest squarePorts)
    (sourceCanonical : ∀ index, (controlBit squarePorts).get (retained index) = true →
      Canonical (source index))
    (targetCanonical : ∀ index, (controlBit squarePorts).get (retained index) = true →
      Canonical (target index)) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (subtractSquareProgram) environment Reference)
        (referenceVector (fun index => arithmeticState squarePorts (source index) (target index)
          Horner.zeroWord (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState squarePorts (source index)
        (Accumulate.Inverse.differenceWord (source index) (source index) (target index)
          ((controlBit squarePorts).get (retained index)))
        Horner.zeroWord (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => subtractSquareProgram_admitted
    environment (source index) (target index) (retained index)
    (sourceCanonical index) (targetCanonical index)) reference amplitude

end

end BorrowedControl

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
