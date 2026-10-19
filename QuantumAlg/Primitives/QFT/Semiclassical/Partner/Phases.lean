/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import all QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Primitives.QFT.Mathematics.PhaseFactors
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Util.Complex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Per-wire feedback factors for an arbitrary coherent partner

Source-only candidate: no Lean acceptance is claimed. The scalar factors below
are the literal positive or negative native Fourier phase angles. Their product
is the already established diagonal feedback of the coherent source. Physical
outcomes stay in leading-wire order; no output SWAP is implicit.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

open QuantumAlg.MeasurementInstrument
open scoped BigOperators

/-- The diagonal scalar selected by the physical bits of a control bank. -/
public def phaseBasis (n : Nat) (phases : Fin n → ℂ) (input : Bits n) : ℂ :=
  ∏ index : Fin n, if tupleCoordinates n input index = 0 then 1 else phases index

private lemma phaseBasis_zero (phases : Fin 0 → ℂ) (input : Bits 0) :
    phaseBasis 0 phases input = 1 := by
  simp [phaseBasis]

private lemma phaseBasis_succ (n : Nat) (phases : Fin (n + 1) → ℂ)
    (head : Fin 2) (tail : Bits n) :
    phaseBasis (n + 1) phases (head, tail) =
      (if head = 0 then 1 else phases 0) *
        phaseBasis n (fun index => phases index.succ) tail := by
  simp only [phaseBasis, Fin.prod_univ_succ, tupleCoordinates_head,
    tupleCoordinates_tail]

private lemma phaseBasis_one (n : Nat) (input : Bits n) :
    phaseBasis n (fun _ => 1) input = 1 := by
  simp [phaseBasis]

private lemma phaseBasis_mul (n : Nat) (left right : Fin n → ℂ) (input : Bits n) :
    phaseBasis n (fun index => left index * right index) input =
      phaseBasis n left input * phaseBasis n right input := by
  unfold phaseBasis
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index _
  split <;> simp

private lemma phaseBasis_star (n : Nat) (phases : Fin n → ℂ) (input : Bits n) :
    phaseBasis n (fun index => star (phases index)) input =
      star (phaseBasis n phases input) := by
  simp only [phaseBasis, star_prod]
  apply Finset.prod_congr rfl
  intro index _
  split <;> simp

/-- One phase leaf, with exactly the sign used by the native Fourier schedule. -/
public def rotation (inverse : Bool) (offset : Nat) : ℂ :=
  Complex.exp (((if inverse then -(Source.phaseAngle offset)
    else Source.phaseAngle offset) : ℂ) * Complex.I)

/-- A measured head bit chooses the phase on each later physical control. -/
public def feedbackPhases (inverse : Bool) (n : Nat) (head : Fin 2) : Fin n → ℂ :=
  fun offset => if head = 1 then rotation inverse offset.val else 1

private lemma rotation_negative (offset : Nat) :
    rotation true offset = star (rotation false offset) := by
  simp [rotation, conj_exp_I]

private lemma tuple_bit (n : Nat) (input : Bits n) (index : Fin n) :
    (binaryEquiv n input).val.testBit index.rev.val =
      finTwoEquiv (tupleCoordinates n input index) := by
  have actual := BinaryBasis.bigEndianEquiv_bit n (tupleCoordinates n input) index
  simpa only [tupleCoordinates, Equiv.apply_symm_apply] using actual

private lemma positive_factor (n : Nat) (input : Bits n) (index : Fin n) :
    (if tupleCoordinates n input index = 0 then 1 else rotation false index.val) =
      qftPhaseFactorAt n index (qftPairEquiv n (1, binaryEquiv n input)) := by
  rw [qftPhaseFactorAt_eq_omega_pow, qftPairEquiv_testBit_high,
    qftPairEquiv_testBit_low, tuple_bit]
  have angle : rotation false index.val =
      ω (n + 1) ^ (2 ^ index.rev.val) := by
    simpa only [rotation, Bool.false_eq_true, ↓reduceIte,
      Source.phaseAngle, qftPhaseAngle] using qftPhaseAngle_exp_eq_omega_pow n index
  generalize tupleCoordinates n input index = bit
  fin_cases bit <;> simp [angle, finTwoEquiv]

private lemma phaseBasis_positive (n : Nat) (input : Bits n) :
    phaseBasis n (fun index => rotation false index.val) input =
      ω (n + 1) ^ (binaryEquiv n input).val := by
  unfold phaseBasis
  simp_rw [positive_factor]
  have source := qftPhaseLayerFactorPrefix_eq_prod n n le_rfl
    (qftPairEquiv n (1, binaryEquiv n input))
  have cast (index : Fin n) :
      (⟨index.val, lt_of_lt_of_le index.isLt le_rfl⟩ : Fin n) = index := Fin.ext rfl
  simp only [cast] at source
  rw [← source, qftPhaseLayerFactor_eq, qftPairEquiv_testBit_high,
    qftPairEquiv_mod_tail]
  simp

/-- Native per-wire phases have precisely the source's selected feedback diagonal. -/
public lemma qftPartner_phaseBasis_feedback (inverse : Bool) (n : Nat)
    (head : Fin 2) (input : Bits n) :
    phaseBasis n (feedbackPhases inverse n head) input =
      if head = 1 then
        (if inverse then star (ω (n + 1) ^ (binaryEquiv n input).val)
          else ω (n + 1) ^ (binaryEquiv n input).val)
      else 1 := by
  by_cases selected : head = 1
  · subst head
    cases inverse
    · change phaseBasis n (fun index => rotation false index.val) input =
        ω (n + 1) ^ (binaryEquiv n input).val
      exact phaseBasis_positive n input
    · change phaseBasis n (fun index => rotation true index.val) input =
        star (ω (n + 1) ^ (binaryEquiv n input).val)
      simp_rw [rotation_negative]
      exact (phaseBasis_star n (fun index => rotation false index.val) input).trans
        (congrArg star (phaseBasis_positive n input))
  · rw [if_neg selected]
    change phaseBasis n (fun offset =>
      if head = 1 then rotation inverse offset.val else 1) input = 1
    simp only [if_neg selected]
    exact phaseBasis_one n input

/-- Fourier recursion built from the same literal selected phase leaves. -/
def feedbackMatrix (inverse : Bool) (n : Nat) (head : Fin 2) :
    Matrix (Bits n) (Bits n) ℂ :=
  Matrix.diagonal (phaseBasis n (feedbackPhases inverse n head))

private lemma feedbackMatrix_positive (n : Nat) (head : Fin 2) :
    feedbackMatrix false n head = feedback n head := by
  ext row column
  simp only [feedbackMatrix, feedback, Matrix.diagonal_apply,
    qftPartner_phaseBasis_feedback, Bool.false_eq_true, ↓reduceIte]

private lemma feedbackMatrix_negative (n : Nat) (head : Fin 2) :
    feedbackMatrix true n head = conjugate (feedback n head) := by
  ext row column
  change (if row = column then phaseBasis n (feedbackPhases true n head) row else 0) =
    star (if row = column then
      (if head = 1 then ω (n + 1) ^ (binaryEquiv n row).val else 1) else 0)
  by_cases same : row = column
  · rw [if_pos same, if_pos same, qftPartner_phaseBasis_feedback]
    by_cases selected : head = 1
    · rw [if_pos selected, if_pos selected]
      rfl
    · rw [if_neg selected, if_neg selected]
      exact (star_one ℂ).symm
  · rw [if_neg same, if_neg same]
    exact (star_zero ℂ).symm

/-- The physical output row of either signed no-SWAP Fourier schedule. -/
public def fourierRows (inverse : Bool) (n : Nat) : Matrix (Bits n) (Bits n) ℂ :=
  coherent Gate.HOp (feedbackMatrix inverse) n

/-- Positive phases recover the existing actual coherent no-SWAP source. -/
public lemma qftPartner_fourierRows_source (n : Nat) :
    fourierRows false n = sourceMatrix OracleModel.empty n OracleModel.emptyInterpretation := by
  have feedback_eq : feedbackMatrix false = feedback := by
    funext width head
    exact feedbackMatrix_positive width head
  rw [fourierRows, feedback_eq, qftSemiclassical_coherent_eq_sourceMatrix]

/-- Negative phases conjugate the same ordered source, retaining physical output order. -/
public lemma qftPartner_fourierRows_negative (n : Nat) :
    fourierRows true n
      = conjugate (sourceMatrix OracleModel.empty n OracleModel.emptyInterpretation) := by
  have feedback_eq : feedbackMatrix true = fun width head => conjugate (feedback width head) :=
    by funext width head; exact feedbackMatrix_negative width head
  rw [fourierRows, feedback_eq]
  have real : conjugate (Gate.HOp : Matrix (Fin 2) (Fin 2) ℂ) = Gate.HOp := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [conjugate, Gate.HOp, UnitaryOperator.coe_ofMatrix,
        NormalizedVector.star_invSqrt2]
  rw [← real, coherent_conjugate, qftSemiclassical_coherent_eq_sourceMatrix]

private lemma fourierRows_positive_entry (n : Nat) (output input : Bits n) :
    fourierRows false n output input =
      QFTOperator n (qftReverseBits n (binaryEquiv n output)) (binaryEquiv n input) := by
  rw [fourierRows]
  have feedback_eq : feedbackMatrix false = feedback := by
    funext width head
    exact feedbackMatrix_positive width head
  rw [feedback_eq]
  exact qftSemiclassical_coherent_entry n output input

/-- The first physical bit is still the least significant decoded frequency bit. -/
public lemma qftPartner_fourierRows_entry (inverse : Bool) (n : Nat) (output input : Bits n) :
    fourierRows inverse n output input =
      if inverse then
        ((QFTOperator n)⁻¹ : UnitaryOperator (Qubits n))
          (qftReverseBits n (binaryEquiv n output)) (binaryEquiv n input)
      else QFTOperator n (qftReverseBits n (binaryEquiv n output)) (binaryEquiv n input) :=
    by
  cases inverse
  · exact fourierRows_positive_entry n output input
  · rw [qftPartner_fourierRows_negative]
    change star (sourceMatrix OracleModel.empty n OracleModel.emptyInterpretation output input) = _
    rw [← qftPartner_fourierRows_source]
    rw [fourierRows_positive_entry]
    change star (QFTOperator n _ _) = star (QFTOperator n _ _)
    congr 1
    simp only [QFTOperator_entry, Nat.mul_comm]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
