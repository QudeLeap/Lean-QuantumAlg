/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Blocks

/-!
# Scalar Fourier rows across chronological blocks

The original signed Fourier row and its incoming diagonal phase factor split
at any two consecutive bit blocks. Earlier measured output bits alter only
the later block's inherited phases. This is a pointwise identity for the
existing mathematical rows, including empty blocks; it constructs no circuit
or measurement and assumes no partner action.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

open QuantumAlg.MeasurementInstrument

private lemma scalar_phaseBasis_succ (n : Nat) (phases : Fin (n + 1) → ℂ)
    (head : Fin 2) (tail : Bits n) :
    phaseBasis (n + 1) phases (head, tail) =
      (if head = 0 then 1 else phases 0) *
        phaseBasis n (fun index => phases index.succ) tail := by
  simp only [phaseBasis, Fin.prod_univ_succ, tupleCoordinates_head,
    tupleCoordinates_tail]

private lemma scalar_phaseBasis_mul (n : Nat) (left right : Fin n → ℂ)
    (input : Bits n) :
    phaseBasis n (fun index => left index * right index) input =
      phaseBasis n left input * phaseBasis n right input := by
  unfold phaseBasis
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index _
  split <;> simp

private lemma scalar_fourierRows_succ (inverse : Bool) (n : Nat)
    (head bit : Fin 2) (output input : Bits n) :
    fourierRows inverse (n + 1) (head, output) (bit, input) =
      fourierRows inverse n output input *
        phaseBasis n (feedbackPhases inverse n head) input * Gate.HOp head bit := by
  exact phaseStage_entry Gate.HOp
    (fun branch => phaseBasis n (feedbackPhases inverse n branch))
    (fourierRows inverse n) head bit output input

private lemma scalar_row_succ (inverse : Bool) (n : Nat)
    (phases : Fin (n + 1) → ℂ) (head bit : Fin 2)
    (output input : Bits n) :
    fourierRows inverse (n + 1) (head, output) (bit, input) *
        phaseBasis (n + 1) phases (bit, input) =
      (fourierRows inverse n output input *
          phaseBasis n (updatedPhases inverse n phases head) input) *
        (Gate.HOp head bit * (if bit = 0 then 1 else phases 0)) := by
  rw [scalar_fourierRows_succ, scalar_phaseBasis_succ]
  change fourierRows inverse n output input *
      phaseBasis n (feedbackPhases inverse n head) input * Gate.HOp head bit *
        ((if bit = 0 then 1 else phases 0) *
          phaseBasis n (fun index => phases index.succ) input) =
      (fourierRows inverse n output input *
        phaseBasis n (fun index =>
          phases index.succ * feedbackPhases inverse n head index) input) *
        (Gate.HOp head bit * (if bit = 0 then 1 else phases 0))
  rw [scalar_phaseBasis_mul]
  ring

private lemma scalar_row_zero (inverse : Bool) (phases : Fin 0 → ℂ)
    (output input : Bits 0) :
    fourierRows inverse 0 output input * phaseBasis 0 phases input = 1 := by
  cases output
  cases input
  simp [fourierRows, coherent, phaseBasis]

/-- The complete original Fourier coefficient splits after any measured prefix.
The suffix receives exactly the inherited phase family of that prefix. -/
lemma qftPartner_fourierRows_phaseBasis_blocks (inverse : Bool) :
    ∀ (headCount tailCount : Nat)
      (phases : Fin (tailCount + headCount) → ℂ)
      (frontOutput frontInput : Bits headCount)
      (tailOutput tailInput : Bits tailCount),
      fourierRows inverse (tailCount + headCount)
          (blockBits headCount tailCount frontOutput tailOutput)
          (blockBits headCount tailCount frontInput tailInput) *
        phaseBasis (tailCount + headCount) phases
          (blockBits headCount tailCount frontInput tailInput) =
      (fourierRows inverse tailCount tailOutput tailInput *
          phaseBasis tailCount
            (suffixPhases inverse headCount tailCount phases frontOutput) tailInput) *
        (fourierRows inverse headCount frontOutput frontInput *
          phaseBasis headCount (prefixFamily tailCount headCount phases) frontInput) := by
  intro headCount
  induction headCount with
  | zero =>
      intro tailCount phases frontOutput frontInput tailOutput tailInput
      cases frontOutput
      cases frontInput
      simp only [blockBits, suffixPhases, Nat.add_zero]
      have empty : fourierRows inverse 0 PUnit.unit PUnit.unit *
          phaseBasis 0 (prefixFamily tailCount 0 phases) PUnit.unit = 1 :=
        scalar_row_zero inverse _ _ _
      simp only [empty, mul_one]
  | succ headCount ih =>
      intro tailCount phases frontOutput frontInput tailOutput tailInput
      rcases frontOutput with ⟨headOutput, restOutput⟩
      rcases frontInput with ⟨headInput, restInput⟩
      change
        fourierRows inverse (tailCount + headCount + 1)
            (headOutput, blockBits headCount tailCount restOutput tailOutput)
            (headInput, blockBits headCount tailCount restInput tailInput) *
          phaseBasis (tailCount + headCount + 1) phases
            (headInput, blockBits headCount tailCount restInput tailInput) =
        (fourierRows inverse tailCount tailOutput tailInput *
          phaseBasis tailCount
            (suffixPhases inverse headCount tailCount
              (updatedPhases inverse (tailCount + headCount) phases headOutput)
              restOutput) tailInput) *
          (fourierRows inverse (headCount + 1)
              (headOutput, restOutput) (headInput, restInput) *
            phaseBasis (headCount + 1)
              (prefixFamily tailCount (headCount + 1) phases)
              (headInput, restInput))
      rw [scalar_row_succ inverse (tailCount + headCount) phases]
      rw [ih tailCount
        (updatedPhases inverse (tailCount + headCount) phases headOutput)
        restOutput restInput tailOutput tailInput]
      rw [scalar_row_succ inverse headCount
        (prefixFamily tailCount (headCount + 1) phases)]
      have phasePrefix :
          prefixFamily tailCount headCount
              (updatedPhases inverse (tailCount + headCount) phases headOutput) =
            updatedPhases inverse headCount
              (prefixFamily tailCount (headCount + 1) phases) headOutput := rfl
      rw [phasePrefix]
      have headPhase : prefixFamily tailCount (headCount + 1) phases 0 = phases 0 := rfl
      rw [headPhase]
      ring

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
