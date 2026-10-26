/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Scalars
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Windows

/-!
# Scalar Fourier rows across symbolic chronological windows

The exact two-block scalar cut composes over any finite list of window widths.
The suffix factor receives the phases accumulated from the actual preceding
outcome block. Widths remain symbolic, including empty windows. This is a
mathematical row identity and does not construct a measured circuit.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

/-- The ordered scalar factors of the original Fourier row and incoming phases. -/
def windowScalar (inverse : Bool) : (widths : List Nat) →
    (Fin (windowWidth widths) → ℂ) → WindowBits widths → WindowBits widths → ℂ
  | [], _, _, _ => 1
  | head :: tail, phases, output, input =>
      windowScalar inverse tail
          (suffixPhases inverse head (windowWidth tail) phases output.1)
          output.2 input.2 *
        (fourierRows inverse head output.1 input.1 *
          phaseBasis head (prefixFamily (windowWidth tail) head phases) input.1)

/-- Every symbolic window factor is the same full Fourier row coefficient. -/
lemma qftPartner_windowScalar (inverse : Bool) :
    ∀ (widths : List Nat) (phases : Fin (windowWidth widths) → ℂ)
      (output input : WindowBits widths),
      windowScalar inverse widths phases output input =
        fourierRows inverse (windowWidth widths)
          (windowBits widths output) (windowBits widths input) *
          phaseBasis (windowWidth widths) phases (windowBits widths input) := by
  intro widths
  induction widths with
  | nil =>
      intro phases output input
      cases output
      cases input
      change (1 : ℂ) = fourierRows inverse 0 PUnit.unit PUnit.unit *
        phaseBasis 0 phases PUnit.unit
      simp [fourierRows, coherent, phaseBasis]
  | cons head tail ih =>
      intro phases output input
      change
        windowScalar inverse tail
            (suffixPhases inverse head (windowWidth tail) phases output.1)
            output.2 input.2 *
          (fourierRows inverse head output.1 input.1 *
            phaseBasis head (prefixFamily (windowWidth tail) head phases) input.1) =
        fourierRows inverse (windowWidth tail + head)
            (blockBits head (windowWidth tail) output.1 (windowBits tail output.2))
            (blockBits head (windowWidth tail) input.1 (windowBits tail input.2)) *
          phaseBasis (windowWidth tail + head) phases
            (blockBits head (windowWidth tail) input.1 (windowBits tail input.2))
      rw [ih]
      exact (qftPartner_fourierRows_phaseBasis_blocks inverse head
        (windowWidth tail) phases output.1 input.1
        (windowBits tail output.2) (windowBits tail input.2)).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
