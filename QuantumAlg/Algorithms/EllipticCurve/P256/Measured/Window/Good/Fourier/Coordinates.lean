/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Address.Equivalence
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Decode

/-!
# Exact original Fourier frequencies of complete chronological output pairs

Bit reversal changes only the output coordinate.
The two original exponent inputs use the existing width cast unchanged.
The coefficient identities reuse the certified full native Fourier rows.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window

/-- Decode each physical stream, then return to the unchanged original exponent width. -/
def decodedFrequency (I : DomainParameters.PublicKeyInstance) :
    Sampling.SourceRegister.Index ≃
      EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) :=
  (Equiv.prodCongr (qftReverseBitsPerm 260) (qftReverseBitsPerm 260)).trans
    (sourceBranchEquiv I).symm

/-- The original decoded frequency casts to exactly both reversed physical streams. -/
lemma sourceBranch_decodedFrequency (I : DomainParameters.PublicKeyInstance)
    (complete : Sampling.SourceRegister.Index) :
    sourceBranch I (decodedFrequency I complete) =
      (qftReverseBits 260 complete.1, qftReverseBits 260 complete.2) := by
  change sourceBranch I ((sourceBranchEquiv I).symm
    (qftReverseBits 260 complete.1, qftReverseBits 260 complete.2)) = _
  exact sourceBranchEquiv_inverse I _

private lemma fullRows_cast {before after : Nat} (widths : before = after)
    (inverse : Bool) (frequency source : Fin (2 ^ before)) :
    Partner.fullRows inverse after
        (Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths) frequency)
        ((binaryEquiv after).symm
          (Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths) source)) =
      Partner.fullRows inverse before frequency ((binaryEquiv before).symm source) := by
  cases widths
  rfl

private lemma physicalRow_decode (inverse : Bool) (width : Nat)
    (complete source : Fin (2 ^ width)) :
    Partner.fourierRows inverse width ((binaryEquiv width).symm complete)
        ((binaryEquiv width).symm source) =
      Partner.fullRows inverse width (qftReverseBits width complete)
        ((binaryEquiv width).symm source) := by
  rw [Partner.qftPartner_fullRows_physical]
  have decoded := Partner.qftPartner_frequencyBits_decode width
    ((binaryEquiv width).symm complete)
  rw [Equiv.apply_symm_apply] at decoded
  rw [decoded]

/-- The first physical full row is the same original-width native frequency row. -/
lemma completed_first_row (I : DomainParameters.PublicKeyInstance)
    (complete : Sampling.SourceRegister.Index)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    Partner.fourierRows true 260 ((binaryEquiv 260).symm complete.1)
        ((binaryEquiv 260).symm (sourceBranch I branch).1) =
      Partner.fullRows true (Cascade.exponentWidth I) (decodedFrequency I complete).1
        ((binaryEquiv (Cascade.exponentWidth I)).symm branch.1) := by
  have decoded := congrArg (fun source : Sampling.SourceRegister.Index => source.1)
    (sourceBranch_decodedFrequency I complete)
  exact (physicalRow_decode true 260 complete.1 (sourceBranch I branch).1).trans
    ((congrArg
      (fun frequency : Fin (2 ^ 260) => Partner.fullRows true 260 frequency
        ((binaryEquiv 260).symm (sourceBranch I branch).1)) decoded.symm).trans
      (fullRows_cast (before := Cascade.exponentWidth I) (after := 260)
        (Cascade.exponentWidth_eq_260 I) true (decodedFrequency I complete).1 branch.1))

/-- The second physical full row is the same original-width native frequency row. -/
lemma completed_second_row (I : DomainParameters.PublicKeyInstance)
    (complete : Sampling.SourceRegister.Index)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    Partner.fourierRows true 260 ((binaryEquiv 260).symm complete.2)
        ((binaryEquiv 260).symm (sourceBranch I branch).2) =
      Partner.fullRows true (Cascade.exponentWidth I) (decodedFrequency I complete).2
        ((binaryEquiv (Cascade.exponentWidth I)).symm branch.2) := by
  have decoded := congrArg (fun source : Sampling.SourceRegister.Index => source.2)
    (sourceBranch_decodedFrequency I complete)
  exact (physicalRow_decode true 260 complete.2 (sourceBranch I branch).2).trans
    ((congrArg
      (fun frequency : Fin (2 ^ 260) => Partner.fullRows true 260 frequency
        ((binaryEquiv 260).symm (sourceBranch I branch).2)) decoded.symm).trans
      (fullRows_cast (before := Cascade.exponentWidth I) (after := 260)
        (Cascade.exponentWidth_eq_260 I) true (decodedFrequency I complete).2 branch.2))

/-- Both decoded rows multiply the unchanged original admissible amplitude coherently. -/
lemma completedAmplitude_fullRows (I : DomainParameters.PublicKeyInstance)
    (complete : Sampling.SourceRegister.Index) (amplitude : GoodBranch I → ℂ)
    (branch : GoodBranch I) :
    completedAmplitude I complete amplitude branch = amplitude branch *
      (Partner.fullRows true (Cascade.exponentWidth I) (decodedFrequency I complete).1
          ((binaryEquiv (Cascade.exponentWidth I)).symm branch.val.1) *
        Partner.fullRows true (Cascade.exponentWidth I) (decodedFrequency I complete).2
          ((binaryEquiv (Cascade.exponentWidth I)).symm branch.val.2)) := by
  rw [completedAmplitude, completed_first_row, completed_second_row]

/-- Reading both final original streams gives the same frequencies as the existing decoder. -/
lemma decodedFrequency_stored {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Execution.Store ctx) :
    sourceBranch I (decodedFrequency I (storedComplete parameters store)) =
      (Decode.storedFrequency parameters.results.cells 0 store,
        Decode.storedFrequency parameters.results.cells 1 store) := by
  rw [sourceBranch_decodedFrequency]
  simp only [storedComplete, Feedback.retainedPrefix_all, Decode.storedFrequency]

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
