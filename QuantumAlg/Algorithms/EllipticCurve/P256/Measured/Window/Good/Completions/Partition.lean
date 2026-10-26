/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions

/-!
# Partition of the same complete coherent weights by the next retained block

Appending one literal outcome partitions the original complete physical
outputs. The terminal vector and event keep their original weights. The
identity uses no distribution on prefix outcomes and no division by a
prefix probability; it also applies to zero or empty good components.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum}

private lemma sum_first_match {Outcome : Type} [Fintype Outcome]
    (first other accepted : Prop) (chosen : Outcome) (weight : ℝ)
    {selected : (outcome : Outcome) → Decidable (((first ∧ chosen = outcome) ∧ other) ∧ accepted)}
    {matched : Decidable ((first ∧ other) ∧ accepted)} :
    (∑ outcome : Outcome,
      @ite ℝ (((first ∧ chosen = outcome) ∧ other) ∧ accepted) (selected outcome) weight 0) =
      @ite ℝ ((first ∧ other) ∧ accepted) matched weight 0 := by
  classical
  by_cases firstProof : first
  · by_cases otherProof : other
    · by_cases acceptedProof : accepted
      · simp [firstProof, otherProof, acceptedProof]
      · simp [firstProof, otherProof, acceptedProof]
    · simp [firstProof, otherProof]
  · simp [firstProof]

private lemma sum_second_match {Outcome : Type} [Fintype Outcome]
    (first other accepted : Prop) (chosen : Outcome) (weight : ℝ)
    {selected : (outcome : Outcome) → Decidable ((first ∧ other ∧ chosen = outcome) ∧ accepted)}
    {matched : Decidable ((first ∧ other) ∧ accepted)} :
    (∑ outcome : Outcome,
      @ite ℝ ((first ∧ other ∧ chosen = outcome) ∧ accepted) (selected outcome) weight 0) =
      @ite ℝ ((first ∧ other) ∧ accepted) matched weight 0 := by
  classical
  by_cases firstProof : first
  · by_cases otherProof : other
    · by_cases acceptedProof : accepted
      · simp [firstProof, otherProof, acceptedProof]
      · simp [firstProof, otherProof, acceptedProof]
    · simp [firstProof, otherProof]
  · simp [firstProof]

/-- Appending the next first-stream block counts every original completion exactly once. -/
lemma completionWeight_first_append (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (head tail second : Nat)
    (within : tail + head ≤ 260) (secondBound : second ≤ 260)
    (before : Store ctx) (after : Bits tail → Store ctx)
    (firstReads : ∀ outcome,
      Feedback.retainedPrefix parameters.results.cells 0 (tail + head) within
          (after outcome) =
        Partner.blockBits head tail
          (Feedback.retainedPrefix parameters.results.cells 0 head
            ((Nat.le_add_left head tail).trans within) before) outcome)
    (otherReads : ∀ outcome,
      Feedback.retainedPrefix parameters.results.cells 1 second secondBound (after outcome) =
        Feedback.retainedPrefix parameters.results.cells 1 second secondBound before)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    (∑ outcome : Bits tail,
      completionWeight parameters I (tail + head) second within secondBound
        (after outcome) amplitude reference event) =
      completionWeight parameters I head second
        ((Nat.le_add_left head tail).trans within) secondBound
        before amplitude reference event := by
  classical
  unfold completionWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro complete _
  simp only [outputCompatible, firstReads, otherReads, Partner.prefixBits_append_eq_iff]
  exact sum_first_match
    (Partner.prefixBits head ((Nat.le_add_left head tail).trans within)
      ((binaryEquiv 260).symm complete.1) =
        Feedback.retainedPrefix parameters.results.cells 0 head
          ((Nat.le_add_left head tail).trans within) before)
    (Partner.prefixBits second secondBound ((binaryEquiv 260).symm complete.2) =
      Feedback.retainedPrefix parameters.results.cells 1 second secondBound before)
    (event complete = true)
    (Partner.segmentBits head tail within ((binaryEquiv 260).symm complete.1)) _

/-- Appending the next second-stream block counts the same original completions once. -/
lemma completionWeight_second_append (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (first head tail : Nat)
    (firstBound : first ≤ 260) (within : tail + head ≤ 260)
    (before : Store ctx) (after : Bits tail → Store ctx)
    (firstReads : ∀ outcome,
      Feedback.retainedPrefix parameters.results.cells 0 first firstBound (after outcome) =
        Feedback.retainedPrefix parameters.results.cells 0 first firstBound before)
    (secondReads : ∀ outcome,
      Feedback.retainedPrefix parameters.results.cells 1 (tail + head) within
          (after outcome) =
        Partner.blockBits head tail
          (Feedback.retainedPrefix parameters.results.cells 1 head
            ((Nat.le_add_left head tail).trans within) before) outcome)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    (∑ outcome : Bits tail,
      completionWeight parameters I first (tail + head) firstBound within
        (after outcome) amplitude reference event) =
      completionWeight parameters I first head firstBound
        ((Nat.le_add_left head tail).trans within) before amplitude reference event := by
  classical
  unfold completionWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro complete _
  simp only [outputCompatible, firstReads, secondReads, Partner.prefixBits_append_eq_iff]
  exact sum_second_match
    (Partner.prefixBits first firstBound ((binaryEquiv 260).symm complete.1) =
      Feedback.retainedPrefix parameters.results.cells 0 first firstBound before)
    (Partner.prefixBits head ((Nat.le_add_left head tail).trans within)
      ((binaryEquiv 260).symm complete.2) =
        Feedback.retainedPrefix parameters.results.cells 1 head
          ((Nat.le_add_left head tail).trans within) before)
    (event complete = true)
    (Partner.segmentBits head tail within ((binaryEquiv 260).symm complete.2)) _

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
