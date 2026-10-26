/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.State
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Fourier.Stream
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Completion

/-!
# Original complete Fourier outputs extending the current actual record

The continuation sum ranges over complete physical output tuples whose
prefixes match the literal retained Store. Each weight is the squared norm
of one complete coherent terminal vector with both original Fourier rows.
No prefix probability is divided out. An empty or zero component keeps its
original mass, and no independence of output bits is assumed.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

attribute [local irreducible] branchGood prefixAffine sourceBranch

private lemma pair_equiv_eq_iff {Source Output : Type} (equivalence : Output ≃ Source)
    (source : Source × Source) (first last : Output) :
    (equivalence.symm source.1 = first ∧ equivalence.symm source.2 = last) ↔
      source = (equivalence first, equivalence last) := by
  rw [equivalence.symm_apply_eq, equivalence.symm_apply_eq]
  constructor
  · rintro ⟨firstEq, lastEq⟩
    exact Prod.ext firstEq lastEq
  · intro same
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- Both original full Fourier rows multiply the same complete admissible source amplitude. -/
def completedAmplitude (I : DomainParameters.PublicKeyInstance)
    (complete : Sampling.SourceRegister.Index) (amplitude : GoodBranch I → ℂ) :
    GoodBranch I → ℂ :=
  fun branch => amplitude branch *
    (Partner.fourierRows true 260 ((binaryEquiv 260).symm complete.1)
        ((binaryEquiv 260).symm (sourceBranch I branch.val).1) *
      Partner.fourierRows true 260 ((binaryEquiv 260).symm complete.2)
        ((binaryEquiv 260).symm (sourceBranch I branch.val).2))

/-- The same original amplitude with precisely the two already retained Fourier rows. -/
def prefixAmplitude {ctx : RuntimeCtx .quantum} (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (first second : Nat) (firstBound : first ≤ 260) (secondBound : second ≤ 260)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ) : GoodBranch I → ℂ :=
  fun branch => amplitude branch *
    (Sampling.streamFourierRow parameters 0 first firstBound store
        (sourceBranch I branch.val).1 *
      Sampling.streamFourierRow parameters 1 second secondBound store
        (sourceBranch I branch.val).2)

/-- No output prefix changes any original branch amplitude before the first actual window. -/
lemma prefixAmplitude_initial {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ) :
    prefixAmplitude parameters I 0 0 (Nat.zero_le 260) (Nat.zero_le 260) store amplitude =
      amplitude := by
  funext branch
  simp only [prefixAmplitude, Sampling.streamFourierRow_initial, mul_one]

/-- A complete original physical tuple extends exactly the two retained current prefixes. -/
def outputCompatible {ctx : RuntimeCtx .quantum} (parameters : Sampling.Parameters ctx)
    (first second : Nat) (firstBound : first ≤ 260) (secondBound : second ≤ 260)
    (store : Store ctx) (complete : Sampling.SourceRegister.Index) : Prop :=
  Partner.prefixBits first firstBound ((binaryEquiv 260).symm complete.1) =
      Feedback.retainedPrefix parameters.results.cells 0 first firstBound store ∧
    Partner.prefixBits second secondBound ((binaryEquiv 260).symm complete.2) =
      Feedback.retainedPrefix parameters.results.cells 1 second secondBound store

/-- Every original complete output extends both initially empty prefixes. -/
lemma outputCompatible_initial {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (store : Store ctx)
    (complete : Sampling.SourceRegister.Index) :
    outputCompatible parameters 0 0 (Nat.zero_le 260) (Nat.zero_le 260) store complete := by
  constructor <;> apply tupleCoordinates_injective 0 <;>
    funext position <;> exact Fin.elim0 position

/-- Complete-output weights retain all original coherent branch and Reference cross terms. -/
def completionWeight {ctx : RuntimeCtx .quantum} (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (first second : Nat) (firstBound : first ≤ 260) (secondBound : second ≤ 260)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) : ℝ :=
  ∑ complete : Sampling.SourceRegister.Index,
    if outputCompatible parameters first second firstBound secondBound store complete ∧
        event complete = true then
      ‖coherentPrefix parameters I 34 (by omega) 520
        (completedAmplitude I complete amplitude) reference‖ ^ 2 else 0

/-- At the original empty prefix, the sum retains every complete physical output. -/
lemma completionWeight_initial {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) :
    completionWeight parameters I 0 0 (Nat.zero_le 260) (Nat.zero_le 260)
        store amplitude reference event =
      ∑ complete : Sampling.SourceRegister.Index,
        if event complete = true then
          ‖coherentPrefix parameters I 34 (by omega) 520
            (completedAmplitude I complete amplitude) reference‖ ^ 2 else 0 := by
  simp only [completionWeight, outputCompatible_initial, true_and]

/-- The original complete physical output pair read from the two actual retained streams. -/
def storedComplete {ctx : RuntimeCtx .quantum} (parameters : Sampling.Parameters ctx)
    (store : Store ctx) : Sampling.SourceRegister.Index :=
  ((binaryEquiv 260)
      (Feedback.retainedPrefix parameters.results.cells 0 260 (Nat.le_refl 260) store),
    (binaryEquiv 260)
      (Feedback.retainedPrefix parameters.results.cells 1 260 (Nat.le_refl 260) store))

/-- The complete retained prefix has exactly both Fourier rows of that physical output pair. -/
lemma prefixAmplitude_terminal {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ) :
    prefixAmplitude parameters I 260 260 (Nat.le_refl 260) (Nat.le_refl 260) store amplitude =
      completedAmplitude I (storedComplete parameters store) amplitude := by
  funext branch
  simp only [prefixAmplitude, completedAmplitude, storedComplete,
    Sampling.streamFourierRow, Partner.prefixBits_all, Equiv.symm_apply_apply]

/-- A full retained prefix has exactly its one original complete physical tuple. -/
lemma outputCompatible_terminal {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (store : Store ctx)
    (complete : Sampling.SourceRegister.Index) :
    outputCompatible parameters 260 260 (Nat.le_refl 260) (Nat.le_refl 260) store complete ↔
      complete = storedComplete parameters store := by
  change Fin (2 ^ 260) × Fin (2 ^ 260) at complete
  simp only [outputCompatible, Partner.prefixBits_all, storedComplete]
  with_reducible
    exact pair_equiv_eq_iff (Source := Fin (2 ^ 260)) (Output := Bits 260)
      (binaryEquiv 260) complete
      (Feedback.retainedPrefix parameters.results.cells 0 260 (Nat.le_refl 260) store)
      (Feedback.retainedPrefix parameters.results.cells 1 260 (Nat.le_refl 260) store)

/-- At the final cursor the completion sum is exactly the original record's coherent weight. -/
lemma completionWeight_terminal {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) :
    completionWeight parameters I 260 260 (Nat.le_refl 260) (Nat.le_refl 260)
        store amplitude reference event =
      if event (storedComplete parameters store) = true then
        ‖coherentPrefix parameters I 34 (by omega) 520
          (completedAmplitude I (storedComplete parameters store) amplitude) reference‖ ^ 2
      else 0 := by
  classical
  simp only [completionWeight, outputCompatible_terminal, ite_and]
  simp

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
