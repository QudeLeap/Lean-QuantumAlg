/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Target.Exponents

/-!
# Original word and exponent conditions for the initialized scalar trajectory

The complete initialized target step preserves every supplied exponent and
all fixed work, while updating only the two original words. Consequently its
trajectory domain is exactly the original active affine exclusions along the
independent finite-word translations. No internal workspace condition remains
in this word-level predicate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredUncompute

private theorem readyBasis_ext (width count : Nat)
    (first second : (readyContext width count).register.Index)
    (shared : sharedBasis width count first = sharedBasis width count second)
    (indexed : ∀ index, indexedValue width count first index =
      indexedValue width count second index) : first = second := by
  apply (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)).injective
  refine Prod.ext shared ?_
  apply (rangeBasis width (count + 1)).injective
  funext index
  exact indexed index

/-- The independent word action uses the original selected exponent and point translation. -/
def wordStep {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Fin 2) (words : Fin (2 ^ p.size) × Fin (2 ^ p.size)) :
    Fin (2 ^ p.size) × Fin (2 ^ p.size) :=
  if control = 1 then MeasuredPointAddition.translationWords E Q words else words

/-- The full initialized target step retains all exponents and prepared work around new words. -/
theorem stepPermutation_initializedReadyBasis {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (exponent : (exponents p.size count).register.Index) (x y : Fin (2 ^ p.size)) :
    stepPermutation E Q active
      (initializedReadyBasis p count (inputLabel p.size count exponent x y)) =
      initializedReadyBasis p count (inputLabel p.size count exponent
        (wordStep E Q (rangeBasis p.size count exponent active) (x, y)).1
        (wordStep E Q (rangeBasis p.size count exponent active) (x, y)).2) := by
  apply readyBasis_ext
  · rw [stepPermutation_prepared E Q active _ x y
      (initializedReadyBasis_shared p count exponent x y), initializedReadyBasis_exponent,
      initializedReadyBasis_shared]
    rfl
  · intro index
    rw [stepPermutation_indexedValue]
    refine Fin.lastCases ?_ (fun original => ?_) index
    · rw [initializedReadyBasis_selector, initializedReadyBasis_selector]
    · rw [initializedReadyBasis_exponent, initializedReadyBasis_exponent]

/-- Actual fixed initialization leaves only the original selected affine-word condition. -/
theorem stepAdmissible_initialized_iff {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (exponent : (exponents p.size count).register.Index) (x y : Fin (2 ^ p.size)) :
    stepAdmissible E Q active
      (initializedReadyBasis p count (inputLabel p.size count exponent x y)) ↔
      (rangeBasis p.size count exponent active = 1 → ∃ P : AffinePoint E,
        x.val = P.x.val ∧ y.val = P.y.val ∧ P ≠ Q ∧ P ≠ AffinePoint.negate Q) := by
  rw [stepAdmissible_iff, initializedReadyBasis_selector, initializedReadyBasis_shared,
    initializedReadyBasis_exponent]
  constructor
  · rintro ⟨_, otherX, otherY, same, allowed⟩
    have fields := (InPlaceTarget.frameEquiv p.size).injective same
    have words : (x, y) = (otherX, otherY) := congrArg Prod.snd fields
    have xSame : x = otherX := congrArg Prod.fst words
    have ySame : y = otherY := congrArg Prod.snd words
    subst otherX
    subst otherY
    exact allowed
  · intro allowed
    exact ⟨rfl, x, y, rfl, allowed⟩

/-- Only active original affine exclusions are checked along the independent word trajectory. -/
def wordTrajectory {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (exponent : Fin count → Fin 2) :
    List (Fin count) → (Fin (2 ^ p.size) × Fin (2 ^ p.size)) → Prop
  | [], _ => True
  | active :: remaining, words =>
      (exponent active = 1 → ∃ P : AffinePoint E,
        words.1.val = P.x.val ∧ words.2.val = P.y.val ∧
          P ≠ points active ∧ P ≠ AffinePoint.negate (points active)) ∧
        wordTrajectory E points exponent remaining
          (wordStep E (points active) (exponent active) words)

/-- The full initialized-basis trajectory is exactly the original finite-word trajectory. -/
theorem basisTrajectory_initialized_iff {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (exponent : (exponents p.size count).register.Index) (order : List (Fin count))
    (x y : Fin (2 ^ p.size)) :
    basisTrajectory E points order
      (initializedReadyBasis p count (inputLabel p.size count exponent x y)) ↔
      wordTrajectory E points (rangeBasis p.size count exponent) order (x, y) := by
  induction order generalizing x y with
  | nil => rfl
  | cons active remaining ih =>
      rw [basisTrajectory, wordTrajectory, stepAdmissible_initialized_iff,
        stepPermutation_initializedReadyBasis]
      apply and_congr Iff.rfl
      simpa only [Prod.eta] using ih
        (wordStep E (points active) (rangeBasis p.size count exponent active) (x, y)).1
        (wordStep E (points active) (rangeBasis p.size count exponent active) (x, y)).2

/-- The original-input predicate contains exactly the exposed word conditions at every step. -/
theorem inputTrajectory_inputLabel_iff {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (exponent : (exponents p.size count).register.Index) (order : List (Fin count))
    (x y : Fin (2 ^ p.size)) :
    inputTrajectory E points order (inputLabel p.size count exponent x y) ↔
      wordTrajectory E points (rangeBasis p.size count exponent) order (x, y) :=
  basisTrajectory_initialized_iff E points exponent order x y

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
