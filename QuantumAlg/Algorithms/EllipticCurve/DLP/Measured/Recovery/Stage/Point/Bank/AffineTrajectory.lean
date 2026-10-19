/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Bank.GoodColumns
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.WordGoodColumns
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Trajectory.Prefix

/-!
# Original affine exclusions for the actual prepared-bank word trajectory

The independently prescribed affine path gives the same ordinary coordinate
words as the actual fixed-control bank target. The original exceptional-offset
good set supplies its active affine exclusions; no executable scalar compiler
or new public input certificate is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace PointBankAffineTrajectory

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication

/-- The original ordinary words of the supplied affine point. -/
def fieldWords {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (P : AffinePoint E) : Fin (2 ^ p.size) × Fin (2 ^ p.size) :=
  (fieldWord P.x, fieldWord P.y)

/-- The bank target follows the same selected affine step on its original active domain. -/
lemma nextWords_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Bool) (P : AffinePoint E)
    (allowed : control = true → P ≠ Q ∧ P ≠ AffinePoint.negate Q) :
    PointBankGoodColumns.nextWords E Q (BinaryLabelEncoding.bool.encode control) (fieldWords P) =
      fieldWords (AffineTrajectory.nextPoint E Q control P) := by
  cases control with
  | false =>
      rw [AffineTrajectory.nextPoint_false]
      rfl
  | true =>
      have domain := genericAddDomain_of_ne_of_ne_negate E P Q
        (allowed rfl).1 (allowed rfl).2
      rw [AffineTrajectory.nextPoint_true E Q P (allowed rfl).1 (allowed rfl).2]
      change translationWords E Q (fieldWord P.x, fieldWord P.y) = _
      rw [translationWords_fieldWords E Q P.x P.y (sub_ne_zero.mpr domain),
        fieldOutput_true E P Q domain]
      rfl

/-- The original affine order with its selected Boolean control at each source. -/
def affineStages {p : Nat} (E : PrimeFieldShortWeierstrass p)
    {count : Nat} {Source : Type} (points : Fin count → AffinePoint E)
    (controls : Source → Fin count → Bool) (order : List (Fin count)) :
    List (ControlledPointWords.Stage E Source) :=
  order.map (fun index =>
    (points index, fun source => BinaryLabelEncoding.bool.encode (controls source index)))

/-- Original affine admissibility supplies the local domain of every actual bank factor. -/
lemma wordAllowed_of_affine {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} {Source : Type} (points : Fin count → AffinePoint E)
    (controls : Source → Fin count → Bool) (order : List (Fin count))
    (source : Source) (initial : AffinePoint E)
    (allowed : AffineTrajectory.admissible E points (controls source) order initial) :
    PointWordGoodColumns.wordAllowed E (affineStages E points controls order)
      source (fieldWords initial) := by
  induction order generalizing initial with
  | nil => trivial
  | cons active remaining ih =>
      change (BinaryLabelEncoding.bool.encode (controls source active) = 1 →
          ∃ P : AffinePoint E,
            (fieldWords initial).1.val = P.x.val ∧ (fieldWords initial).2.val = P.y.val ∧
              P ≠ points active ∧ P ≠ AffinePoint.negate (points active)) ∧ _
      refine ⟨?_, ?_⟩
      · intro enabled
        have activeTrue : controls source active = true :=
          BinaryLabelEncoding.bool.encode_injective enabled
        exact ⟨initial, rfl, rfl, (allowed.1 activeTrue).1, (allowed.1 activeTrue).2⟩
      · rw [nextWords_fieldWords E (points active) (controls source active) initial allowed.1]
        exact ih _ allowed.2

/-- Actual bank words retain the prescribed ordinary coordinates along the affine path. -/
lemma wordResult_fieldWords {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} {Source : Type} (points : Fin count → AffinePoint E)
    (controls : Source → Fin count → Bool) (order : List (Fin count))
    (source : Source) (initial : AffinePoint E)
    (allowed : AffineTrajectory.admissible E points (controls source) order initial) :
    PointWordGoodColumns.wordResult E (affineStages E points controls order)
      source (fieldWords initial) =
        fieldWords (AffineTrajectory.path E points (controls source) order initial) := by
  induction order generalizing initial with
  | nil => rfl
  | cons active remaining ih =>
      change PointWordGoodColumns.wordResult E (affineStages E points controls remaining) source
          (PointBankGoodColumns.nextWords E (points active)
            (BinaryLabelEncoding.bool.encode (controls source active)) (fieldWords initial)) = _
      rw [nextWords_fieldWords E (points active) (controls source active) initial allowed.1,
        AffineTrajectory.path]
      exact ih _ allowed.2

/-- The unchanged original group-offset good set establishes the full actual bank domain. -/
lemma wordAllowed_finRange_of_group {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} {Source : Type} (points : Fin count → AffinePoint E)
    (controls : Source → Fin count → Bool) (source : Source) (initial : AffinePoint E)
    (good : ExceptionalOffsetAveraging.Admissible count controls
      (fun index => (points index).toGroupPoint) initial.toGroupPoint source) :
    PointWordGoodColumns.wordAllowed E (affineStages E points controls (List.finRange count))
      source (fieldWords initial) := by
  apply wordAllowed_of_affine E points controls (List.finRange count) source initial
  exact AffineTrajectory.admissible_finRange_of_group E points (controls source) initial good

/-- On the same good set the full bank word ends at the original affine trajectory. -/
lemma wordResult_finRange_of_group {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} {Source : Type} (points : Fin count → AffinePoint E)
    (controls : Source → Fin count → Bool) (source : Source) (initial : AffinePoint E)
    (good : ExceptionalOffsetAveraging.Admissible count controls
      (fun index => (points index).toGroupPoint) initial.toGroupPoint source) :
    PointWordGoodColumns.wordResult E (affineStages E points controls (List.finRange count))
      source (fieldWords initial) =
        fieldWords (AffineTrajectory.path E points (controls source)
          (List.finRange count) initial) :=
  wordResult_fieldWords E points controls (List.finRange count) source initial
    (AffineTrajectory.admissible_finRange_of_group E points (controls source) initial good)

end

end PointBankAffineTrajectory
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
