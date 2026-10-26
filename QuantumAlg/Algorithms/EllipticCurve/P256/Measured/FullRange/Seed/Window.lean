/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.FullRange.Seed.Schedule
import all QuantumAlg.Util.ExceptionalOffsetAveraging.Window

/-!
# A fresh fixed seed for the complete thirty-four-window branch family

Each original 260-bit exponent supplies sixteen unsigned 16-bit windows
and one four-bit tail. All zero addresses remain in the full physical
branch square. The second group base below is the inverse public target;
an actual caller must prepare that signed second classical base port and
certify the same original quantum bit addresses before using this family
for its table/point implementation. No old bitwise seed is reused.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.FullRange

noncomputable section

open PrimeFieldShortWeierstrass FiniteCyclicDLP

private def windowBranch (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) : Nat × Nat :=
  (branch.1.val, branch.2.val)

def windowAddress (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34) : Nat :=
  ExceptionalOffsetAveraging.Window.address (2 ^ 16) 17 (windowBranch I branch) position

def windowSelected (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 34) : Bool :=
  ExceptionalOffsetAveraging.Window.selected (2 ^ 16) 17 (windowBranch I branch) position

def windowAddend (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34) :
    (DomainParameters.curve I.curveCert).GroupPoint :=
  let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
  ExceptionalOffsetAveraging.Window.addend (2 ^ 16) 17 problem.generator problem.target⁻¹
    (windowBranch I branch) position

lemma windowAddress_first (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (window : Fin 17) :
    windowAddress I branch (window.castAdd 17) =
      Nat.FixedWidth.Radix.digit (2 ^ 16) branch.1.val window.val := by
  simp only [windowAddress, ExceptionalOffsetAveraging.Window.address, Fin.val_castAdd,
    window.isLt, ↓reduceIte, windowBranch]

lemma windowAddress_second (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (window : Fin 17) :
    windowAddress I branch (window.natAdd 17) =
      Nat.FixedWidth.Radix.digit (2 ^ 16) branch.2.val window.val := by
  simp only [windowAddress, ExceptionalOffsetAveraging.Window.address, Fin.val_natAdd]
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  rfl

lemma windowAddress_first_bit (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (window : Fin 17) (bit : Fin 16) :
    (windowAddress I branch (window.castAdd 17)).testBit bit.val =
      branch.1.val.testBit (16 * window.val + bit.val) :=
  (congrArg (fun value => value.testBit bit.val) (windowAddress_first I branch window)).trans
    (Nat.FixedWidth.Radix.binary_digit_bit 16 branch.1.val window.val bit)

lemma windowAddress_second_bit (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (window : Fin 17) (bit : Fin 16) :
    (windowAddress I branch (window.natAdd 17)).testBit bit.val =
      branch.2.val.testBit (16 * window.val + bit.val) :=
  (congrArg (fun value => value.testBit bit.val) (windowAddress_second I branch window)).trans
    (Nat.FixedWidth.Radix.binary_digit_bit 16 branch.2.val window.val bit)

private lemma tail_digit_bound {value : Nat} (bounded : value < 2 ^ 260) :
    Nat.FixedWidth.Radix.digit (2 ^ 16) value 16 < 16 :=
  Nat.FixedWidth.Radix.binary_tail_digit_lt_of_width
    (width := 260) (chunk := 16) (window := 16) (tailWidth := 4) (by decide) bounded

/-- The last physical address is four bits even when described in the same sixteen-bit family. -/
lemma windowAddress_first_tail (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    windowAddress I branch ((⟨16, by decide⟩ : Fin 17).castAdd 17) < 16 := by
  rw [windowAddress_first]
  apply tail_digit_bound
  simpa only [Cascade.exponentWidth_eq_260] using branch.1.isLt

lemma windowAddress_second_tail (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    windowAddress I branch ((⟨16, by decide⟩ : Fin 17).natAdd 17) < 16 := by
  rw [windowAddress_second]
  apply tail_digit_bound
  simpa only [Cascade.exponentWidth_eq_260] using branch.2.isLt

/-- Address zero is the identity in precisely the same branch-dependent addend family. -/
lemma windowAddend_zero (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34)
    (inactive : windowSelected I branch position = false) :
    windowAddend I branch position = 1 :=
  ExceptionalOffsetAveraging.Window.addend_of_unselected (2 ^ 16) 17 _ _
    (windowBranch I branch) position inactive

private lemma full_window_capacity (I : DomainParameters.PublicKeyInstance) :
    2 ^ Cascade.exponentWidth I ≤ (2 ^ 16) ^ 17 := by
  apply Nat.FixedWidth.Radix.binary_capacity
  rw [Cascade.exponentWidth_eq_260]
  decide

/-- Complete original exponent values are recovered without truncation to the subgroup order. -/
lemma windowPrefix_complete (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    ExceptionalOffsetAveraging.prefixMultiplier 34 (windowSelected I) (windowAddend I branch)
        branch 34 =
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ^ branch.1.val *
        ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target ^ branch.2.val)⁻¹ := by
  have complete := ExceptionalOffsetAveraging.Window.prefixMultiplier_complete_mapped (2 ^ 16) 17
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target⁻¹ (windowBranch I) branch
  have first := branch.1.isLt.trans_le (full_window_capacity I)
  have second := branch.2.isLt.trans_le (full_window_capacity I)
  exact complete.trans (by
    rw [windowBranch, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second, inv_pow])

/-- One fresh mathematically selected nonidentity seed for this full-q thirty-four-window family. -/
def windowFixedSeed (I : DomainParameters.PublicKeyInstance) :
    AffinePoint (DomainParameters.curve I.curveCert) :=
  scheduleFixedSeed I 34 (windowSelected I) (windowAddend I)

lemma windowFixedSeed_original_subgroup (I : DomainParameters.PublicKeyInstance) :
    (windowFixedSeed I).toGroupPoint ∈
        Subgroup.zpowers (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ∧
      (windowFixedSeed I).toGroupPoint ≠ 1 :=
  scheduleFixedSeed_original_subgroup I 34 (windowSelected I) (windowAddend I)

/-- The entire physical q-squared amplitude mass excludes at most two offsets per window step. -/
lemma windowFixedSeed_exceptionalMass_le (I : DomainParameters.PublicKeyInstance) :
    EllipticCurve.FullRange.exceptionalMass (Cascade.exponentWidth I) 34 (windowSelected I)
        (windowAddend I) (windowFixedSeed I).toGroupPoint ≤
      (68 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ) :=
  (Classical.choose_spec
    (EllipticCurve.FullRange.exists_fixedSeed_exceptionalMass_bound
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
      (Cascade.exponentWidth I) 34 (windowSelected I) (windowAddend I))).2.2

/-- This new family retains the conservative calibration reserve;
actual Born transfer still needs its physical-address and common-coefficient laws. -/
lemma windowFixedSeed_floor_ge (I : DomainParameters.PublicKeyInstance) :
    (4 : ℝ) / 5 ≤ 55 / 64 - 1 / (DomainParameters.subgroupOrder : ℝ) -
      4 * Real.sqrt (EllipticCurve.FullRange.exceptionalMass (Cascade.exponentWidth I) 34
        (windowSelected I) (windowAddend I) (windowFixedSeed I).toGroupPoint) :=
  scheduleFixedSeed_floor_ge I 34 (by decide) (windowSelected I) (windowAddend I)

end

end QuantumAlg.EllipticCurve.P256.Measured.FullRange
