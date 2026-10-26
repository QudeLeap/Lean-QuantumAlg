/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.FullRange.Seed.Window
import all QuantumAlg.Util.ExceptionalOffsetAveraging.Chronology

/-!
# A fresh fixed seed for high-to-low recycled windows on the complete exponent square

Logical row sixteen, the four-bit high tail, is first; complete logical rows
fifteen through zero follow. The generator stream precedes the inverse-target
stream. Offset averaging is instantiated anew on these chronological prefixes.
The resulting seed is independent of the old low-to-high or bitwise choices.
Actual point, feedback, Born and same-seed reset laws remain separate consumers.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.FullRange

noncomputable section

open PrimeFieldShortWeierstrass FiniteCyclicDLP

/-- Logical table row used by each actual chronological position, preserving stream order. -/
def chronologicalRow : Equiv.Perm (Fin 34) := Nat.FixedWidth.Window.Chronology.paired 17

lemma chronologicalRow_first (position : Fin 17) :
    chronologicalRow (position.castAdd 17) = (Fin.rev position).castAdd 17 :=
  Nat.FixedWidth.Window.Chronology.paired_first 17 position

lemma chronologicalRow_second (position : Fin 17) :
    chronologicalRow (position.natAdd 17) = (Fin.rev position).natAdd 17 :=
  Nat.FixedWidth.Window.Chronology.paired_second 17 position

lemma chronologicalRow_first_val (position : Fin 17) :
    (chronologicalRow (position.castAdd 17)).val = 16 - position.val := by
  rw [chronologicalRow_first]
  change 17 - (position.val + 1) = 16 - position.val
  omega

def chronologicalAddress (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34) : Nat :=
  windowAddress I branch (chronologicalRow position)

def chronologicalSelected (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 34) : Bool := windowSelected I branch (chronologicalRow position)

def chronologicalAddend (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34) :
    (DomainParameters.curve I.curveCert).GroupPoint :=
  windowAddend I branch (chronologicalRow position)

lemma chronologicalAddress_first (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 17) :
    chronologicalAddress I branch (position.castAdd 17) =
      Nat.FixedWidth.Radix.digit (2 ^ 16) branch.1.val (Fin.rev position).val := by
  rw [chronologicalAddress, chronologicalRow_first, windowAddress_first]

lemma chronologicalAddress_second (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 17) :
    chronologicalAddress I branch (position.natAdd 17) =
      Nat.FixedWidth.Radix.digit (2 ^ 16) branch.2.val (Fin.rev position).val := by
  rw [chronologicalAddress, chronologicalRow_second, windowAddress_second]

lemma chronologicalAddress_first_bit (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 17) (bit : Fin 16) :
    (chronologicalAddress I branch (position.castAdd 17)).testBit bit.val =
      branch.1.val.testBit (16 * (Fin.rev position).val + bit.val) := by
  rw [chronologicalAddress, chronologicalRow_first]
  exact windowAddress_first_bit I branch (Fin.rev position) bit

lemma chronologicalAddress_second_bit (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 17) (bit : Fin 16) :
    (chronologicalAddress I branch (position.natAdd 17)).testBit bit.val =
      branch.2.val.testBit (16 * (Fin.rev position).val + bit.val) := by
  rw [chronologicalAddress, chronologicalRow_second]
  exact windowAddress_second_bit I branch (Fin.rev position) bit

lemma chronologicalAddress_first_tail (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    chronologicalAddress I branch ((0 : Fin 17).castAdd 17) < 16 := by
  change windowAddress I branch
    ((Nat.FixedWidth.Window.Chronology.logical 17 (0 : Fin 17)).castAdd 17) < 16
  rw [Nat.FixedWidth.Window.Chronology.logical_first]
  exact windowAddress_first_tail I branch

lemma chronologicalAddress_second_tail (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    chronologicalAddress I branch ((0 : Fin 17).natAdd 17) < 16 := by
  change windowAddress I branch
    ((Nat.FixedWidth.Window.Chronology.logical 17 (0 : Fin 17)).natAdd 17) < 16
  rw [Nat.FixedWidth.Window.Chronology.logical_first]
  exact windowAddress_second_tail I branch

lemma chronologicalAddend_zero (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 34)
    (inactive : chronologicalSelected I branch position = false) :
    chronologicalAddend I branch position = 1 :=
  windowAddend_zero I branch (chronologicalRow position) inactive

/-- The new completed chronological family has the same ordered two original exponent powers. -/
lemma chronologicalPrefix_complete (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    ExceptionalOffsetAveraging.prefixMultiplier 34 (chronologicalSelected I)
        (chronologicalAddend I branch) branch 34 =
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ^ branch.1.val *
        ((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target ^ branch.2.val)⁻¹ := by
  have complete := ExceptionalOffsetAveraging.Chronology.windowPrefix_complete (2 ^ 16) 17
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target⁻¹ (windowBranch I branch)
  have first := branch.1.isLt.trans_le (full_window_capacity I)
  have second := branch.2.isLt.trans_le (full_window_capacity I)
  exact complete.trans (by
    rw [windowBranch, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second, inv_pow])

/-- This choice is made directly against all new chronological full-q prefixes. -/
def chronologicalFixedSeed (I : DomainParameters.PublicKeyInstance) :
    AffinePoint (DomainParameters.curve I.curveCert) :=
  scheduleFixedSeed I 34 (chronologicalSelected I) (chronologicalAddend I)

lemma chronologicalFixedSeed_original_subgroup (I : DomainParameters.PublicKeyInstance) :
    (chronologicalFixedSeed I).toGroupPoint ∈
        Subgroup.zpowers (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ∧
      (chronologicalFixedSeed I).toGroupPoint ≠ 1 :=
  scheduleFixedSeed_original_subgroup I 34 (chronologicalSelected I) (chronologicalAddend I)

/-- Every original address pair, including zero, occurs in this new
thirty-four-step average. -/
lemma chronologicalFixedSeed_exceptionalMass_le (I : DomainParameters.PublicKeyInstance) :
    EllipticCurve.FullRange.exceptionalMass (Cascade.exponentWidth I) 34 (chronologicalSelected I)
        (chronologicalAddend I) (chronologicalFixedSeed I).toGroupPoint ≤
      (68 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ) :=
  (Classical.choose_spec
    (EllipticCurve.FullRange.exists_fixedSeed_exceptionalMass_bound
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
      (Cascade.exponentWidth I) 34 (chronologicalSelected I) (chronologicalAddend I))).2.2

lemma chronologicalFixedSeed_floor_ge (I : DomainParameters.PublicKeyInstance) :
    (4 : ℝ) / 5 ≤ 55 / 64 - 1 / (DomainParameters.subgroupOrder : ℝ) -
      4 * Real.sqrt (EllipticCurve.FullRange.exceptionalMass (Cascade.exponentWidth I) 34
        (chronologicalSelected I) (chronologicalAddend I)
        (chronologicalFixedSeed I).toGroupPoint) :=
  scheduleFixedSeed_floor_ge I 34 (by decide) (chronologicalSelected I) (chronologicalAddend I)

end

end QuantumAlg.EllipticCurve.P256.Measured.FullRange
