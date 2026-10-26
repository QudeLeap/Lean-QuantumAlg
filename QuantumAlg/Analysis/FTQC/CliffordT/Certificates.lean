/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Certificates.Checks
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Certified dyadic rotations

The original family consists of exactly 42 rotations at indices four through 45.
A separate index-three certificate retains the standard rotation global phase.
The synthesis target is [RS16, gridsynth.tex:146-162]; the explicit words and
bounds here are verified instances, not an optimality claim for their T-counts.
-/

public section

namespace QuantumAlg.CliffordT

noncomputable section

/-- Uniform certified error for each table entry, including the separate index three. -/
def certEps (_j : Nat) : Real := ((1 / 2 ^ 50 : Rat) : Real)

lemma certEps_le (j : Nat) : certEps j ≤ (1 : Real) / 2 ^ 50 := by
  norm_num [certEps]

/-- Explicit T-count bounds of the generated 42-entry table. -/
def tBound (j : Nat) : Nat :=
  match j with
  | 4 => word4TBound
  | 5 => word5TBound
  | 6 => word6TBound
  | 7 => word7TBound
  | 8 => word8TBound
  | 9 => word9TBound
  | 10 => word10TBound
  | 11 => word11TBound
  | 12 => word12TBound
  | 13 => word13TBound
  | 14 => word14TBound
  | 15 => word15TBound
  | 16 => word16TBound
  | 17 => word17TBound
  | 18 => word18TBound
  | 19 => word19TBound
  | 20 => word20TBound
  | 21 => word21TBound
  | 22 => word22TBound
  | 23 => word23TBound
  | 24 => word24TBound
  | 25 => word25TBound
  | 26 => word26TBound
  | 27 => word27TBound
  | 28 => word28TBound
  | 29 => word29TBound
  | 30 => word30TBound
  | 31 => word31TBound
  | 32 => word32TBound
  | 33 => word33TBound
  | 34 => word34TBound
  | 35 => word35TBound
  | 36 => word36TBound
  | 37 => word37TBound
  | 38 => word38TBound
  | 39 => word39TBound
  | 40 => word40TBound
  | 41 => word41TBound
  | 42 => word42TBound
  | 43 => word43TBound
  | 44 => word44TBound
  | 45 => word45TBound
  | _ => 0

/-- Kernel-checked standard rotations for the phase-gradient angle table. -/
public def gradientCertificate (j : Nat) (hj : 4 ≤ j ∧ j ≤ 45) :
    RotationCertificate (2 * Real.pi / 2 ^ j) (certEps j) := by
  rcases hj with ⟨hlo, hhi⟩
  interval_cases j
  · exact RotationCertificate.ofCheck word4_check
  · exact RotationCertificate.ofCheck word5_check
  · exact RotationCertificate.ofCheck word6_check
  · exact RotationCertificate.ofCheck word7_check
  · exact RotationCertificate.ofCheck word8_check
  · exact RotationCertificate.ofCheck word9_check
  · exact RotationCertificate.ofCheck word10_check
  · exact RotationCertificate.ofCheck word11_check
  · exact RotationCertificate.ofCheck word12_check
  · exact RotationCertificate.ofCheck word13_check
  · exact RotationCertificate.ofCheck word14_check
  · exact RotationCertificate.ofCheck word15_check
  · exact RotationCertificate.ofCheck word16_check
  · exact RotationCertificate.ofCheck word17_check
  · exact RotationCertificate.ofCheck word18_check
  · exact RotationCertificate.ofCheck word19_check
  · exact RotationCertificate.ofCheck word20_check
  · exact RotationCertificate.ofCheck word21_check
  · exact RotationCertificate.ofCheck word22_check
  · exact RotationCertificate.ofCheck word23_check
  · exact RotationCertificate.ofCheck word24_check
  · exact RotationCertificate.ofCheck word25_check
  · exact RotationCertificate.ofCheck word26_check
  · exact RotationCertificate.ofCheck word27_check
  · exact RotationCertificate.ofCheck word28_check
  · exact RotationCertificate.ofCheck word29_check
  · exact RotationCertificate.ofCheck word30_check
  · exact RotationCertificate.ofCheck word31_check
  · exact RotationCertificate.ofCheck word32_check
  · exact RotationCertificate.ofCheck word33_check
  · exact RotationCertificate.ofCheck word34_check
  · exact RotationCertificate.ofCheck word35_check
  · exact RotationCertificate.ofCheck word36_check
  · exact RotationCertificate.ofCheck word37_check
  · exact RotationCertificate.ofCheck word38_check
  · exact RotationCertificate.ofCheck word39_check
  · exact RotationCertificate.ofCheck word40_check
  · exact RotationCertificate.ofCheck word41_check
  · exact RotationCertificate.ofCheck word42_check
  · exact RotationCertificate.ofCheck word43_check
  · exact RotationCertificate.ofCheck word44_check
  · exact RotationCertificate.ofCheck word45_check

lemma gradientCertificate_tCount_le (j : Nat) (hj : 4 ≤ j ∧ j ≤ 45) :
    (gradientCertificate j hj).tCount ≤ tBound j := by
  rcases hj with ⟨hlo, hhi⟩
  interval_cases j <;> decide +kernel +revert

/-- Every table angle has a kernel-certified full-phase approximation with its literal T bound. -/
public theorem gradientCertificate_exists (j : Nat) (hj : 4 ≤ j ∧ j ≤ 45) :
    ∃ certificate : RotationCertificate (2 * Real.pi / 2 ^ j) (certEps j),
      certificate.tCount ≤ tBound j :=
  ⟨gradientCertificate j hj, gradientCertificate_tCount_le j hj⟩

/-- Total error of the original 42 entries; the separate index three is excluded. -/
def certEpsTotal : Real := ∑ j ∈ Finset.Icc 4 45, certEps j

lemma certEpsTotal_le : certEpsTotal ≤ 42 * ((1 : Real) / 2 ^ 50) := by
  norm_num [certEpsTotal, certEps, Finset.sum_const, Nat.card_Icc]

/-- Additional approximate certificate at index three, with its own resource bound. -/
def thirdCertificate : RotationCertificate (2 * Real.pi / 2 ^ 3) (certEps 3) :=
  RotationCertificate.ofCheck word3_check

lemma thirdCertificate_tCount : thirdCertificate.tCount = word3TBound := by
  decide +kernel

/-- Repeated exact pi/2 rotations give the three phase-exact small-index cases. -/
private def exactRotationWord (j : Nat) : List Letter :=
  (List.replicate (2 ^ (2 - j)) [.h, .s, .s, .s, .h, .s, .s, .s, .h]).flatten

private lemma exactRotationWord_check (j : Nat) (hj : j ≤ 2) :
    check (exactRotationWord j) j 0 = true := by
  interval_cases j <;> decide +kernel

/-- Exact certificates exist at indices at most two, with no phase quotient. -/
def exactCertificate (j : Nat) (hj : j ≤ 2) :
    RotationCertificate (2 * Real.pi / 2 ^ j) 0 := by
  simpa only [Rat.cast_zero] using RotationCertificate.ofCheck (exactRotationWord_check j hj)

end

end QuantumAlg.CliffordT
