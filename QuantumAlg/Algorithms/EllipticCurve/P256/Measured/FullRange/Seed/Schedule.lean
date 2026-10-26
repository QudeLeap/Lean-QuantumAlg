/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Offset
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.FullRange.Calibration

/-!
# New full-q good seeds for branch-dependent P-256 schedules

Each supplied schedule receives its own mathematically selected nonidentity
subgroup seed against the complete physical square. Every address, including
zero, belongs to that branch family. For at most 520 steps the same conservative
numerical calibration applies. An actual window implementation must separately
prove its branch-dependent action and common coefficient, including address zero.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.FullRange

noncomputable section

open PrimeFieldShortWeierstrass FiniteCyclicDLP

/-- Select a new good seed for precisely the supplied complete physical branch family. -/
def scheduleFixedSeed (I : DomainParameters.PublicKeyInstance) (steps : Nat)
    (selected : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps → Bool)
    (addend : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps →
      (DomainParameters.curve I.curveCert).GroupPoint) :
    AffinePoint (DomainParameters.curve I.curveCert) :=
  Classical.choose (EllipticCurve.FullRange.exists_fixedSeed_exceptionalMass_bound
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
    (Cascade.exponentWidth I) steps selected addend)

/-- The independently selected schedule seed belongs to the original subgroup and is nonzero. -/
lemma scheduleFixedSeed_original_subgroup (I : DomainParameters.PublicKeyInstance) (steps : Nat)
    (selected : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps → Bool)
    (addend : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps →
      (DomainParameters.curve I.curveCert).GroupPoint) :
    (scheduleFixedSeed I steps selected addend).toGroupPoint ∈
        Subgroup.zpowers (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ∧
      (scheduleFixedSeed I steps selected addend).toGroupPoint ≠ 1 := by
  have chosen := Classical.choose_spec
    (EllipticCurve.FullRange.exists_fixedSeed_exceptionalMass_bound
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
      (Cascade.exponentWidth I) steps selected addend)
  exact ⟨chosen.1, chosen.2.1⟩

/-- A new branch-dependent schedule's full-q exceptional mass fits the conservative calibration. -/
lemma scheduleFixedSeed_exceptionalMass_le (I : DomainParameters.PublicKeyInstance)
    (steps : Nat) (bounded : steps ≤ 520)
    (selected : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps → Bool)
    (addend : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps →
      (DomainParameters.curve I.curveCert).GroupPoint) :
    EllipticCurve.FullRange.exceptionalMass (Cascade.exponentWidth I) steps selected addend
        (scheduleFixedSeed I steps selected addend).toGroupPoint ≤
      (1040 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ) := by
  have chosen := (Classical.choose_spec
    (EllipticCurve.FullRange.exists_fixedSeed_exceptionalMass_bound
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
      (Cascade.exponentWidth I) steps selected addend)).2.2
  have numerator : ((2 * steps : Nat) : ℝ) ≤ 1040 := by
    exact_mod_cast (show 2 * steps ≤ 1040 by omega)
  exact chosen.trans (div_le_div_of_nonneg_right numerator (by positivity))

/-- The fresh full-range schedule certificate retains the four-fifths numerical reserve. -/
lemma scheduleFixedSeed_floor_ge (I : DomainParameters.PublicKeyInstance)
    (steps : Nat) (bounded : steps ≤ 520)
    (selected : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps → Bool)
    (addend : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I) → Fin steps →
      (DomainParameters.curve I.curveCert).GroupPoint) :
    (4 : ℝ) / 5 ≤ 55 / 64 - 1 / (DomainParameters.subgroupOrder : ℝ) -
      4 * Real.sqrt (EllipticCurve.FullRange.exceptionalMass (Cascade.exponentWidth I) steps
        selected addend (scheduleFixedSeed I steps selected addend).toGroupPoint) := by
  have error := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (scheduleFixedSeed_exceptionalMass_le I steps bounded selected addend))
    (by norm_num : (0 : ℝ) ≤ 4)
  exact calibratedFloor_ge.trans (sub_le_sub_left error _)

end

end QuantumAlg.EllipticCurve.P256.Measured.FullRange
