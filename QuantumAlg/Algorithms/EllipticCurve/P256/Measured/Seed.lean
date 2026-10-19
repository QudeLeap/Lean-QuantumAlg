/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Offset

/-!
# One original subgroup seed for the actual P-256 execution

Finite averaging chooses a nonidentity offset from the original public
subgroup. This mathematical choice precedes every input state, reference and
repetition. The seed and affine addend schedule use only the certified public
instance; no logarithm witness is an executable parameter.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open PrimeFieldShortWeierstrass FiniteCyclicDLP

/-- One fixed original nonidentity subgroup point supplies every actual P-256 repetition. -/
public def fixedSeed (I : DomainParameters.PublicKeyInstance) :
    AffinePoint (DomainParameters.curve I.curveCert) :=
  Classical.choose (ECDLP.Measured.exists_fixedOffset_exceptionalMass_bound
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
    (Cascade.addend I))

/-- The selected point lies in the original public subgroup and is nonidentity. -/
lemma fixedSeed_original_subgroup (I : DomainParameters.PublicKeyInstance) :
    (fixedSeed I).toGroupPoint ∈
        Subgroup.zpowers (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator ∧
      (fixedSeed I).toGroupPoint ≠ 1 := by
  have selected := Classical.choose_spec (ECDLP.Measured.exists_fixedOffset_exceptionalMass_bound
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
    (Cascade.addend I))
  exact ⟨selected.1, selected.2.1⟩

/-- The original prepared exceptional mass has the original two-exceptions-per-step bound. -/
lemma fixedSeed_exceptionalMass_le (I : DomainParameters.PublicKeyInstance) :
    ECDLP.Measured.preparedExceptionalMass
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) (fixedSeed I) ≤
      (2 * (2 * orderWidth (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))) : Nat) /
        (((ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).order - 1 : Nat) : ℝ) :=
  (Classical.choose_spec (ECDLP.Measured.exists_fixedOffset_exceptionalMass_bound
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le
    (Cascade.addend I))).2.2

/-- The original physical affine schedule denotes the exact paired big-endian public powers. -/
lemma addend_original_encoding (I : DomainParameters.PublicKeyInstance) :
    (fun index => (Cascade.addend I index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (Cascade.exponentWidth I)
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).generator
        (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).target := by
  funext index
  rw [Cascade.addend_toGroupPoint]
  rfl

end

end QuantumAlg.EllipticCurve.P256.Measured
