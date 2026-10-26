/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Fiber

/-!
# Full physical exponent labels and cyclic point fibers

The multiplier's cyclic residue is valid for arbitrary natural exponents,
including every physical label beyond the subgroup order.  Seed cancellation
then identifies the native point-output fibers with the cyclic Fourier kernel.
-/

namespace QuantumAlg.EllipticCurve.FullRange

open FiniteCyclicDLP FiniteCyclicDLP.Canonical.Probability

noncomputable section

/-- The group oracle's exact affine cyclic residue, without a source-range cutoff. -/
lemma oracleMultiplier_eq_pow_iff {G : Type*} [Group G] (problem : KnownOrderProblem G)
    (input : SecretInput problem) (left right : Nat) (residue : ZMod problem.order) :
    problem.toSourceScope.oracleMultiplier left right = problem.generator ^ residue.val ↔
      (left : ZMod problem.order) - input.secret * (right : ZMod problem.order) = residue := by
  let : NeZero problem.order := ⟨problem.order_ne_zero⟩
  rw [SourceScope.oracleMultiplier, ← input.target_eq_generator_pow, ← pow_mul,
    mul_inv_eq_iff_eq_mul, ← pow_add, pow_inj_mod, ← problem.order_eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff']
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  exact sub_eq_iff_eq_add.symm

open PrimeFieldShortWeierstrass ECDLP.Measured

/-- Every full physical branch has exactly the cyclic point-fiber label used
by the full-range Fourier kernel, with the seed canceled as a common translate. -/
lemma idealGroupLabel_selected_iff_residue {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (input : SecretInput problem)
    (branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (residue : Fin problem.order) :
    idealGroupLabel problem seed branch = selectedIdealGroupLabel problem seed residue ↔
      (branch.1.val : ZMod problem.order) - input.secret * (branch.2.val : ZMod problem.order) =
        (residue.val : ZMod problem.order) := by
  have values :
      idealGroupLabel problem seed branch = selectedIdealGroupLabel problem seed residue ↔
      (idealGroupLabel problem seed branch).val =
        (selectedIdealGroupLabel problem seed residue).val := Subtype.ext_iff
  rw [values, selectedIdealGroupLabel_value]
  change seed.toGroupPoint * problem.toSourceScope.oracleMultiplier branch.1.val branch.2.val =
    seed.toGroupPoint * problem.generator ^ residue.val ↔ _
  rw [mul_left_cancel_iff]
  simpa only [ZMod.val_natCast_of_lt residue.isLt] using
    oracleMultiplier_eq_pow_iff problem input branch.1.val branch.2.val
      (residue.val : ZMod problem.order)

end

end QuantumAlg.EllipticCurve.FullRange
