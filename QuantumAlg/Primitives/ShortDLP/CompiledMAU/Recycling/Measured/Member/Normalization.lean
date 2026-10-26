/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Normalization

/-!
# Exact two-stream arithmetic-record normalization and actual record reindexing

All actual chronological records are reindexed bijectively. Only arithmetic
coefficient weights are summed to one; retained exponent outcomes continue
to carry their complete source-dependent probabilities [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat) (modulus : BitVec width) (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- Every original actual member record is retained in the exact two-stream reindexing. -/
lemma member_outcome_sum_reindex {M : Type} [AddCommMonoid M]
    (function : MemberOutcomes base noQuantum m ell width modulus wide generator target → M) :
    (∑ outcomes, function outcomes) =
      ∑ arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator
          target,
        ∑ readout : MemberReadouts m ell,
          function ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator
            target).symm (arithmetic, readout)) := by
  let correspondence := memberOutcomeEquiv base noQuantum m ell width modulus wide generator target
  calc
    _ = ∑ joined, function (correspondence.symm joined) :=
      Fintype.sum_equiv correspondence _ _ (fun outcomes =>
        congrArg function (correspondence.symm_apply_apply outcomes).symm)
    _ = _ := by rw [Fintype.sum_prod_type]

/-- At each fixed retained tuple the complete original arithmetic coefficient weights sum to one. -/
lemma member_arithmetic_weights_sum :
    (∑ _record : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target,
      memberAlpha m ell width modulus generator target *
        star (memberAlpha m ell width modulus generator target)) = 1 := by
  let firstAlpha := exponentAlpha width modulus (bits := ell + m) generator (ell + m) 0 (by omega)
  let secondAlpha := exponentAlpha width modulus (bits := ell) target⁻¹ ell 0 (by omega)
  change (∑ _record :
      ExponentArithmeticOutcomes base noQuantum m ell width modulus wide (bits := ell + m) generator
          (ell + m) 0 (by omega) ×
        ExponentArithmeticOutcomes base noQuantum m ell width modulus wide (bits := ell) target⁻¹
          ell 0 (by omega),
    (secondAlpha * firstAlpha) * star (secondAlpha * firstAlpha)) = 1
  rw [Fintype.sum_prod_type]
  simp_rw [arithmetic_weight_mul]
  calc
    _ = ∑ _first : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide
          (bits := ell + m) generator (ell + m) 0 (by omega),
        (firstAlpha * star firstAlpha) *
          (∑ _second : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide
            (bits := ell) target⁻¹ ell 0 (by omega), secondAlpha * star secondAlpha) := by
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.mul_sum]
    _ = ∑ _first : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide
          (bits := ell + m) generator (ell + m) 0 (by omega), firstAlpha * star firstAlpha := by
      rw [exponent_arithmetic_weights_sum base noQuantum m ell width modulus wide (bits := ell)
        target⁻¹ ell 0 (by omega)]
      simp only [mul_one]
    _ = 1 := exponent_arithmetic_weights_sum base noQuantum m ell width modulus wide
      (bits := ell + m) generator (ell + m) 0 (by omega)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
