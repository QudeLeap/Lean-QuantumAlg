/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Projection
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Matrix
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Normalization
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic-record normalization at each retained exponent bit tuple

Only the chronological arithmetic records are summed. The actual retained
exponent bits keep their source-dependent half-sum probabilities. This
normalization makes no uniform-readout assumption and does not identify
distinct overwritten arithmetic outcomes [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

private lemma arithmetic_weight_mul (first second : ℂ) :
    (first * second) * star (first * second) =
      (second * star second) * (first * star first) := by
  rw [star_mul]
  ring

variable (base : RuntimeCtx .quantum)
  (noQuantum : base.quantumWires = []) (m ell width : Nat)
  (modulus : BitVec width) (wide : 2 ≤ width) {bits : Nat}
  (unit : (ZMod modulus.toNat)ˣ)

/-- Every fixed retained readout tuple has total arithmetic coefficient weight exactly one. -/
lemma exponent_arithmetic_weights_sum (remaining position : Nat)
    (bounded : position + remaining ≤ bits) :
    (∑ _record : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
        position bounded,
      exponentAlpha width modulus unit remaining position bounded *
        star (exponentAlpha width modulus unit remaining position bounded)) = 1 := by
  induction remaining generalizing position with
  | zero =>
      change (∑ _record : Unit, (1 : ℂ) * star (1 : ℂ)) = 1
      simp only [Fintype.sum_unique, star_one, mul_one]
  | succ remaining induction =>
      let current : Fin bits := ⟨position, by omega⟩
      let headAlpha := arithmeticAlpha width modulus (unit ^ (2 ^ current.rev.val))
      let tailAlpha := exponentAlpha width modulus (bits := bits) unit remaining (position + 1)
        (by omega)
      change (∑ _record : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
          current × ExponentArithmeticOutcomes base noQuantum m ell width modulus wide
            (bits := bits) unit remaining (position + 1) (by omega),
        (tailAlpha * headAlpha) * star (tailAlpha * headAlpha)) = 1
      rw [Fintype.sum_prod_type]
      simp_rw [arithmetic_weight_mul]
      calc
        _ = ∑ _head : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit current,
            (headAlpha * star headAlpha) *
              (∑ _tail : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide
                (bits := bits) unit remaining (position + 1) (by omega),
                tailAlpha * star tailAlpha) := by
          apply Finset.sum_congr rfl
          intro head _
          rw [Finset.mul_sum]
        _ = ∑ _head : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit current,
            headAlpha * star headAlpha := by
          rw [induction (position + 1) (by omega)]
          simp only [mul_one]
        _ = 1 := arithmetic_record_weights_sum base noQuantum m ell width wide modulus
          (unit ^ (2 ^ current.rev.val))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
