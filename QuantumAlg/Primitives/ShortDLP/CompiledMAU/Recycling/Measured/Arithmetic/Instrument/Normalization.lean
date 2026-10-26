/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Coherent
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Records
import all QuantumAlg.Components.Kets

/-!
# Sum of the common weights over the actual chronological arithmetic records

The finite outcome family is exactly that of the emitted forward MAC,
exchange and explicit inverse MAC. Actual overwritten storage cells do not
identify their distinct chronological outcomes [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

/-- All actual record weights sum to one, including statically omitted zero-offset rows. -/
lemma arithmetic_record_weights_sum (wide : 2 ≤ width) (modulus : BitVec width)
    (coefficient : (ZMod modulus.toNat)ˣ) :
    (∑ _measured : WordOutcomes (Physical.qubits width)
      (context_wires base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val),
      arithmeticAlpha width modulus coefficient *
        star (arithmeticAlpha width modulus coefficient)) = 1 := by
  have weight : arithmeticAlpha width modulus coefficient *
      star (arithmeticAlpha width modulus coefficient) =
      (2 : ℂ)⁻¹ ^ Layout.multiplicationVents modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val := by
    rw [arithmeticAlpha, Layout.multiplication_commonAlpha_eq_power, star_pow,
      NormalizedVector.star_invSqrt2, ← mul_pow, NormalizedVector.invSqrt2_mul_self]
  rw [weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Layout.multiplicationWord_outcomes_card]
  rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
  norm_num

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
