/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Recompute
import all QuantumAlg.Primitives.MeasuredUncompute.Multiplication.Arithmetic

/-!
# Actual saved words agree with the independent in-place targets

The physical accumulator readouts of the actual native products agree
with the independently defined two-word prime permutations on the
original domain 0<X<p and Y<p. In particular Y=0 remains included
[LYL+26, sec_point_add/sec_point_add.tex:24-36,45-105,119-122].

Implementation agreement belongs here, outside the mathematical target
owner. The target never takes its output word from an EEA run, a native
product or a caller-supplied arithmetic action.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceTargetAgreement

noncomputable section

/-- The EEA-independent residue inverse and the target's finite inverse are the same word. -/
lemma inverse_word (modulus : Nat) (prime : Nat.Prime modulus)
    (value : Fin (2 ^ modulus.size)) :
    NumberTheory.SharedEEA.CanonicalInverse.word modulus prime.pos value.val =
      Nat.FixedWidth.PrimeWordProduct.inverseWord
        (InPlaceTarget.modulusWord modulus) prime value := by
  apply Fin.ext
  rfl

/-- The actual initial multiplication saves exactly the independent original-domain product. -/
lemma multiplication_saved (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    MultiplicationArithmetic.saved modulus value numerator =
      InPlaceTarget.resultWord .multiplication modulus prime value numerator :=
  Fin.ext ((MultiplicationArithmetic.saved_value modulus prime value numerator).trans
    (InPlaceTarget.multiplication_value modulus prime value numerator
      positive bounded numeratorBound).symm)

/-- The actual inverse-product accumulator saves exactly the independent quotient word. -/
lemma division_saved (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    InPlaceRecompute.saved modulus value numerator positive bounded =
      InPlaceTarget.resultWord .division modulus prime value numerator := by
  have actual := InPlaceRecompute.saved_value modulus prime value numerator positive bounded
  change (InPlaceRecompute.saved modulus value numerator positive bounded).val =
    (((value.val : ZMod modulus)⁻¹).val * numerator.val) % modulus at actual
  exact Fin.ext (actual.trans (InPlaceTarget.division_value modulus prime value numerator
    positive bounded numeratorBound).symm)

end

end QuantumAlg.MeasuredUncompute.InPlaceTargetAgreement
