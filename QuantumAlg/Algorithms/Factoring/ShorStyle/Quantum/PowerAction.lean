/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Layout

/-!
# Exact selected-power action on the actual Shor seed words

The source modulus is nontrivial, so its canonical unit seed is the literal
word one. The actual compiled MAU schedule maps every exponent basis state
to its modular power and returns the same shared arithmetic auxiliary to
zero. This is an internal seeded action; no initialization certificate is
added to the public factoring input. The action follows from the actual
selected-power fold and the project's clean-auxiliary specialization of
unit-inverse multiplication [G17, paper.tex:186-211].
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

open Nat.FixedWidth

/-- On the original nontrivial-modulus domain, the canonical unit is the actual word one. -/
theorem unitSeed_eq_one {N : Nat} (input : Input N) :
    unitResidueWord (modulus N) input.modulus_pos 1 = (1 : Fin (2 ^ modulusBits N)) := by
  apply Fin.ext
  exact (unitResidueWord_one_val (modulus N) input.modulus_pos).trans
    ((Nat.mod_eq_of_lt input.modulus_gt_one).trans
      (Nat.mod_eq_of_lt (input.modulus_gt_one.trans_le input.register_fits)).symm)

/-- The actual compiled member computes each source power and restores its sole auxiliary word. -/
theorem power_apply_seed {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (exponent : Fin (2 ^ phaseBits N)) :
    (MAU.Exponentiation.Gidney.program (phaseBits N) (modulusBits N)
      (modulus N) (selectedUnit parameter)).applyNormalized
        (NormalizedVector.ket ((MAU.Exponentiation.Gidney.encoding
          (phaseBits N) (modulusBits N)).encode (exponent, 1, 0))) =
      NormalizedVector.ket ((MAU.Exponentiation.Gidney.encoding
        (phaseBits N) (modulusBits N)).encode
          (exponent, unitResidueWord (modulus N) input.modulus_pos
            (selectedUnit parameter ^ exponent.val), 0)) := by
  have actual := MAU.Exponentiation.Gidney.gidneyExponent_clean (phaseBits N) (modulusBits N)
    (modulus N) input.modulus_pos (selectedUnit parameter) exponent
  rw [unitSeed_eq_one input] at actual
  exact actual

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
