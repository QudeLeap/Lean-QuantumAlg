/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix.Reverse

/-! # Complete unsigned readout of the literal four-stage P-256 correction -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

/-- Add the exact sparse complement under the existing flag, retaining every other coordinate. -/
def complementWordStep (state : Registers) : Registers :=
  if state.2 then
    ((state.1.1, ⟨(state.1.2.val + complement) % 2 ^ width,
      Nat.mod_lt _ (Nat.two_pow_pos width)⟩), state.2)
  else state

private def wordComposition (state : Registers) : Registers :=
  suffixReverseWordStep 160 (suffixReverseWordStep 64
    (suffixWordStep 32 (suffixWordStep width state)))

private lemma four_actions {Label : Type}
    (first second third fourth first' second' third' fourth' : Label → Label)
    (sameFirst : ∀ state, first state = first' state)
    (sameSecond : ∀ state, second state = second' state)
    (sameThird : ∀ state, third state = third' state)
    (sameFourth : ∀ state, fourth state = fourth' state) (state : Label) :
    fourth (third (second (first state))) = fourth' (third' (second' (first' state))) := by
  rw [sameFirst, sameSecond, sameThird, sameFourth]

private lemma wordComposition_eq (state : Registers) :
    wordComposition state = complementWordStep state := by
  rcases state with ⟨⟨addend, target⟩, control⟩
  cases control with
  | false =>
      simp only [wordComposition, suffixReverseWordStep, suffixWordStep,
        complementWordStep, Bool.false_eq_true, ↓reduceIte]
  | true =>
      simp only [wordComposition, suffixReverseWordStep, suffixWordStep,
        complementWordStep, ↓reduceIte]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          change
            (((((target.val + 1) % 2 ^ width + 2 ^ 224) % 2 ^ width +
                (2 ^ width - 2 ^ 192)) % 2 ^ width +
                  (2 ^ width - 2 ^ 96)) % 2 ^ width) =
              (target.val + complement) % 2 ^ width
          simp only [Nat.mod_add_mod]
          have constant : 1 + 2 ^ 224 + (2 ^ width - 2 ^ 192) +
              (2 ^ width - 2 ^ 96) = complement + 2 ^ width + 2 ^ width := by
            norm_num [width, complement]
          have total : target.val + 1 + 2 ^ 224 + (2 ^ width - 2 ^ 192) +
              (2 ^ width - 2 ^ 96) = target.val + complement + 2 ^ width + 2 ^ width := by
            omega
          rw [total, Nat.add_mod_right, Nat.add_mod_right]
      · rfl

/-- Whole-word semantics of both forward suffixes and both literal reversed suffixes. -/
lemma sparseComplementStep_eq_wordStep (state : Registers) :
    sparseComplementStep state = complementWordStep state := by
  have actual := four_actions
    (suffixIncrementStep width le_rfl) (suffixIncrementStep 32 (by decide))
    (stepList (suffixIncrementGates 64 (by decide)).reverse)
    (stepList (suffixIncrementGates 160 (by decide)).reverse)
    (suffixWordStep width) (suffixWordStep 32)
    (suffixReverseWordStep 64) (suffixReverseWordStep 160)
    (suffixIncrementStep_eq_wordStep width le_rfl)
    (suffixIncrementStep_eq_wordStep 32 (by decide))
    (suffixIncrement_reverse_step 64 (by decide))
    (suffixIncrement_reverse_step 160 (by decide)) state
  exact actual.trans (wordComposition_eq state)

/-- The same native correction retains all phases with this exact complete-word action. -/
lemma sparseComplement_word_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding sparseComplementProgram environment complementWordStep := by
  exact realizesList_congrStep (QubitLayout.canonical _) .empty sparseComplementGates
    (fun state => (sparseComplementGates_step state).trans
      (sparseComplementStep_eq_wordStep state)) environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
