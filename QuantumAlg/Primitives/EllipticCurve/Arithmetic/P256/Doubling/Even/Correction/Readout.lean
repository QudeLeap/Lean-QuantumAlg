/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Correction.Program

/-! # Complete unsigned readout of the actual three-stage even correction -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private def fixedTranslation (selected : Bool) (amount : Nat) (state : Registers) : Registers :=
  if selected then
    ((state.1.1, ⟨(state.1.2.val + amount) % 2 ^ width,
      Nat.mod_lt _ (Nat.two_pow_pos width)⟩), state.2)
  else state

private lemma three_selected_actions {Label : Type} (selector : Label → Bool)
    (first second third : Label → Label) (first' second' third' : Bool → Label → Label)
    (firstAction : ∀ state, first state = first' (selector state) state)
    (firstControl : ∀ state, selector (first state) = selector state)
    (secondAction : ∀ state, second state = second' (selector state) state)
    (secondControl : ∀ state, selector (second state) = selector state)
    (thirdAction : ∀ state, third state = third' (selector state) state)
    (state : Label) :
    third (second (first state)) =
      third' (selector state) (second' (selector state) (first' (selector state) state)) := by
  rw [thirdAction, secondControl, firstControl, secondAction, firstControl, firstAction]

private lemma forward_translation (length : Nat) (fits : length < width) (state : Registers) :
    evenSuffixStep length fits state =
      fixedTranslation (targetLow.get state) (2 ^ (width - length)) state :=
  evenSuffixStep_eq_wordStep length fits state

private lemma reverse_translation (length : Nat) (fits : length < width) (state : Registers) :
    stepList (evenSuffixGates length fits).reverse state =
      fixedTranslation (targetLow.get state) (2 ^ width - 2 ^ (width - length)) state :=
  evenSuffix_reverse_step length fits state

private lemma translations_eq (selected : Bool) (state : Registers) :
    fixedTranslation selected (2 ^ width - 2 ^ (width - 160))
      (fixedTranslation selected (2 ^ width - 2 ^ (width - 64))
        (fixedTranslation selected (2 ^ (width - 32)) state)) =
      fixedTranslation selected (complement - 1) state := by
  rcases state with ⟨⟨addend, target⟩, flag⟩
  cases selected with
  | false => simp only [fixedTranslation, Bool.false_eq_true, if_false]
  | true =>
      simp only [fixedTranslation, ↓reduceIte]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          change (((target.val + 2 ^ 224) % 2 ^ width + (2 ^ width - 2 ^ 192)) %
            2 ^ width + (2 ^ width - 2 ^ 96)) % 2 ^ width =
              (target.val + (complement - 1)) % 2 ^ width
          simp only [Nat.mod_add_mod]
          have constant : 2 ^ 224 + (2 ^ width - 2 ^ 192) + (2 ^ width - 2 ^ 96) =
              complement - 1 + 2 ^ width + 2 ^ width := by
            norm_num [width, complement]
          have total : target.val + 2 ^ 224 + (2 ^ width - 2 ^ 192) +
              (2 ^ width - 2 ^ 96) = target.val + (complement - 1) +
                2 ^ width + 2 ^ width := by omega
          rw [total, Nat.add_mod_right, Nat.add_mod_right]
      · rfl

/-- The actual three-stage program adds the even complement under the retained original bit. -/
lemma evenCorrectionStep_eq_wordStep (state : Registers) :
    evenCorrectionStep state =
      if targetLow.get state then
        ((state.1.1, ⟨(state.1.2.val + (complement - 1)) % 2 ^ width,
          Nat.mod_lt _ (Nat.two_pow_pos width)⟩), state.2)
      else state := by
  have actual := three_selected_actions targetLow.get
    (evenSuffixStep 32 (by decide))
    (stepList (evenSuffixGates 64 (by decide)).reverse)
    (stepList (evenSuffixGates 160 (by decide)).reverse)
    (fun selected => fixedTranslation selected (2 ^ (width - 32)))
    (fun selected => fixedTranslation selected (2 ^ width - 2 ^ (width - 64)))
    (fun selected => fixedTranslation selected (2 ^ width - 2 ^ (width - 160)))
    (forward_translation 32 (by decide)) (evenSuffix_control 32 (by decide))
    (reverse_translation 64 (by decide)) (evenSuffix_reverse_control 64 (by decide))
    (reverse_translation 160 (by decide)) state
  exact actual.trans (translations_eq (targetLow.get state) state)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
