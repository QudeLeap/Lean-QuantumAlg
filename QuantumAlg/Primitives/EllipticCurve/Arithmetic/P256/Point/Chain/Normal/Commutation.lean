/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Normal
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.State.Update
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber.Set

/-!
# Exact genuine-normal cleanup after the original numerical Y update

The genuine predicate depends only on real F and numerical X. Updating Y
therefore commutes with the original normal toggle on the complete label.
The same inverse toggle clears exactly its own retained predicate after
the actual measured product and exceptional Y addition. All original
source coordinates remain part of the equation, without a new domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal

noncomputable section

open EncodedBit EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

private lemma normal_numerator_ne (index : Fin 256) :
    Window.normalBit.wire ≠ ((Window.resultWord .numerator).bit index).wire := by
  intro same
  have locations := congrArg Fin.val same
  rw [Window.normalBit_wire, Window.resultWord_wire] at locations
  change 837 = 580 + (255 - index.val) at locations
  omega

/-- The genuine normal predicate keeps its exact value after any original Y replacement. -/
lemma selected_setNumerator (value : Word) (state : Window.Raw) :
    selected (resultSetConstant (Window.resultWord .numerator) value state) = selected state := by
  have flag : Window.Enable.outputBit.get
      (resultSetConstant (Window.resultWord .numerator) value state) =
        Window.Enable.outputBit.get state := by
    apply resultSetConstant_observed
    intro index same
    have locations := congrArg Fin.val same
    rw [Window.resultWord_wire, Window.Enable.outputBit_wire] at locations
    change 580 + (255 - index.val) = 560 at locations
    omega
  have target : Frame.work2
      (resultSetConstant (Window.resultWord .numerator) value state).1 = Frame.work2 state.1 :=
    Window.resultSetConstant_word_other .numerator .work2 (by decide) value state
  rw [selected_value, selected_value, flag, target]

/-- Normal preparation commutes with the same complete original Y-word replacement. -/
lemma step_setNumerator_comm (value : Word) (state : Window.Raw) :
    step (resultSetConstant (Window.resultWord .numerator) value state) =
      resultSetConstant (Window.resultWord .numerator) value (step state) := by
  apply EncodedBit.state_eq_of_get_eq Window.encoding_surjective
  intro observed
  by_cases normal : Window.normalBit.wire = observed.wire
  · rw [← eq_of_wire_eq Window.normalBit observed normal, step_normal,
      Window.resultSetConstant_normal, selected_setNumerator,
      Window.resultSetConstant_normal, step_normal]
  · by_cases target : ∃ index, ((Window.resultWord .numerator).bit index).wire = observed.wire
    · obtain ⟨index, same⟩ := target
      rw [← eq_of_wire_eq ((Window.resultWord .numerator).bit index) observed same,
        step_other _ (normal_numerator_ne index),
        resultSetConstant_get _ (Window.resultWord_distinct .numerator),
        resultSetConstant_get _ (Window.resultWord_distinct .numerator)]
    · have outside : ∀ index,
          ((Window.resultWord .numerator).bit index).wire ≠ observed.wire := by
        intro index same
        exact target ⟨index, same⟩
      rw [step_other observed normal,
        resultSetConstant_observed _ value observed outside,
        resultSetConstant_observed _ value observed outside, step_other observed normal]

/-- The actual inverse normal toggle restores the original normal bit after any Y result. -/
lemma step_setNumerator_step (value : Word) (state : Window.Raw) :
    step (resultSetConstant (Window.resultWord .numerator) value (step state)) =
      resultSetConstant (Window.resultWord .numerator) value state := by
  rw [step_setNumerator_comm, step_step]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal
