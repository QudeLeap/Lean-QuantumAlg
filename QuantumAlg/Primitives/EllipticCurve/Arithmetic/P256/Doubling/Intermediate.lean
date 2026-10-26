/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Rotation.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Correction.Readout
import all QuantumAlg.Util.Nat.FixedWidth.Modular.NearPower.Double

/-! # Canonical intermediate value after the actual rotation and even correction -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

def intermediateWord (target : Word) (canonical : Canonical target) : Word :=
  ⟨Nat.FixedWidth.NearPower.doubleIntermediate modulus capacity target.val,
    Nat.FixedWidth.NearPower.doubleIntermediate_lt_capacity modulus_add_complement canonical⟩

private lemma intermediateWord_value (target : Word) (canonical : Canonical target) :
    (intermediateWord target canonical).val =
      Nat.FixedWidth.NearPower.doubleIntermediate modulus capacity target.val := rfl

private lemma mod_power_eq_capacity (value : Nat) : value % 2 ^ width = value % capacity := by
  have same : 2 ^ width = capacity := rfl
  exact congrArg (fun divisor : Nat => value % divisor) same

private lemma product_coordinates_eq {First Second Third : Type}
    {first second : (First × Second) × Third}
    (source : first.1.1 = second.1.1) (target : first.1.2 = second.1.2)
    (flag : first.2 = second.2) : first = second :=
  Prod.ext (Prod.ext source target) flag

private lemma conditional_word_eq {Source : Type} {bound : Nat} (positive : 0 < bound)
    (state : (Source × Fin bound) × Bool) (source : Source) (target : Fin bound)
    (selected : Bool) (amount : Nat) (sourceSame : state.1.1 = source)
    (flagSame : state.2 = false)
    (numeric : (state.1.2.val + if selected then amount else 0) % bound = target.val) :
    (if selected then
      ((state.1.1, (⟨(state.1.2.val + amount) % bound, Nat.mod_lt _ positive⟩ : Fin bound)),
        state.2) else state) = ((source, target), false) := by
  cases selected with
  | true =>
      simp only [↓reduceIte] at numeric ⊢
      exact product_coordinates_eq sourceSame (Fin.ext numeric) flagSame
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at numeric ⊢
      have targetSame : state.1.2 = target :=
        Fin.ext ((Nat.mod_eq_of_lt state.1.2.isLt).symm.trans numeric)
      exact product_coordinates_eq sourceSame targetSame flagSame

private lemma conditional_numeric {capacity original current amount result : Nat}
    (selected : Bool) (value : current = Nat.FixedWidth.NearPower.rotatedWord capacity original)
    (control : selected = decide (capacity ≤ 2 * original))
    (arithmetic : (Nat.FixedWidth.NearPower.rotatedWord capacity original +
      (if capacity ≤ 2 * original then amount else 0)) % capacity = result) :
    (current + if selected then amount else 0) % capacity = result := by
  rw [value, control]
  simpa only [decide_eq_true_eq] using arithmetic

section

-- Compose certified readouts without normalizing the literal 765-CNOT sweep.
attribute [local irreducible] GateSpec.stepList

private lemma evenCorrection_of_readouts (state : Registers) (source target : Word)
    (canonical : Canonical target) (sourceSame : state.1.1 = source)
    (flagSame : state.2 = false)
    (value : state.1.2.val = Nat.FixedWidth.NearPower.rotatedWord capacity target.val)
    (control : targetLow.get state = decide (capacity ≤ 2 * target.val)) :
    evenCorrectionStep state = ((source, intermediateWord target canonical), false) := by
  have actual := evenCorrectionStep_eq_wordStep state
  have arithmetic := Nat.FixedWidth.NearPower.rotatedWord_even_correction_mod
    complement_positive modulus_add_complement canonical
  have numeric := conditional_numeric (targetLow.get state) value control arithmetic
  have scalar : (state.1.2.val + if targetLow.get state then complement - 1 else 0) %
      2 ^ width = (intermediateWord target canonical).val :=
    (mod_power_eq_capacity _).trans
      (numeric.trans (intermediateWord_value target canonical).symm)
  exact actual.trans (conditional_word_eq (Nat.two_pow_pos width) state source
    (intermediateWord target canonical) (targetLow.get state) (complement - 1)
    sourceSame flagSame scalar)

/-- No borrowed-source initialization or canonical-source premise is needed by doubling. -/
lemma rotation_evenCorrection_clean (source target : Word) (canonical : Canonical target) :
    evenCorrectionStep (stepList rotationGates ((source, target), false)) =
      ((source, intermediateWord target canonical), false) := by
  let original : Registers := ((source, target), false)
  have rotation := rotationGates_step original
  have sourceProjection := congrArg (fun state : Registers => state.1.1) rotation
  have sourceRetained : (stepList rotationGates original).1.1 = source := sourceProjection
  have flagProjection := congrArg (fun state : Registers => state.2) rotation
  have flagRetained : (stepList rotationGates original).2 = false := flagProjection
  exact evenCorrection_of_readouts (stepList rotationGates original) source target canonical
    sourceRetained flagRetained (rotation_target_value original) (rotation_target_control original)

end

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
