/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Address

/-!
# Whole-digit enable ignores all unused tail address systems

The current MSB-first payload is read from the same physical digit controls.
All remaining address systems have arbitrary saved values. The predicate is
zero exactly when both the selected stream top and that payload are zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

lemma digitZero_iff (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Frame.Raw) (payload : Fin (2 ^ width)) (saved : Fin (2 ^ (15 - width))) :
    (∀ index, (digitBit stream width bounded index).get
      (state, packAddress bounded payload saved) = false) ↔
        (streamBit stream).get (state, packAddress bounded payload saved) = false ∧
          payload = 0 := by
  constructor
  · intro zero
    refine ⟨zero 0, ?_⟩
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have actual := zero bit.rev.succ
    change (addressBit ⟨bit.rev.val, by omega⟩).get
      (state, packAddress bounded payload saved) = false at actual
    rw [addressBit_get, packAddress_bit, Fin.rev_rev] at actual
    simpa only [Fin.val_zero, Nat.zero_testBit] using actual
  · rintro ⟨top, zero⟩ index
    refine Fin.cases top (fun index => ?_) index
    change (addressBit ⟨index.val, by omega⟩).get
      (state, packAddress bounded payload saved) = false
    rw [addressBit_get, packAddress_bit, zero]
    simp

lemma packed_step_output (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Frame.Raw) (payload : Fin (2 ^ width)) (saved : Fin (2 ^ (15 - width))) :
    outputBit.get (step stream width bounded (state, packAddress bounded payload saved)) =
      (outputBit.get (state, packAddress bounded payload saved) ^^
        !decide ((streamBit stream).get (state, packAddress bounded payload saved) = false ∧
          payload = 0)) := by
  rw [step_output]
  simp only [digitZero_iff]

/-- The actual tail predicate reads only four digit bits, even with nonzero saved low systems. -/
lemma tail_step_output (stream : Fin 2) (state : Frame.Raw) (value : Nat)
    (saved : Fin (2 ^ 12)) :
    outputBit.get (step stream 3 (by omega) (state, tailAddress value saved)) =
      (outputBit.get (state, tailAddress value saved) ^^
        !decide ((streamBit stream).get (state, tailAddress value saved) = false ∧
          tailPayload value = 0)) :=
  packed_step_output stream 3 (by omega) state (tailPayload value) saved

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
