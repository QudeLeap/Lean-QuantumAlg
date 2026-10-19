/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Coefficient.Window
import all QuantumAlg.Util.NumberTheory.SharedEEA.PhysicalWindow

/-!
# Signed instructions on the actual packed coefficient window

The source's coefficient arithmetic reads the left-most `ℓ_t + 1` bits of
the actually rotated second word, updates that window, and subsequently
rotates the word once more [LYL+26, sec_EEA/sub_regshare.tex:263-264,288-296].
Here the input word is the existing bounded `CoefficientCapacity` payload
at its retained physical rotation. The window is extracted from those
actual bits and passed to the already proved signed instructions. The
updated low word replaces exactly that same physical region.

Reachable source capacity proves that the whole arithmetic window lies
inside the coefficient region. Reading it gives exactly the actual integer
part; replacing it preserves every outside bit, including the wrapped
fractional part and the divisor. Reassembling the updated integer part
with the unchanged fraction gives the existing next coefficient microstate.
The complete equality with the next repacked payload and its final extra
rotation is a subsequent composition law, not assumed here.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PackedCoefficientWindow

/-- The actual bounded second work word at this coefficient-phase position. -/
def word (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    BitVec (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size) :=
  WordRotation.packRotatedWork2 count
    (CoefficientCapacity.work2Payload state modulus count valid conserved active)

/-- Reachable source capacity puts the entire arithmetic window in the actual physical word. -/
lemma window_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    CoefficientWindow.width state ≤
      CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size := by
  have inside := CoefficientWindow.arithmetic_window_fits state modulus count
    valid conserved active within
  omega

/-- Extracting the rotated bits recovers exactly the specified arithmetic input word. -/
lemma read_eq (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    PhysicalWindow.read (CoefficientWindow.width state)
        (word state modulus count valid conserved active) =
      CoefficientWindow.valueWord state count valid := by
  calc
    _ = (CoefficientCapacity.work2Payload state modulus count
          valid conserved active).coefficientBits.extractLsb'
            count (CoefficientWindow.width state) :=
      PhysicalWindow.read_rotated count _
        (CoefficientWindow.arithmetic_window_fits state modulus count valid conserved active within)
    _ = _ := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      change ((CoefficientWindow.current state count).value / 2 ^ count) %
          2 ^ CoefficientWindow.width state = CoefficientWindow.integerPart state count
      have aligned : (CoefficientWindow.current state count).value / 2 ^ count =
          CoefficientWindow.integerPart state count := by
        unfold CoefficientWindow.integerPart
        rw [CoefficientCapacity.current_scale]
      rw [aligned, Nat.mod_eq_of_lt]
      have room := CoefficientWindow.addition_room state count valid
      omega

/-- Execute the actual signed instructions using the word read from the physical packed region. -/
def signedWindow (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) : BitVec (CoefficientWindow.width state + 1) :=
  SignedCoefficient.addBit
    (PhysicalWindow.read (CoefficientWindow.width state)
      (word state modulus count valid conserved active))
    (CoefficientWindow.coefficientWord state)
    (CoefficientPhase.lowBit (CoefficientWindow.current state count).remaining)

/-- The actual extracted-window instruction is exactly the previously proved signed microstep. -/
lemma signedWindow_eq (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    signedWindow state modulus count valid conserved active =
      (CoefficientWindow.instruction state count valid).2 := by
  unfold signedWindow
  rw [read_eq state modulus count valid conserved active within]
  rfl

/-- The actual signed computation clears Sign on the read physical region. -/
lemma signedWindow_sign (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    (signedWindow state modulus count valid conserved active).msb = false := by
  rw [signedWindow_eq state modulus count valid conserved active within]
  exact (CoefficientWindow.instruction_clears state count valid).2

/-- Write the actual updated low window back into precisely the same physical word region. -/
def updatedWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    BitVec (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size) :=
  PhysicalWindow.replace (word state modulus count valid conserved active)
    ((signedWindow state modulus count valid conserved active).setWidth
      (CoefficientWindow.width state))
    (window_fits state modulus count valid conserved active within)

/-- Reading back the written physical region gives exactly the true signed-instruction result. -/
lemma updated_read (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    PhysicalWindow.read (CoefficientWindow.width state)
        (updatedWord state modulus count valid conserved active within) =
      (CoefficientWindow.instruction state count valid).2.setWidth
        (CoefficientWindow.width state) := by
  unfold updatedWord
  rw [PhysicalWindow.read_replace,
    signedWindow_eq state modulus count valid conserved active within]

/-- Every physical bit outside the selected arithmetic window is retained without modification. -/
lemma updated_outside (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size)
    (index : Nat) (outside : CoefficientWindow.width state ≤ index)
    (inWord : index <
      CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size) :
    (updatedWord state modulus count valid conserved active within).getMsbD index =
      (word state modulus count valid conserved active).getMsbD index :=
  PhysicalWindow.replace_outside _ _ _ index outside inWord

/-- The updated physical window and retained fractional part give the exact next coefficient. -/
lemma updated_reassembled (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    (PhysicalWindow.read (CoefficientWindow.width state)
        (updatedWord state modulus count valid conserved active within)).toNat *
          (CoefficientWindow.current state count).scale +
            CoefficientWindow.fractionPart state count =
      (CoefficientWindow.current state (count + 1)).value := by
  rw [updated_read]
  exact CoefficientWindow.reassembled_next state count valid

/-- Restoring the originally extracted window recovers the entire original packed work word. -/
lemma replace_original (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    PhysicalWindow.replace (word state modulus count valid conserved active)
        (CoefficientWindow.valueWord state count valid)
        (window_fits state modulus count valid conserved active within) =
      word state modulus count valid conserved active := by
  rw [← read_eq state modulus count valid conserved active within]
  exact PhysicalWindow.replace_read _ _

/-- The actual prime-input path retains its nonzero wrapped fraction through the physical update. -/
lemma nonzero_fraction_physical_step :
    let initial := IterationState.initial 17 (foldInput 17 5).2
    let state := IterationState.step initial
    let valid := IterationState.step_admissible initial
      (folded_initial_admissible 17 5 (by decide) (by decide))
      (foldInput_positive_half 17 5 (by decide) (by decide)).1
    let conserved : state.balance = 17 :=
      (IterationState.step_balance initial).trans (IterationState.initial_balance 17 _)
    let active : 0 < state.divisor := by decide
    let within : 1 ≤ state.quotient.size := by decide
    (word state 17 1 valid conserved active).toNat = 5 ∧
      (updatedWord state 17 1 valid conserved active within).toNat = 197 ∧
      CoefficientWindow.fractionPart state 1 = 1 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.PackedCoefficientWindow
