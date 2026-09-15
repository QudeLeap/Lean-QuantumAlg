/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.PackedCoefficient.Window
import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Scale

/-!
# Complete physical integer window for coefficient deshifting

The fourth phase specifies the complete comparison of the updated
coefficient with the shifted old coefficient
[LYL+26, sec_EEA/sub_regshare.tex:263-264,297-300]. As the physical rotation
decreases, the whole integer part can need more than the fixed phase-three
coefficient-length-plus-one window. Reading the complete remaining
coefficient region retains those high bits and excludes both the divisor
and every wrapped fractional bit.

This owner proves exact extraction and comparison identities. It does not
claim that the existing fixed-window native block reads this larger region;
the actual finite selector and its reversible placement require their own
implementation refinement and native event accounting. Every internal
window bound below follows from the original admissible macro state.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DeshiftWindow

/-- Extracting every remaining coefficient bit recovers the full integer, without truncation. -/
theorem read_full (shift : Nat) {coefficientWidth remainderWidth : Nat}
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (within : shift ≤ coefficientWidth) :
    (PhysicalWindow.read (coefficientWidth - shift)
      (WordRotation.packRotatedWork2 shift payload)).toNat =
        payload.coefficientBits.toNat / 2 ^ shift := by
  rw [PhysicalWindow.read_rotated shift payload (by omega), BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mpr
  calc
    payload.coefficientBits.toNat < 2 ^ coefficientWidth := payload.coefficientBits.isLt
    _ = 2 ^ (coefficientWidth - shift) * 2 ^ shift := by
      rw [← Nat.pow_add, Nat.sub_add_cancel within]

/-- The original active macro capacity supplies the complete coefficient-region boundary. -/
theorem source_window_bound (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    shift + (state.coefficient.size + 1) ≤
      CoefficientCapacity.work2CoefficientWidth state modulus :=
  CoefficientWindow.arithmetic_window_fits state modulus shift valid conserved active within

/-- The full physical window after quotient consumption reads the entire updated coefficient. -/
theorem read_completed (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    (PhysicalWindow.read (CoefficientCapacity.work2CoefficientWidth state modulus - shift)
      (WordRotation.packRotatedWork2 shift
        (CoefficientCapacity.work2Payload state modulus state.quotient.size
          valid conserved active))).toNat =
      (IterationState.step state).coefficient / 2 ^ shift := by
  have bound := source_window_bound state modulus shift valid conserved active within
  rw [read_full shift _ (by omega)]
  change (CoefficientPhase.run state.coefficient state.quotient.size
    (CoefficientPhase.start state)).value / 2 ^ shift = _
  have complete := CoefficientPhase.finish_start_coefficient state
  change (CoefficientPhase.run state.coefficient state.quotient.size
    (CoefficientPhase.start state)).value = _ at complete
  rw [complete]

/-- This complete physical read gives exactly the source's full fourth-phase comparison. -/
theorem comparison_completed (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    state.coefficient ≤
      (PhysicalWindow.read (CoefficientCapacity.work2CoefficientWidth state modulus - shift)
        (WordRotation.packRotatedWork2 shift
          (CoefficientCapacity.work2Payload state modulus state.quotient.size
            valid conserved active))).toNat ↔
      state.coefficient * 2 ^ shift ≤ (IterationState.step state).coefficient := by
  rw [read_completed state modulus shift valid conserved active within]
  exact DivisionScale.comparison (IterationState.step state).coefficient state.coefficient shift

/-- The full physical window retains the high bit omitted by the fixed two-bit example. -/
theorem full_window_seventeen :
    (PhysicalWindow.read (7 - 2)
      (WordRotation.packRotatedWork2 2
        (⟨17#7, 1#1⟩ : WordPacking.Work2Payload 7 1))).toNat = 4 := by decide

end QuantumAlg.NumberTheory.SharedEEA.DeshiftWindow
