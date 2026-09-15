/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Phase.Composition
import all QuantumAlg.Util.NumberTheory.SharedEEA.ExtendedTerminal

/-!
# Independent schedule bounds for the composed arithmetic phases

The accumulated mathematical count below reads the four actual phase
interfaces and continues from their composed output coordinates. Their
proved exact macro projection identifies this count with four times the
quotient weight [LYL+26, app_proof/sub_stepnum.tex:4-16]. Existing proved
termination fuel is used only for this mathematical accumulation; it is
not a definition of physical idle instructions.

For every coprime positive-residue input, the independent schedule
bounds the complete arithmetic phase count without a caller termination
assumption. Subtracting that count gives precisely the padding length for
the actual rotating terminal prefix. The enlarged counter retains the
entire displacement and permits exact right-rotation decoding.

This connects decoded/finite-word phase counts to a proposed finite
schedule. It does not establish the complete native gate trace, final
counter-wire placement, or a coherent full-circuit cost. In particular,
mathematical termination does not replace the source's real terminal
rotations or erase its retained forward state Gamma
[LYL+26, sec_EEA/sub_opt.tex:37-48,74-84; sec_EEA/sub_4phase.tex:105,121-128].
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PhaseSchedule

open QuantumAlg.ClassicalAlgorithms.NumberTheory

/-- Accumulate only active phase calls, continuing from their actual composed output coordinates. -/
def activeMicrosteps : Nat → IterationState → Nat
  | 0, _state => 0
  | fuel + 1, state =>
    if state.divisor = 0 then 0 else
      PhaseComposition.microsteps state + activeMicrosteps fuel (PhaseComposition.boundary state)

/-- Actual phase counts coincide with the proved quotient weight after exact projection. -/
theorem activeMicrosteps_eq_weight (fuel : Nat) (state : IterationState) :
    activeMicrosteps fuel state = 4 * QuotientTrajectory.weight fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    by_cases finished : state.divisor = 0
    · simp only [activeMicrosteps, QuotientTrajectory.weight, if_pos finished, Nat.mul_zero]
    · have active := Nat.pos_of_ne_zero finished
      rw [activeMicrosteps, if_neg finished, PhaseComposition.boundary_eq_step state active,
        PhaseComposition.microsteps_eq_quotient state active, inductionHypothesis,
        QuotientTrajectory.weight, if_neg finished, Nat.mul_add]

/-- Count the actual composed phase calls from the source's original input fold. -/
def foldedMicrosteps (modulus input : Nat) : Nat :=
  activeMicrosteps (Euclid.gcdFuel modulus.size)
    (IterationState.initial modulus (foldInput modulus input).2)

/-- The genuine composed counts equal the mathematical weight used by the independent schedule. -/
theorem foldedMicrosteps_eq_phaseWeight (modulus input : Nat) :
    foldedMicrosteps modulus input = QuotientSchedule.phaseWeight modulus input :=
  activeMicrosteps_eq_weight _ _

/-- The complete original domain internally supplies both deterministic active count bounds. -/
theorem foldedMicrosteps_bounds (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    4 * modulus.size ≤ foldedMicrosteps modulus input ∧
      foldedMicrosteps modulus input ≤ QuotientSchedule.schedule modulus.size := by
  rw [foldedMicrosteps_eq_phaseWeight]
  exact QuotientSchedule.phase_weight_bounds modulus input coprime positive bounded

/-- The real active phase count plus its remaining terminal count equals the fixed schedule. -/
theorem active_add_padding (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    foldedMicrosteps modulus input + QuotientSchedule.padding modulus input =
      QuotientSchedule.schedule modulus.size := by
  have bounds := foldedMicrosteps_bounds modulus input coprime positive bounded
  rw [QuotientSchedule.padding, ← foldedMicrosteps_eq_phaseWeight]
  omega

/-- Remaining scheduled steps after the actual phase calls fit the two-bit counter extension. -/
theorem remaining_fits_extended_clock (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    QuotientSchedule.schedule modulus.size - foldedMicrosteps modulus input <
      2 ^ (modulus.size.size + 2) := by
  rw [foldedMicrosteps_eq_phaseWeight]
  exact QuotientSchedule.padding_fits_extended_clock modulus input coprime positive bounded

/-- The remaining scheduled steps retain the actual full terminal frame, with rotation and count. -/
theorem remaining_terminal_position {wordWidth : Nat}
    (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (first second : BitVec wordWidth) (iteration : Bool) :
    let remaining := QuotientSchedule.schedule modulus.size - foldedMicrosteps modulus input
    TerminalTail.repeatPrefix remaining
        (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration) =
      ⟨first, second.rotateLeft remaining, BitVec.ofNat (modulus.size.size + 2) remaining,
        ⟨false, false, false, iteration⟩⟩ := by
  dsimp only
  rw [foldedMicrosteps_eq_phaseWeight]
  exact ExtendedTerminal.scheduled_position modulus input coprime positive bounded
    first second iteration

/-- The actual retained counter decodes the complete word after precisely those remaining steps. -/
theorem remaining_terminal_decode {wordWidth : Nat}
    (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (first second : BitVec wordWidth) (iteration : Bool) :
    let remaining := QuotientSchedule.schedule modulus.size - foldedMicrosteps modulus input
    let final := TerminalTail.repeatPrefix remaining
      (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration)
    final.secondWord.rotateRight final.shift.toNat = second := by
  dsimp only
  rw [foldedMicrosteps_eq_phaseWeight]
  exact ExtendedTerminal.scheduled_decode modulus input coprime positive bounded
    first second iteration

end QuantumAlg.NumberTheory.SharedEEA.PhaseSchedule
