/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Alignment
import all QuantumAlg.Util.NumberTheory.SharedEEA.Coefficient.Capacity

/-!
# Intermediate source quotient prefixes and actual length coordinates

The second phase shifts the aligned divisor right and appends one actual
comparison bit at each step [LYL+26, sec_EEA/sub_4phase.tex:8-22;
sec_EEA/sub_regshare.tex:279-287]. Its source `ℓ_q` counts the written
effective most-significant quotient bits, while `ℓ_s` records the remaining
alignment shifts. This module proves these coordinates for the existing
`DivisionPhase.run`, entered from the already constructed `Alignment.align`.

At every intermediate position, the written prefix is the actual quotient
divided by the remaining scale; its bit length equals the written count.
The quotient is used only in the proved characterization. Neither actual
initialization nor the division steps read a precomputed quotient. The zero
written-bit state, subtraction equality, and a zero current remainder are
included. Reversing the retained written count restores every arithmetic
coordinate; phase/sign flag restoration is a separate obligation.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DivisionProgress

private lemma half_power (count remaining : Nat) :
    2 ^ ((count + 1) + remaining) / 2 = 2 ^ (count + remaining) := by
  rw [show (count + 1) + remaining = (count + remaining) + 1 by omega, Nat.pow_succ]
  exact Nat.mul_div_left _ (by decide : 0 < 2)

/-- A genuine partial division run preserves its full arithmetic and reversible invariants. -/
lemma run_invariants (divisor count remaining : Nat) (state : DivisionPhase.State)
    (scale : state.scale = 2 ^ (count + remaining))
    (below : DivisionPhase.Below divisor state) :
    (DivisionPhase.run divisor count state).scale = 2 ^ remaining ∧
      DivisionPhase.total divisor (DivisionPhase.run divisor count state) =
        DivisionPhase.total divisor state ∧
      DivisionPhase.Below divisor (DivisionPhase.run divisor count state) ∧
      DivisionPhase.rewindRun divisor count (DivisionPhase.run divisor count state) = state := by
  induction count generalizing state with
  | zero =>
    refine ⟨?_, rfl, below, rfl⟩
    simpa only [DivisionPhase.run, Nat.zero_add] using scale
  | succ count inductionHypothesis =>
    have nextScale : (DivisionPhase.step divisor state).scale = 2 ^ (count + remaining) := by
      change state.scale / 2 = 2 ^ (count + remaining)
      rw [scale]
      exact half_power count remaining
    have evenScale : 2 * (state.scale / 2) = state.scale := by
      rw [scale, half_power]
      rw [show (count + 1) + remaining = (count + remaining) + 1 by omega, Nat.pow_succ]
      omega
    obtain ⟨finalScale, total, finalBelow, reversed⟩ := inductionHypothesis
      (DivisionPhase.step divisor state) nextScale
      (DivisionPhase.step_below divisor state evenScale below)
    refine ⟨finalScale, total.trans (DivisionPhase.step_total divisor state evenScale),
      finalBelow, ?_⟩
    change DivisionPhase.rewind divisor
      (DivisionPhase.rewindRun divisor count
        (DivisionPhase.run divisor count (DivisionPhase.step divisor state))) = state
    rw [reversed]
    exact DivisionPhase.rewind_step divisor state evenScale

/-- Enter the actual second phase from the comparison-driven first phase and execute a prefix. -/
def current (state : IterationState) (count : Nat) : DivisionPhase.State :=
  DivisionPhase.run state.divisor count
    (DivisionPhase.start state.remainder (Alignment.align state.remainder state.divisor).scale)

/-- Every performed extraction increments the source's actual quotient-length coordinate. -/
lemma current_written (state : IterationState) (count : Nat) :
    (current state count).written = count := by
  simpa only [current, DivisionPhase.start, Nat.zero_add] using
    DivisionPhase.run_written state.divisor count
      (DivisionPhase.start state.remainder (Alignment.align state.remainder state.divisor).scale)

/-- Actual alignment supplies all invariants at each genuine intermediate division position. -/
lemma current_invariants (state : IterationState) (count : Nat)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    (current state count).scale =
        2 ^ ((Alignment.align state.remainder state.divisor).places - count) ∧
      (current state count).remainder +
          (current state count).quotientPrefix * (current state count).scale * state.divisor =
        state.remainder ∧
      (current state count).remainder < (current state count).scale * state.divisor ∧
      DivisionPhase.rewindRun state.divisor (current state count).written
          (current state count) =
        DivisionPhase.start state.remainder
          (Alignment.align state.remainder state.divisor).scale := by
  have initialScale : (Alignment.align state.remainder state.divisor).scale =
      2 ^ (count + ((Alignment.align state.remainder state.divisor).places - count)) := by
    rw [Alignment.align_scale]
    congr 1
    omega
  obtain ⟨scale, total, below, reversed⟩ := run_invariants state.divisor count
    ((Alignment.align state.remainder state.divisor).places - count)
    (DivisionPhase.start state.remainder (Alignment.align state.remainder state.divisor).scale)
    initialScale (Alignment.align_stops state.remainder state.divisor active)
  refine ⟨scale, ?_, below, ?_⟩
  · change (current state count).remainder +
        (current state count).quotientPrefix * (current state count).scale * state.divisor =
      state.remainder + 0 * (Alignment.align state.remainder state.divisor).scale * state.divisor
        at total
    simpa only [Nat.zero_mul, Nat.add_zero] using total
  · rw [current_written]
    exact reversed

/-- The actual prefix equals the high quotient bits at the current remaining scale. -/
lemma current_prefix (state : IterationState) (count : Nat)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    (current state count).quotientPrefix =
      state.quotient / 2 ^ ((Alignment.align state.remainder state.divisor).places - count) := by
  obtain ⟨scale, decomposition, below, _⟩ := current_invariants state count active within
  have quotientPrefixEq : (current state count).quotientPrefix =
      state.remainder / ((current state count).scale * state.divisor) := by
    symm
    apply Nat.div_eq_of_lt_le
    · have weighted : (current state count).quotientPrefix *
          ((current state count).scale * state.divisor) ≤ state.remainder := by
        rw [← Nat.mul_assoc]
        omega
      exact weighted
    · calc
        state.remainder = (current state count).remainder +
            (current state count).quotientPrefix * (current state count).scale * state.divisor :=
          decomposition.symm
        _ < (current state count).scale * state.divisor +
            (current state count).quotientPrefix * (current state count).scale * state.divisor :=
          Nat.add_lt_add_right below _
        _ = ((current state count).quotientPrefix + 1) *
            ((current state count).scale * state.divisor) := by ring
  calc
    _ = state.remainder / ((current state count).scale * state.divisor) := quotientPrefixEq
    _ = state.remainder / state.divisor / (current state count).scale := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    _ = _ := by rw [scale]; rfl

/-- No leading zero is counted: actual phase-two quotient length is its effective bit length. -/
lemma current_prefix_size (state : IterationState) (count : Nat)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    (current state count).quotientPrefix.size = (current state count).written := by
  rw [current_prefix state count active within, current_written,
    CoefficientCapacity.size_div_pow_two]
  have aligned := Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  change (Alignment.align state.remainder state.divisor).places = state.quotient.size at aligned
  omega

/-- The remaining physical shift and the written quotient length sum to the actual alignment. -/
lemma current_lengths (state : IterationState) (count : Nat)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    ((Alignment.align state.remainder state.divisor).places - count) +
        (current state count).written = (Alignment.align state.remainder state.divisor).places := by
  rw [current_written]
  omega

/-- Executing all actual aligned places is exactly the already proved first-two-phase result. -/
lemma current_end (state : IterationState) :
    current state (Alignment.align state.remainder state.divisor).places =
      Alignment.divide state.remainder state.divisor := by
  rfl

/-- The zero-bit starting state and the equality-boundary first digit are both real states. -/
lemma smallest_input_prefixes :
    current (IterationState.initial 2 1) 0 = ⟨2, 0, 4, 0⟩ ∧
      current (IterationState.initial 2 1) 1 = ⟨0, 1, 2, 1⟩ ∧
      current (IterationState.initial 2 1) 2 = ⟨0, 2, 1, 2⟩ := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.DivisionProgress
