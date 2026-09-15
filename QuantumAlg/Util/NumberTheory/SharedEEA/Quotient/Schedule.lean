/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Quotient.Trajectory
import all QuantumAlg.Util.Classical.NumberTheory.Euclidean

/-!
# An independent integer schedule for shared EEA quotient phases

The exact remainder projection identifies the active shared-EEA macro
trajectory with the existing Euclidean recurrence. Only after that
identity is proved do we reuse its polynomial termination fuel. The
integer potentials then bound the complete sum of actual quotient bit
lengths, not merely the number of macro iterations.

For the coprime positive-residue domain, the resulting quotient
weight lies between `n` and `2*n-1`. Four phases per quotient bit, as
specified by the source [LYL+26, app_proof/sub_stepnum.tex:4-16], give the
independent conservative schedule `4*(2*n-1)`. The remaining phase weight
is below the capacity of a shift register with `Nat.size n + 2` bits.
The coprime domain extends the source's prime domain by a project proof;
the schedule and its numerical bounds are unchanged.

These are deterministic mathematical schedule bounds. They neither turn
the stopped active trajectory into a physical idle operation nor establish
a corrected terminal circuit, a native gate budget, or restored Gamma.
The source's sharp analytic constant and exact resource formula are not
claimed by this conservative integer argument.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.QuotientSchedule

open QuantumAlg.ClassicalAlgorithms.NumberTheory

/-- The actual shared macro state's remainder coordinates in the existing Euclidean convention. -/
def divisorView (state : IterationState) : Euclid.State :=
  ⟨state.divisor, state.remainder⟩

/-- The shared macro update is exactly the existing remainder update on its actual coordinates. -/
theorem divisorView_step (state : IterationState) :
    divisorView (IterationState.step state) = Euclid.step (divisorView state) := rfl

/-- The complete active shared macro trajectory has exactly the same Euclidean remainder run. -/
theorem divisorView_activeRun (fuel : Nat) (state : IterationState) :
    divisorView (QuotientTrajectory.activeRun fuel state) =
      Euclid.run fuel (divisorView state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    change divisorView (if state.divisor = 0 then state else
        QuotientTrajectory.activeRun fuel (IterationState.step state)) =
      if state.divisor = 0 then divisorView state else
        Euclid.run fuel (Euclid.step (divisorView state))
    by_cases done : state.divisor = 0
    · simp only [if_pos done]
    · simp only [if_neg done]
      exact inductionHypothesis (IterationState.step state)

/-- Existing Euclidean fuel terminates the shared macro recurrence after the exact projection. -/
theorem activeRun_finishes (width : Nat) (state : IterationState)
    (bounded : state.divisor < 2 ^ width) :
    (QuotientTrajectory.activeRun (Euclid.gcdFuel width) state).divisor = 0 := by
  have finished := Euclid.euclidRun_first_eq_zero_of_first_lt_pow width (divisorView state) bounded
  calc
    _ = (divisorView (QuotientTrajectory.activeRun (Euclid.gcdFuel width) state)).first := rfl
    _ = (Euclid.run (Euclid.gcdFuel width) (divisorView state)).first :=
      congrArg Euclid.State.first (divisorView_activeRun (Euclid.gcdFuel width) state)
    _ = 0 := finished

/-- The full actual quotient weight after the source's original input fold. -/
def foldedWeight (modulus input : Nat) : Nat :=
  QuotientTrajectory.weight (Euclid.gcdFuel modulus.size)
    (IterationState.initial modulus (foldInput modulus input).2)

/-- Every original positive residue terminates within the reused fuel after exact projection. -/
theorem folded_finishes (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (QuotientTrajectory.activeRun (Euclid.gcdFuel modulus.size)
      (IterationState.initial modulus (foldInput modulus input).2)).divisor = 0 := by
  apply activeRun_finishes
  have folded := foldInput_positive_half modulus input positive bounded
  have below : (foldInput modulus input).2 ≤ modulus := by omega
  exact below.trans_lt (Nat.lt_size_self modulus)

/-- The coprime-input domain supplies both complete quotient-weight bounds internally. -/
theorem folded_weight_bounds (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    modulus.size ≤ foldedWeight modulus input ∧ foldedWeight modulus input < 2 * modulus.size := by
  let state := IterationState.initial modulus (foldInput modulus input).2
  have valid := folded_initial_admissible modulus input positive bounded
  have active : 0 < state.divisor := (foldInput_positive_half modulus input positive bounded).1
  have finished : (QuotientTrajectory.activeRun (Euclid.gcdFuel modulus.size) state).divisor = 0 :=
    folded_finishes modulus input positive bounded
  have foldedCoprime : Nat.gcd state.remainder state.divisor = 1 := by
    change Nat.gcd modulus (foldInput modulus input).2 = 1
    rw [foldInput_gcd modulus input bounded.le]
    exact coprime.symm
  exact ⟨QuotientTrajectory.size_le_weight (Euclid.gcdFuel modulus.size) state active finished
      foldedCoprime,
    QuotientTrajectory.weight_lt_twice_size (Euclid.gcdFuel modulus.size) state
      valid.divisor_lt finished⟩

/-- The four-phase weight corresponding to the complete actual quotient sequence. -/
def phaseWeight (modulus input : Nat) : Nat := 4 * foldedWeight modulus input

/-- An independent conservative schedule, chosen from the proved integer quotient potential. -/
def schedule (width : Nat) : Nat := 4 * (2 * width - 1)

/-- The source's four-phase quotient weight lies within the independent deterministic schedule. -/
theorem phase_weight_bounds (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    4 * modulus.size ≤ phaseWeight modulus input ∧
      phaseWeight modulus input ≤ schedule modulus.size := by
  have bounds := folded_weight_bounds modulus input coprime positive bounded
  unfold phaseWeight schedule
  omega

/-- The independent schedule is linear in the original encoded input width. -/
theorem schedule_linear (width : Nat) : schedule width ≤ 8 * width := by
  unfold schedule
  omega

/-- The remaining scheduled phase weight, retained separately from the active mathematical run. -/
def padding (modulus input : Nat) : Nat := schedule modulus.size - phaseWeight modulus input

/-- All coprime positive inputs leave at most the stated deterministic terminal padding length. -/
theorem padding_bound (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    padding modulus input ≤ 4 * modulus.size - 4 := by
  have sizeTwo : 2 ≤ modulus.size := by
    have oneLt : 1 < modulus.size := Nat.lt_size.mpr (by omega : 2 ≤ modulus)
    omega
  have bounds := phase_weight_bounds modulus input coprime positive bounded
  unfold padding schedule
  omega

/-- Two high counter bits suffice for all proved terminal padding lengths, without wrap. -/
theorem padding_fits_extended_clock (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    padding modulus input < 2 ^ (modulus.size.size + 2) := by
  have paddingBound := padding_bound modulus input coprime positive bounded
  have widthBound := Nat.lt_size_self modulus.size
  rw [Nat.pow_add]
  change padding modulus input < 2 ^ modulus.size.size * 4
  omega

/-- The original active alignment-length upper bound also fits that same extended register. -/
theorem width_fits_extended_clock (width : Nat) : width < 2 ^ (width.size + 2) :=
  (Nat.lt_size_self width).trans_le
    (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))

end QuantumAlg.NumberTheory.SharedEEA.QuotientSchedule
