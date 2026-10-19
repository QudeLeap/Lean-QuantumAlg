/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Macrostep
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Trajectory

/-!
# Complete active trajectory of the actual shared-register microstep

Every transition below is a proved composition of the same eight native
blocks. The accumulated count is four times the actual quotient-size
weight, and the result retains the complete shared words, all finite
length fields, clean internal Ctrl, and the exact fold-and-exchange Iter
history [LYL+26, sec_EEA/sub_regshare.tex:275-313;
LYL+26, sec_EEA/sub_4phase.tex:112-125].

The independent Euclidean fuel and coprime positive-residue assumptions
establish the actual terminal macro frame internally. This is the active
prefix of the physical program, before its remaining fixed-schedule
terminal steps. No idle operation, new runtime loop, omitted padding
gate, or erased forward state is introduced by this mathematical count.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeTrajectory

noncomputable section

open NumberTheory.SharedEEA
open QuantumAlg.ClassicalAlgorithms.NumberTheory

/-- The entire actual active prefix reaches its canonical frame and exact retained iteration bit. -/
lemma iterate_frame (fuel : Nat) (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[4 * QuotientTrajectory.weight fuel state]
      (MacroBoundary.frame state modulus valid conserved iteration) =
      MacroBoundary.frame (QuotientTrajectory.activeRun fuel state) modulus
        (TerminalPadding.activeRun_admissible fuel state valid)
        ((TerminalPadding.activeRun_balance fuel state).trans conserved)
        (SignedTrajectory.retainedIteration fuel state iteration) := by
  induction fuel generalizing state iteration with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    by_cases finished : state.divisor = 0
    · simp only [QuotientTrajectory.weight, QuotientTrajectory.activeRun,
        SignedTrajectory.retainedIteration, if_pos finished, Nat.mul_zero,
        Function.iterate_zero_apply]
    · have active := Nat.pos_of_ne_zero finished
      have count : 4 * QuotientTrajectory.weight (fuel + 1) state =
          4 * QuotientTrajectory.weight fuel (IterationState.step state) +
            4 * state.quotient.size := by
        rw [QuotientTrajectory.weight, if_neg finished]
        omega
      rw [count, Function.iterate_add_apply,
        NativeMacrostep.native_frame state modulus valid conserved coprime active iteration]
      simpa only [QuotientTrajectory.activeRun, SignedTrajectory.retainedIteration,
        if_neg finished] using
        inductionHypothesis (IterationState.step state)
          (IterationState.step_admissible state valid active)
          ((IterationState.step_balance state).trans conserved)
          ((IterationState.step_gcd state).trans coprime) (!iteration)

/-- Actual active execution reaches the full terminal frame for every coprime positive residue. -/
lemma folded_frame (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (NativeMicrostep.step modulus.size)^[QuotientSchedule.phaseWeight modulus input]
      (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input).2) modulus
        (folded_initial_admissible modulus input positive bounded)
        (IterationState.initial_balance modulus (foldInput modulus input).2)
        (foldInput modulus input).1) =
      MacroBoundary.frame (TerminalPadding.finalState modulus input) modulus
        (TerminalPadding.final_admissible modulus input positive bounded)
        (TerminalPadding.final_balance modulus input)
        (SignedTrajectory.finalIteration modulus input) := by
  have foldedCoprime : Nat.gcd modulus (foldInput modulus input).2 = 1 := by
    rw [foldInput_gcd modulus input bounded.le]
    exact coprime.symm
  exact iterate_frame (Euclid.gcdFuel modulus.size)
    (IterationState.initial modulus (foldInput modulus input).2) modulus
    (folded_initial_admissible modulus input positive bounded)
    (IterationState.initial_balance modulus (foldInput modulus input).2)
    foldedCoprime (foldInput modulus input).1

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeTrajectory
