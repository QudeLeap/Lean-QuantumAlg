/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Alignment.Trajectory
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Entry
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Trajectory

/-!
# One complete Euclidean macrostep of the actual shared-register program

The four phases below all iterate the same already realized native
microstep, in the actual source order. Alignment writes its real stop
flag; division and coefficient consumption transfer the quotient through
the original shared word; deshifting executes the full comparison and
the actual swap, length refresh, and Iter flip
[LYL+26, sec_EEA/sub_regshare.tex:275-313;
LYL+26, sec_EEA/sub_opt.tex:37-84].

The result is the entire canonical physical frame of the exact next
Euclidean state. No intermediate frame is prepared by a caller. The
four-times-quotient-size expression counts actual native microsteps;
it is neither their elementary-event count nor a separately implemented
runtime loop. A fixed overall schedule and reversible terminal padding
still require their own connection to these actual state equations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeMacrostep

noncomputable section

open NumberTheory.SharedEEA

/-- All four actual phases compose on the full frame, without supplied intermediate states. -/
lemma four_phases (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[state.quotient.size]
      ((NativeMicrostep.step modulus.size)^[state.quotient.size]
        ((NativeMicrostep.step modulus.size)^[state.quotient.size]
          ((NativeMicrostep.step modulus.size)^[state.quotient.size]
            (MacroBoundary.frame state modulus valid conserved iteration)))) =
      MacroBoundary.frame (IterationState.step state) modulus
        (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) := by
  have middle := CoefficientEntry.middle_phases state modulus valid conserved active iteration
  let entry : Registers modulus.size := DivisionTrajectory.phaseFrame state modulus 0
    valid conserved active (Nat.zero_le _) iteration
  have places : (Alignment.align state.remainder state.divisor).places = state.quotient.size :=
    Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  have exactMiddle := (congrArg
    (fun count : Nat => (NativeMicrostep.step modulus.size)^[state.quotient.size]
      ((NativeMicrostep.step modulus.size)^[count] entry)) places.symm).trans middle
  rw [AlignmentTrajectory.finish_frame state modulus valid conserved active iteration,
    exactMiddle,
    DeshiftTrajectory.finish_frame state modulus valid conserved coprime active iteration]

/-- The proved four-phase count implements the complete Euclidean macro transition. -/
lemma native_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[4 * state.quotient.size]
      (MacroBoundary.frame state modulus valid conserved iteration) =
      MacroBoundary.frame (IterationState.step state) modulus
        (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) := by
  have count : 4 * state.quotient.size =
      state.quotient.size + state.quotient.size + state.quotient.size + state.quotient.size := by
    omega
  rw [count]
  simpa only [Function.iterate_add_apply] using
    four_phases state modulus valid conserved coprime active iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeMacrostep
