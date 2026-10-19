/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Invariant
import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Padding

/-!
# Retained parity and original-input inverse along the active macro trajectory

The actual word exchange flips Iter once per active macro transition.
Combining this retained bit with the original fold establishes the
source's final conditional correction on the coprime positive-residue
domain, extending the source's prime domain by a project proof
[LYL+26, sec_EEA/sub_regshare.tex:309-313;
LYL+26, sec_EEA/sub_4phase.tex:112-125].

The recurrence below records only that bit along the already defined
mathematical active trajectory. Its terminal branch contributes no new
active exchanges; it does not make physical terminal padding idle.
No caller termination, coefficient-fit, or signed-relation premise is
needed by the final product theorem. Native padding, output gates, and
the inverse cleanup of the retained forward state remain separate work.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.SignedTrajectory

open QuantumAlg.ClassicalAlgorithms.NumberTheory

/-- The retained Iter value after precisely the active macro exchanges in a finite prefix. -/
def retainedIteration : Nat → IterationState → Bool → Bool
  | 0, _state, iteration => iteration
  | fuel + 1, state, iteration =>
      if state.divisor = 0 then iteration
      else retainedIteration fuel (IterationState.step state) (!iteration)

/-- A completed mathematical active prefix contributes no further iteration-bit complements. -/
lemma retainedIteration_finished (fuel : Nat) (state : IterationState) (iteration : Bool)
    (finished : state.divisor = 0) :
    retainedIteration fuel state iteration = iteration := by
  cases fuel <;> simp only [retainedIteration, if_pos finished]

/-- Every actual active macro exchange preserves both congruences with its retained parity. -/
lemma activeRun_holds (fuel modulus input : Nat) (state : IterationState) (iteration : Bool)
    (invariant : SignedInvariant.Holds modulus input state iteration) :
    SignedInvariant.Holds modulus input (QuotientTrajectory.activeRun fuel state)
      (retainedIteration fuel state iteration) := by
  induction fuel generalizing state iteration with
  | zero => exact invariant
  | succ fuel inductionHypothesis =>
    by_cases finished : state.divisor = 0
    · simpa only [QuotientTrajectory.activeRun, retainedIteration, if_pos finished] using invariant
    · simp only [QuotientTrajectory.activeRun, retainedIteration, if_neg finished]
      exact inductionHypothesis (IterationState.step state) (!iteration)
        (SignedInvariant.step modulus input state iteration invariant)

/-- Actual fold history followed by all active macro Iter flips under independently proved fuel. -/
def finalIteration (modulus input : Nat) : Bool :=
  retainedIteration (Euclid.gcdFuel modulus.size)
    (IterationState.initial modulus (foldInput modulus input).2) (foldInput modulus input).1

/-- The original residue establishes the full signed terminal relation without extra premises. -/
lemma final_holds (modulus input : Nat) (bounded : input < modulus) :
    SignedInvariant.Holds modulus input (TerminalPadding.finalState modulus input)
      (finalIteration modulus input) :=
  activeRun_holds (Euclid.gcdFuel modulus.size) modulus input
    (IterationState.initial modulus (foldInput modulus input).2) (foldInput modulus input).1
    (SignedInvariant.folded_initial modulus input bounded)

/-- The retained parity selects a genuine inverse for every coprime positive residue. -/
lemma final_product (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (input : ZMod modulus) *
      (SignedInvariant.output modulus (TerminalPadding.finalState modulus input)
        (finalIteration modulus input) : ZMod modulus) = 1 :=
  SignedInvariant.terminal_product modulus input (TerminalPadding.finalState modulus input)
    (finalIteration modulus input) (TerminalPadding.final_admissible modulus input positive bounded)
    (TerminalPadding.final_balance modulus input) (final_holds modulus input bounded)
    (TerminalPadding.final_divisor modulus input positive bounded)
    (TerminalPadding.final_remainder modulus input coprime positive bounded)

end QuantumAlg.NumberTheory.SharedEEA.SignedTrajectory
