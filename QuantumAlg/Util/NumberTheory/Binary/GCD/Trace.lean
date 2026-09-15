/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.Binary.GCD.FixedRound

/-!
# Fixed-round binary-GCD traces

This quantum-free module owns the mathematical definitions used by the
fixed-round binary-GCD realization.  Physical registers and gate schedules
remain in `QuantumAlg.Primitives`.
-/

section

namespace QuantumAlg
namespace NumberTheory.BinaryGCD

/-! ## Trace object for future circuit witnesses -/

/-- A fixed-round trace object for the future concrete compute circuit.  Its
history length and consumed-round count are consequences of the selected
fixed-round schedule [RNSL17, ECDLP.tex:393,468,477]. -/
structure Trace (n : Nat) where
  /-- State before the `2n` fixed rounds. -/
  start : RoundState
  /-- State after the `2n` fixed rounds. -/
  finish : RoundState
  /-- Stored `m_i` history bits. -/
  history : List Bool
  /-- Finish is obtained by running the selected fixed-round schedule. -/
  finish_eq :
    finish = RoundState.runRounds (fixedRoundCount n) start
  /-- History is obtained from the same selected fixed-round schedule. -/
  history_eq :
    history = RoundState.historyBits (fixedRoundCount n) start

namespace Trace

/-- Canonical trace from the source initial state
[RNSL17, ECDLP.tex:409,468]. -/
def ofInput (n p x : Nat) : Trace n where
  start := RoundState.initial p x
  finish := RoundState.fixedRoundState n p x
  history := RoundState.fixedRoundHistory n p x
  finish_eq := rfl
  history_eq := rfl


/-- Canonical fixed-round trace for a staged unit input, using the canonical
`ZMod` representative as the source-level integer input. -/
def ofUnitInput (n p : Nat) (u : (ZMod p)ˣ) : Trace n :=
  ofInput n p (u : ZMod p).val

theorem ofUnitInput_eq_ofInput_val (n p : Nat) (u : (ZMod p)ˣ) :
    ofUnitInput n p u = ofInput n p (u : ZMod p).val :=
  rfl

theorem history_length {n : Nat} (trace : Trace n) :
    trace.history.length = 2 * n := by
  rw [trace.history_eq]
  simp

/-- Source prefix state after a fixed number of rounds in this trace. -/
def prefixState {n : Nat} (trace : Trace n) (rounds : Nat) : RoundState :=
  RoundState.runRounds rounds trace.start

@[simp] theorem prefixState_zero {n : Nat} (trace : Trace n) :
    trace.prefixState 0 = trace.start :=
  rfl

/-- Extending a trace prefix by one source round applies `RoundState.round` to
the current prefix state. -/
theorem prefixState_succ {n : Nat} (trace : Trace n) (rounds : Nat) :
    trace.prefixState (rounds + 1) =
      RoundState.round (trace.prefixState rounds) := by
  simp [prefixState, RoundState.runRounds_succ_eq_round_runRounds]

/-- The full fixed-round prefix is the trace finish state. -/
theorem prefixState_full {n : Nat} (trace : Trace n) :
    trace.prefixState (fixedRoundCount n) =
      trace.finish := by
  rw [prefixState, trace.finish_eq]

theorem finish_totalRounds {n : Nat} (trace : Trace n) :
    RoundState.totalRounds trace.finish =
      RoundState.totalRounds trace.start + 2 * n := by
  rw [trace.finish_eq]
  rw [RoundState.runRounds_totalRounds]
  simp

theorem ofInput_finish_bezoutInvariant (n p x : Nat) :
    RoundState.BezoutInvariant p (ofInput n p x).finish :=
  RoundState.fixedRoundState_bezoutInvariant n p x

theorem ofInput_finish_bezoutInvariant_zmod_eq_zero (n p x : Nat) :
    ((ofInput n p x).finish.rCoeff : ZMod p) *
          ((ofInput n p x).finish.v : ZMod p) +
        ((ofInput n p x).finish.sCoeff : ZMod p) *
          ((ofInput n p x).finish.u : ZMod p) = 0 :=
  RoundState.bezoutInvariant_zmod_eq_zero p (ofInput n p x).finish
    (ofInput_finish_bezoutInvariant n p x)

theorem ofInput_finish_scaledInputCongruence (n p x : Nat) :
    RoundState.scaledInputCongruence p x (ofInput n p x).finish :=
  RoundState.fixedRoundState_scaledInputCongruence n p x

/-- Read the `m_i` history bit of a trace by the fixed-round schedule index. -/
def historyAt {n : Nat} (trace : Trace n)
    (roundIndex : Fin (fixedRoundCount n)) : Bool :=
  RoundState.historyBitsAt (fixedRoundCount n)
    trace.start roundIndex

/-- Trace-indexed history readout agrees with the source prefix state after the
same number of rounds. -/
theorem historyAt_eq_historyBit_prefix {n : Nat} (trace : Trace n)
    (roundIndex : Fin (fixedRoundCount n)) :
    trace.historyAt roundIndex =
      RoundState.historyBit
        (RoundState.runRounds roundIndex.val trace.start) := by
  simpa [historyAt] using
    RoundState.historyBitsAt_eq_historyBit_runRounds
      (fixedRoundCount n) trace.start roundIndex

/-- Trace-indexed history readout agrees with the named prefix state. -/
theorem historyAt_eq_historyBit_prefixState {n : Nat} (trace : Trace n)
    (roundIndex : Fin (fixedRoundCount n)) :
    trace.historyAt roundIndex =
      RoundState.historyBit (trace.prefixState roundIndex.val) := by
  simpa [prefixState] using
    historyAt_eq_historyBit_prefix trace roundIndex

/-- Trace-indexed history readout agrees with the materialized trace history
list. -/
theorem historyAt_eq_get {n : Nat} (trace : Trace n)
    (roundIndex : Fin (fixedRoundCount n)) :
    trace.historyAt roundIndex =
      trace.history.get
        ⟨roundIndex.val, by
          rw [history_length trace]
          exact roundIndex.isLt⟩ := by
  rcases trace with ⟨start, finish, history, hfinish, hhistory⟩
  dsimp [historyAt] at *
  subst history
  exact
    RoundState.historyBitsAt_eq_get
      (fixedRoundCount n) start roundIndex

/-- The materialized trace history list is exactly the finite table of indexed
trace history readouts. -/
theorem history_eq_ofFn_historyAt {n : Nat} (trace : Trace n) :
    trace.history =
      List.ofFn
        (fun roundIndex : Fin (fixedRoundCount n) =>
          trace.historyAt roundIndex) := by
  rw [trace.history_eq]
  simpa [historyAt] using
    RoundState.historyBits_eq_ofFn_historyBitsAt
      (fixedRoundCount n) trace.start

/-- The canonical input trace uses the fixed-round source history readout. -/
theorem ofInput_historyAt (n p x : Nat)
    (roundIndex : Fin (fixedRoundCount n)) :
    (ofInput n p x).historyAt roundIndex =
      RoundState.fixedRoundHistoryAt n p x roundIndex := by
  rfl

/-- The canonical input trace's indexed history readout agrees with its
materialized `m_i` history list. -/
theorem ofInput_historyAt_eq_get (n p x : Nat)
    (roundIndex : Fin (fixedRoundCount n)) :
    (ofInput n p x).historyAt roundIndex =
      (ofInput n p x).history.get
        ⟨roundIndex.val, by
          rw [history_length (ofInput n p x)]
          exact roundIndex.isLt⟩ :=
  historyAt_eq_get (ofInput n p x) roundIndex

/-- Number of correction doublings selected by the trace's fixed-round endpoint.
-/
def correctionRounds {n : Nat} (trace : Trace n) : Nat :=
  RoundState.correctionRounds trace.finish

theorem correctionRounds_eq_finish_paddingSteps {n : Nat} (trace : Trace n) :
    trace.correctionRounds = trace.finish.paddingSteps :=
  rfl

/-- Trace-side residue copied before correction. -/
def pseudoInverseResidue {n : Nat} (p : Nat) (trace : Trace n) : ZMod p :=
  RoundState.pseudoInverseResidue p trace.finish

/-- Trace-side Montgomery correction factor. -/
def correctionFactor {n : Nat} (p : Nat) (trace : Trace n) : ZMod p :=
  RoundState.correctionFactor p trace.correctionRounds

/-- Trace-side corrected residue after applying the selected doublings. -/
def correctedInverseResidue {n : Nat} (p : Nat) (trace : Trace n) : ZMod p :=
  RoundState.correctedInverseResidue p trace.finish

theorem correctedInverseResidue_eq_factor_mul_pseudo {n p : Nat}
    (trace : Trace n) :
    trace.correctedInverseResidue p =
      trace.correctionFactor p * trace.pseudoInverseResidue p :=
  rfl

/-- Trace-side sign-adjusted corrected residue.  This is read from the same
fixed endpoint as `correctedInverseResidue`; it only makes the source-level
coefficient sign explicit. -/
def signedCorrectedInverseResidue {n : Nat}
    (p : Nat) (trace : Trace n) : ZMod p :=
  RoundState.signedCorrectedInverseResidue p trace.finish

theorem signedCorrectedInverseResidue_eq_neg_corrected {n p : Nat}
    (trace : Trace n) :
    trace.signedCorrectedInverseResidue p =
      -trace.correctedInverseResidue p :=
  rfl

theorem ofInput_correctionRounds_eq_two_mul_sub_kaliskiSteps
    (n p x : Nat) :
    (ofInput n p x).correctionRounds =
      2 * n - (ofInput n p x).finish.kaliskiSteps := by
  simpa [correctionRounds, ofInput] using
    RoundState.fixedRoundState_correctionRounds_eq_two_mul_sub_kaliskiSteps
      n p x

theorem ofInput_pseudoInverseResidue_eq_fixedRoundState_rCoeff
    (n p x : Nat) :
    (ofInput n p x).pseudoInverseResidue p =
      (RoundState.fixedRoundState n p x).rCoeff := by
  rfl

theorem ofInput_correctedInverseResidue_eq_fixedRoundState
    (n p x : Nat) :
    (ofInput n p x).correctedInverseResidue p =
      RoundState.correctedInverseResidue p (RoundState.fixedRoundState n p x) :=
  rfl

/-- Final fixed-trace correction factor: once the fixed trace has terminated
at `u = 1`, the corrected trace-side residue multiplied by the input is the
fixed scaling factor [RNSL17, ECDLP.tex:399-412,442-479; HJN+20,
modular-arithmetic.tex:141-144]. -/
theorem ofInput_correctedInverseResidue_mul_input_eq_neg_pow_of_final_state
    (n p x : Nat)
    (hfinish : (ofInput n p x).finish.u = 1) :
    (ofInput n p x).correctedInverseResidue p * (x : ZMod p) =
      -((2 : ZMod p) ^ (2 * n)) := by
  have htotal :
      (ofInput n p x).finish.kaliskiSteps +
          (ofInput n p x).finish.paddingSteps = 2 * n := by
    change RoundState.totalRounds (ofInput n p x).finish = 2 * n
    simpa [ofInput] using RoundState.fixedRoundState_totalRounds n p x
  have hrounds :
      RoundState.correctionRounds (ofInput n p x).finish +
          (ofInput n p x).finish.kaliskiSteps = 2 * n := by
    change
      (ofInput n p x).finish.paddingSteps +
          (ofInput n p x).finish.kaliskiSteps = 2 * n
    rw [Nat.add_comm]
    exact htotal
  calc
    (ofInput n p x).correctedInverseResidue p * (x : ZMod p)
        = RoundState.correctedInverseResidue p (ofInput n p x).finish *
            (x : ZMod p) := by
      rfl
    _ = -((2 : ZMod p) ^ (2 * n)) :=
      RoundState.correctedInverseResidue_mul_input_eq_neg_pow_of_scaled
        p x n (ofInput n p x).finish
        (ofInput_finish_scaledInputCongruence n p x) hrounds hfinish

/-- Unit-input form of the final fixed-trace correction factor.  The canonical
`ZMod` representative discharges the trace/input representative equality; the
output remains the explicit fixed scaling factor. -/
theorem ofUnitInput_correctedInverseResidue_mul_input_eq_neg_pow_of_final_state
    (n p : Nat) [NeZero p] (u : (ZMod p)ˣ)
    (hfinish : (ofUnitInput n p u).finish.u = 1) :
    (ofUnitInput n p u).correctedInverseResidue p * (u : ZMod p) =
      -((2 : ZMod p) ^ (2 * n)) := by
  change
    (ofInput n p (u : ZMod p).val).correctedInverseResidue p *
        (u : ZMod p) =
      -((2 : ZMod p) ^ (2 * n))
  have hx : ((u : ZMod p).val : ZMod p) = (u : ZMod p) := by
    simp
  calc
    (ofInput n p (u : ZMod p).val).correctedInverseResidue p *
          (u : ZMod p)
        = (ofInput n p (u : ZMod p).val).correctedInverseResidue p *
            ((u : ZMod p).val : ZMod p) := by
      rw [hx]
    _ = -((2 : ZMod p) ^ (2 * n)) :=
      ofInput_correctedInverseResidue_mul_input_eq_neg_pow_of_final_state
        n p (u : ZMod p).val (by simpa [ofUnitInput] using hfinish)

/-- Sign-adjusted final fixed-trace correction factor. -/
theorem ofInput_signedCorrectedInverseResidue_mul_input_eq_pow_of_final_state
    (n p x : Nat)
    (hfinish : (ofInput n p x).finish.u = 1) :
    (ofInput n p x).signedCorrectedInverseResidue p * (x : ZMod p) =
      (2 : ZMod p) ^ (2 * n) := by
  have htotal :
      (ofInput n p x).finish.kaliskiSteps +
          (ofInput n p x).finish.paddingSteps = 2 * n := by
    change RoundState.totalRounds (ofInput n p x).finish = 2 * n
    simpa [ofInput] using RoundState.fixedRoundState_totalRounds n p x
  have hrounds :
      RoundState.correctionRounds (ofInput n p x).finish +
          (ofInput n p x).finish.kaliskiSteps = 2 * n := by
    change
      (ofInput n p x).finish.paddingSteps +
          (ofInput n p x).finish.kaliskiSteps = 2 * n
    rw [Nat.add_comm]
    exact htotal
  exact
    RoundState.signedCorrectedInverseResidue_mul_input_eq_pow_of_scaled
      p x n (ofInput n p x).finish
      (ofInput_finish_scaledInputCongruence n p x) hrounds hfinish

/-- Unit-input form of the positive final fixed-trace Montgomery scale. -/
theorem ofUnitInput_signedCorrectedInverseResidue_mul_input_eq_pow_of_final_state
    (n p : Nat) [NeZero p] (u : (ZMod p)ˣ)
    (hfinish : (ofUnitInput n p u).finish.u = 1) :
    (ofUnitInput n p u).signedCorrectedInverseResidue p * (u : ZMod p) =
      (2 : ZMod p) ^ (2 * n) := by
  change
    (ofInput n p (u : ZMod p).val).signedCorrectedInverseResidue p *
        (u : ZMod p) = (2 : ZMod p) ^ (2 * n)
  have hx : ((u : ZMod p).val : ZMod p) = (u : ZMod p) := by
    simp
  calc
    (ofInput n p (u : ZMod p).val).signedCorrectedInverseResidue p *
          (u : ZMod p) =
        (ofInput n p (u : ZMod p).val).signedCorrectedInverseResidue p *
          ((u : ZMod p).val : ZMod p) := by
      rw [hx]
    _ = (2 : ZMod p) ^ (2 * n) :=
      ofInput_signedCorrectedInverseResidue_mul_input_eq_pow_of_final_state
        n p (u : ZMod p).val (by simpa [ofUnitInput] using hfinish)

end Trace

end NumberTheory.BinaryGCD
end QuantumAlg

end
