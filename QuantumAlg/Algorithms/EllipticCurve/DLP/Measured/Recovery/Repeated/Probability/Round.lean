/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Mixed
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Support
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout.Mass

/-!
# Original selected-frequency floor for one complete actual reset and sampling round

The same round resets every original quantum wire, runs the original measured
arithmetic and Fourier readout, and observes its actual overwritten result
cells. Every conditional reference block and original classical value remains
arbitrary. The original selected-frequency floor, multiplied by the actual
input mass, retains exactly the original exceptional-offset error.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The mathematical selected event reads only the actual terminal measurement result cells. -/
def samplingSelectedEffects (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem)
    (Reference : Register) {History : Type} :
    Circuit.EffectFamily (PublicInput.terminal E (orderWidth problem)) Reference History :=
  fun record => if selectedExponentEvent problem input (QubitReadouts.mask
    (record.1.read (inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))))) = true then
      Effect.one ((PublicInput.terminal E (orderWidth problem)).register.prod Reference)
    else Effect.zero ((PublicInput.terminal E (orderWidth problem)).register.prod Reference)

/-- Every complete actual round retains the original floor for arbitrary mixed input and history. -/
theorem selectedSamplingRound_weight_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register} {H : Type} [Fintype H]
    (state : State (PublicInput.terminal E (orderWidth problem)) Reference H) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((samplingRound E fieldTail sameWidth fits odd problem points seed).execute
        Reference state).effectWeight (samplingSelectedEffects E problem input Reference) := by
  have mixed := selectedSamplingPrefix_mixed_weight_bound E fieldTail sameWidth fits odd problem
    points seed addends input
    (samplingReadoutSplitState E (orderWidth problem)
      ((samplingReset E fieldTail (orderWidth problem) sameWidth fits seed).execute
        Reference state))
    (samplingResetSplit_supported E fieldTail (orderWidth problem) sameWidth fits seed state)
  rw [samplingReadoutSplitState_mass, Circuit.execute_mass] at mixed
  unfold samplingRound samplingSelectedEffects
  rw [Circuit.execute_seq]
  erw [State.effectWeight_mapHistory]
  rw [samplingReadout_eventWeight_split]
  exact mixed

/-- One original offset supplies the same actual round bound for every witness and posterior. -/
theorem exists_fixedOffset_selectedSamplingRound_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (orderAtLeastTwo : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers problem.generator ∧ seed.toGroupPoint ≠ 1 ∧
        ∀ (input : SecretInput problem) (Reference : Register) (H : Type) [Fintype H]
          (state : State (PublicInput.terminal E (orderWidth problem)) Reference H),
          state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
              (4 * (fourierModulus problem : ℝ) ^ 2) -
                4 * Real.sqrt
                  ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ))) ≤
            ((samplingRound E fieldTail sameWidth fits odd problem points seed).execute
              Reference state).effectWeight
                (samplingSelectedEffects E problem input Reference) := by
  obtain ⟨seed, member, nonidentity, exceptional⟩ :=
    exists_fixedOffset_exceptionalMass_bound problem orderAtLeastTwo points
  refine ⟨seed, member, nonidentity, ?_⟩
  intro input Reference H _ state
  have error : 4 * Real.sqrt (preparedExceptionalMass problem points seed) ≤
      4 * Real.sqrt
        ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt exceptional) (by norm_num)
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left error _) state.mass_nonneg).trans
    (selectedSamplingRound_weight_bound E fieldTail sameWidth fits odd problem points seed
      addends input state)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
