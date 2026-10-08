/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Selection
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Event

/-!
# The original candidate floor beside the actual persistent recovery cells

The actual complete sampling round runs beside all seven existing recovery
cells. Their old values remain arbitrary and correlated with every original
input block and reference. Its original selected event is contained in the
complete stored candidate event used by the real checked recovery.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The selected complete sampling round, lifted beside the existing recovery cells. -/
def persistentSamplingRound (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  underPersistent
    (BitWord.selectForCircuit (samplingRound E fieldTail sameWidth fits odd problem points seed))
    (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- Actual sampling beside the existing cells has the original complete-candidate mass floor. -/
theorem persistentSamplingRound_candidate_weight_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H)) :
    let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((persistentSamplingRound E fieldTail sameWidth fits odd problem points seed).execute
        Reference state).effectWeight
        (fun record =>
          if SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
              problem.generator.toMathlib problem.target.toMathlib
              (record.1.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
                (rawRecoveryInput problem measured))) then
            Effect.one ((persistentCtx (PublicInput.terminal E (orderWidth problem))
              (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference)
          else Effect.zero ((persistentCtx (PublicInput.terminal E (orderWidth problem))
              (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference)) := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let code := samplingRound E fieldTail sameWidth fits odd problem points seed
  have supported := samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed
  let selectedCode := BitWord.selectForCircuit code
  have selectedSupported : selectedCode.IsLocal :=
    BitWord.selectForCircuit_isLocal code supported
  let localReference := persistentLocalReference (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem) Reference
  let split := underPersistentSplitState (Canonical.Layout.fieldWidth E)
    (orderWidth problem) state
  have original := selectedSamplingRound_weight_bound E fieldTail sameWidth fits odd problem
    points seed addends input
    (underPersistentSplitState (Canonical.Layout.fieldWidth E) (orderWidth problem) state)
  rw [underPersistentSplitState_mass] at original
  have sameWeight :
      (selectedCode.execute localReference split).effectWeight
          (samplingSelectedEffects E problem input localReference) =
        (code.execute localReference split).effectWeight
          (samplingSelectedEffects E problem input localReference) := by
    rw [BitWord.selectForCircuit_execute code localReference split]
    rw [State.effectWeight_mapHistory]
    rfl
  have actual := underPersistent_eventWeight selectedCode selectedSupported
    (Canonical.Layout.fieldWidth E)
    (orderWidth problem) state measured
    (fun value => selectedExponentEvent problem input (QubitReadouts.mask value))
  change _ = (selectedCode.execute localReference split).effectWeight
    (samplingSelectedEffects E problem input localReference) at actual
  rw [sameWeight] at actual
  have inclusion := selectedPersistentSample_weight_le problem nontrivial input
    (Canonical.Layout.fieldWidth E) measured
    ((underPersistent selectedCode selectedSupported (Canonical.Layout.fieldWidth E)
      (orderWidth problem)).execute Reference state)
  exact (original.trans_eq actual.symm).trans inclusion

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
