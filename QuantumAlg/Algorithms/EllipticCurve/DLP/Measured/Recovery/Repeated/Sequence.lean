/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Persistent
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Selected
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Sequence
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all QuantumAlg.Core.Execution.Circuit.Associativity

/-!
# Actual reset boundary inside persistent checked sampling

The unchanged selected sampling round consists of the original reset followed
by the original sample/readout. The seven persistent recovery cells remain
live during both sections, exposing the real reset boundary for complete-cycle
reasoning without commuting or replacing any instruction.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
  ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- The actual reset is lifted beside every existing checked-recovery cell. -/
def persistentSamplingReset :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  underPersistent
    (BitWord.selectForCircuit
      (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed))
    (BitWord.selectForCircuit_isLocal _
      (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The unchanged sampling/readout follows the same lifted reset. -/
def persistentSamplingReadout :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  underPersistent
    (BitWord.selectForCircuit
      (samplingReadout E fieldTail odd problem points))
    (BitWord.selectForCircuit_isLocal _
      (samplingReadout_isLocal E fieldTail odd problem points))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- Existing persistent sampling has the actual reset then readout boundary. -/
theorem persistentSamplingRound_seq :
    persistentSamplingRound E fieldTail sameWidth fits odd problem points seed =
      (persistentSamplingReset E fieldTail sameWidth fits problem seed).seq
        (persistentSamplingReadout E fieldTail odd problem points) := by
  let reset := BitWord.selectForCircuit
    (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)
  let readout := BitWord.selectForCircuit
    (samplingReadout E fieldTail odd problem points)
  have resetLocal : reset.IsLocal :=
    BitWord.selectForCircuit_isLocal _
      (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  have readoutLocal : readout.IsLocal :=
    BitWord.selectForCircuit_isLocal _
      (samplingReadout_isLocal E fieldTail odd problem points)
  have segmented := underPersistent_seq reset readout resetLocal readoutLocal
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
  simpa only [persistentSamplingRound, persistentSamplingReset,
    persistentSamplingReadout, samplingRound, BitWord.selectForCircuit_seq,
    reset, readout] using segmented

/-- The unchanged checked recovery immediately consumes the measured sample. -/
def persistentCheckedRecovery (nontrivial : 2 ≤ problem.order) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  persistentAttempt (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem))
    (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))

/-- The real sampled attempt includes the selected round and its original
checked recovery, with the seven destinations already resident. -/
def persistentCheckedAttempt (nontrivial : 2 ≤ problem.order) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let round := BitWord.selectForCircuit
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
  sampledAttempt round
    (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed))
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))

/-- The actual checked attempt has the unchanged reset, readout and classical
recovery in their original order. -/
theorem persistentCheckedAttempt_seq (nontrivial : 2 ≤ problem.order) :
    persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed nontrivial =
      ((persistentSamplingReset E fieldTail sameWidth fits problem seed).seq
        (persistentSamplingReadout E fieldTail odd problem points)).seq
        (persistentCheckedRecovery E problem nontrivial) := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let checked := persistentCheckedRecovery E problem nontrivial
  unfold persistentCheckedAttempt sampledAttempt
  exact congrArg (fun code => code.seq checked)
    (persistentSamplingRound_seq E fieldTail sameWidth fits odd problem points seed)

/-- Rebracketing the real checked attempt retains its complete weighted
execution, actual events, depth and both live-space peaks. -/
def persistentCheckedAttempt_operationalEquiv (nontrivial : 2 ≤ problem.order) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let readout := persistentSamplingReadout E fieldTail odd problem points
    let checked := persistentCheckedRecovery E problem nontrivial
    Circuit.OperationalEquiv
      (persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
        nontrivial)
      (reset.seq (readout.seq checked)) := by
  dsimp only
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let readout := persistentSamplingReadout E fieldTail odd problem points
  let checked := persistentCheckedRecovery E problem nontrivial
  have codeEq := persistentCheckedAttempt_seq E fieldTail sameWidth fits odd problem
    points seed nontrivial
  rw [codeEq]
  exact Circuit.seqAssocOperationalEquiv reset readout checked

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
